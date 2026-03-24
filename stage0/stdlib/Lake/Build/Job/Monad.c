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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_pushLogEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_instMonadST___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
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
static const lean_closure_object l_Lake_instMonadStateOfJobStateJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lake_instAlternativeJobM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instAlternativeJobM___closed__0;
static const lean_closure_object l_Lake_instAlternativeJobM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instAlternativeJobM___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instAlternativeJobM___closed__1 = (const lean_object*)&l_Lake_instAlternativeJobM___closed__1_value;
static const lean_closure_object l_Lake_instAlternativeJobM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instAlternativeJobM___lam__1___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instAlternativeJobM___closed__2 = (const lean_object*)&l_Lake_instAlternativeJobM___closed__2_value;
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
v___x_9_ = lean_apply_7(v_f_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___redArg___boxed(lean_object* v_f_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lake_JobM_ofFn___redArg(v_f_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn(lean_object* v_00_u03b1_19_, lean_object* v_f_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_apply_7(v_f_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, lean_box(0));
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___boxed(lean_object* v_00_u03b1_29_, lean_object* v_f_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_JobM_ofFn(v_00_u03b1_29_, v_f_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
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
lean_object* v___f_78_; lean_object* v___x_79_; 
v___f_78_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__0));
v___x_79_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v___f_78_);
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
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec(v___y_275_);
lean_dec(v___y_274_);
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
return v_res_308_;
}
}
static lean_object* _init_l_Lake_instAlternativeJobM___closed__0(void){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_instMonadST(lean_box(0));
return v___x_309_;
}
}
static lean_object* _init_l_Lake_instAlternativeJobM(void){
_start:
{
lean_object* v___x_312_; lean_object* v_toApplicative_313_; lean_object* v_toBind_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_348_; 
v___x_312_ = lean_obj_once(&l_Lake_instAlternativeJobM___closed__0, &l_Lake_instAlternativeJobM___closed__0_once, _init_l_Lake_instAlternativeJobM___closed__0);
v_toApplicative_313_ = lean_ctor_get(v___x_312_, 0);
v_toBind_314_ = lean_ctor_get(v___x_312_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_348_ == 0)
{
v___x_316_ = v___x_312_;
v_isShared_317_ = v_isSharedCheck_348_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_toBind_314_);
lean_inc(v_toApplicative_313_);
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_348_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_toFunctor_318_; lean_object* v_toPure_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_344_; 
v_toFunctor_318_ = lean_ctor_get(v_toApplicative_313_, 0);
v_toPure_319_ = lean_ctor_get(v_toApplicative_313_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_toApplicative_313_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_345_ = lean_ctor_get(v_toApplicative_313_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_toApplicative_313_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_toApplicative_313_, 2);
lean_dec(v_unused_347_);
v___x_321_ = v_toApplicative_313_;
v_isShared_322_ = v_isSharedCheck_344_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_toPure_319_);
lean_inc(v_toFunctor_318_);
lean_dec(v_toApplicative_313_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_344_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___f_328_; lean_object* v___x_330_; 
lean_inc(v_toBind_314_);
lean_inc(v_toPure_319_);
v___f_323_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_323_, 0, v_toPure_319_);
lean_closure_set(v___f_323_, 1, v_toBind_314_);
lean_inc(v_toBind_314_);
lean_inc(v_toPure_319_);
v___f_324_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_324_, 0, v_toPure_319_);
lean_closure_set(v___f_324_, 1, v_toBind_314_);
lean_inc_ref(v___f_323_);
lean_inc(v_toPure_319_);
v___f_325_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_325_, 0, v_toPure_319_);
lean_closure_set(v___f_325_, 1, v___f_323_);
lean_inc(v_toPure_319_);
lean_inc_ref(v_toFunctor_318_);
v___f_326_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_326_, 0, v_toFunctor_318_);
lean_closure_set(v___f_326_, 1, v_toPure_319_);
lean_closure_set(v___f_326_, 2, v_toBind_314_);
v___x_327_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_318_);
v___f_328_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_328_, 0, v_toPure_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 4, v___f_324_);
lean_ctor_set(v___x_321_, 3, v___f_325_);
lean_ctor_set(v___x_321_, 2, v___f_326_);
lean_ctor_set(v___x_321_, 1, v___f_328_);
lean_ctor_set(v___x_321_, 0, v___x_327_);
v___x_330_ = v___x_321_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___f_328_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v___f_326_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v___f_325_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v___f_324_);
v___x_330_ = v_reuseFailAlloc_343_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___f_323_);
lean_ctor_set(v___x_316_, 0, v___x_330_);
v___x_332_ = v___x_316_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___f_323_);
v___x_332_ = v_reuseFailAlloc_342_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_toApplicative_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___x_341_; 
v___x_333_ = l_ReaderT_instMonad___redArg(v___x_332_);
v___x_334_ = l_ReaderT_instMonad___redArg(v___x_333_);
v___x_335_ = l_ReaderT_instMonad___redArg(v___x_334_);
v___x_336_ = l_ReaderT_instMonad___redArg(v___x_335_);
v___x_337_ = l_Lake_EquipT_instMonad___redArg(v___x_336_);
v_toApplicative_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_toApplicative_338_);
lean_dec_ref(v___x_337_);
v___f_339_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__1));
v___f_340_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__2));
v___x_341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_341_, 0, v_toApplicative_338_);
lean_ctor_set(v___x_341_, 1, v___f_339_);
lean_ctor_set(v___x_341_, 2, v___f_340_);
return v___x_341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object* v_00_u03b1_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_log_358_; uint8_t v_action_359_; uint8_t v_wantsRebuild_360_; lean_object* v_trace_361_; lean_object* v_buildTime_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_391_; 
v_log_358_ = lean_ctor_get(v___y_356_, 0);
v_action_359_ = lean_ctor_get_uint8(v___y_356_, sizeof(void*)*3);
v_wantsRebuild_360_ = lean_ctor_get_uint8(v___y_356_, sizeof(void*)*3 + 1);
v_trace_361_ = lean_ctor_get(v___y_356_, 1);
v_buildTime_362_ = lean_ctor_get(v___y_356_, 2);
v_isSharedCheck_391_ = !lean_is_exclusive(v___y_356_);
if (v_isSharedCheck_391_ == 0)
{
v___x_364_ = v___y_356_;
v_isShared_365_ = v_isSharedCheck_391_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_buildTime_362_);
lean_inc(v_trace_361_);
lean_inc(v_log_358_);
lean_dec(v___y_356_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_391_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_apply_2(v___y_350_, v_log_358_, lean_box(0));
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_378_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_a_368_ = lean_ctor_get(v___x_366_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_378_ == 0)
{
v___x_370_ = v___x_366_;
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_a_368_);
v___x_373_ = v___x_364_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_368_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_trace_361_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_buildTime_362_);
lean_ctor_set_uint8(v_reuseFailAlloc_377_, sizeof(void*)*3, v_action_359_);
lean_ctor_set_uint8(v_reuseFailAlloc_377_, sizeof(void*)*3 + 1, v_wantsRebuild_360_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v___x_373_);
v___x_375_ = v___x_370_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_390_; 
v_a_379_ = lean_ctor_get(v___x_366_, 0);
v_a_380_ = lean_ctor_get(v___x_366_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_390_ == 0)
{
v___x_382_ = v___x_366_;
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_inc(v_a_379_);
lean_dec(v___x_366_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_a_380_);
v___x_385_ = v___x_364_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_trace_361_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_buildTime_362_);
lean_ctor_set_uint8(v_reuseFailAlloc_389_, sizeof(void*)*3, v_action_359_);
lean_ctor_set_uint8(v_reuseFailAlloc_389_, sizeof(void*)*3 + 1, v_wantsRebuild_360_);
v___x_385_ = v_reuseFailAlloc_389_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_387_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object* v_00_u03b1_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lake_instMonadLiftLogIOJobM___lam__0(v_00_u03b1_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t v_action_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_log_407_; uint8_t v_action_408_; uint8_t v_wantsRebuild_409_; lean_object* v_trace_410_; lean_object* v_buildTime_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_421_; 
v_log_407_ = lean_ctor_get(v_a_405_, 0);
v_action_408_ = lean_ctor_get_uint8(v_a_405_, sizeof(void*)*3);
v_wantsRebuild_409_ = lean_ctor_get_uint8(v_a_405_, sizeof(void*)*3 + 1);
v_trace_410_ = lean_ctor_get(v_a_405_, 1);
v_buildTime_411_ = lean_ctor_get(v_a_405_, 2);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_421_ == 0)
{
v___x_413_ = v_a_405_;
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_buildTime_411_);
lean_inc(v_trace_410_);
lean_inc(v_log_407_);
lean_dec(v_a_405_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_418_; 
v___x_415_ = lean_box(0);
v___x_416_ = l_Lake_JobAction_merge(v_action_408_, v_action_404_);
if (v_isShared_414_ == 0)
{
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_log_407_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_trace_410_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_buildTime_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*3 + 1, v_wantsRebuild_409_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3, v___x_416_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_415_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object* v_action_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_action_boxed_425_; lean_object* v_res_426_; 
v_action_boxed_425_ = lean_unbox(v_action_422_);
v_res_426_ = l_Lake_updateAction___redArg(v_action_boxed_425_, v_a_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t v_action_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_log_435_; uint8_t v_action_436_; uint8_t v_wantsRebuild_437_; lean_object* v_trace_438_; lean_object* v_buildTime_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_449_; 
v_log_435_ = lean_ctor_get(v_a_433_, 0);
v_action_436_ = lean_ctor_get_uint8(v_a_433_, sizeof(void*)*3);
v_wantsRebuild_437_ = lean_ctor_get_uint8(v_a_433_, sizeof(void*)*3 + 1);
v_trace_438_ = lean_ctor_get(v_a_433_, 1);
v_buildTime_439_ = lean_ctor_get(v_a_433_, 2);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_433_);
if (v_isSharedCheck_449_ == 0)
{
v___x_441_ = v_a_433_;
v_isShared_442_ = v_isSharedCheck_449_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_buildTime_439_);
lean_inc(v_trace_438_);
lean_inc(v_log_435_);
lean_dec(v_a_433_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_449_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_446_; 
v___x_443_ = lean_box(0);
v___x_444_ = l_Lake_JobAction_merge(v_action_436_, v_action_427_);
if (v_isShared_442_ == 0)
{
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_log_435_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_trace_438_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_buildTime_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*3 + 1, v_wantsRebuild_437_);
v___x_446_ = v_reuseFailAlloc_448_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; 
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*3, v___x_444_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_443_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object* v_action_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
uint8_t v_action_boxed_458_; lean_object* v_res_459_; 
v_action_boxed_458_ = lean_unbox(v_action_450_);
v_res_459_ = l_Lake_updateAction(v_action_boxed_458_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object* v_a_460_){
_start:
{
lean_object* v_trace_462_; lean_object* v___x_463_; 
v_trace_462_ = lean_ctor_get(v_a_460_, 1);
lean_inc_ref(v_trace_462_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_trace_462_);
lean_ctor_set(v___x_463_, 1, v_a_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg___boxed(lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lake_getTrace___redArg(v_a_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_trace_474_; lean_object* v___x_475_; 
v_trace_474_ = lean_ctor_get(v_a_472_, 1);
lean_inc_ref(v_trace_474_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v_trace_474_);
lean_ctor_set(v___x_475_, 1, v_a_472_);
return v___x_475_;
}
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
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object* v_trace_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_log_487_; uint8_t v_action_488_; uint8_t v_wantsRebuild_489_; lean_object* v_buildTime_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_499_; 
v_log_487_ = lean_ctor_get(v_a_485_, 0);
v_action_488_ = lean_ctor_get_uint8(v_a_485_, sizeof(void*)*3);
v_wantsRebuild_489_ = lean_ctor_get_uint8(v_a_485_, sizeof(void*)*3 + 1);
v_buildTime_490_ = lean_ctor_get(v_a_485_, 2);
v_isSharedCheck_499_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v_a_485_, 1);
lean_dec(v_unused_500_);
v___x_492_ = v_a_485_;
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_buildTime_490_);
lean_inc(v_log_487_);
lean_dec(v_a_485_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_box(0);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v_trace_484_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_log_487_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_trace_484_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_buildTime_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_498_, sizeof(void*)*3, v_action_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_498_, sizeof(void*)*3 + 1, v_wantsRebuild_489_);
v___x_496_ = v_reuseFailAlloc_498_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; 
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_494_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg___boxed(lean_object* v_trace_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lake_setTrace___redArg(v_trace_501_, v_a_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object* v_trace_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_log_513_; uint8_t v_action_514_; uint8_t v_wantsRebuild_515_; lean_object* v_buildTime_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v_log_513_ = lean_ctor_get(v_a_511_, 0);
v_action_514_ = lean_ctor_get_uint8(v_a_511_, sizeof(void*)*3);
v_wantsRebuild_515_ = lean_ctor_get_uint8(v_a_511_, sizeof(void*)*3 + 1);
v_buildTime_516_ = lean_ctor_get(v_a_511_, 2);
v_isSharedCheck_525_ = !lean_is_exclusive(v_a_511_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_a_511_, 1);
lean_dec(v_unused_526_);
v___x_518_ = v_a_511_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_buildTime_516_);
lean_inc(v_log_513_);
lean_dec(v_a_511_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_box(0);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v_trace_505_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_log_513_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_trace_505_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_buildTime_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_524_, sizeof(void*)*3, v_action_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_524_, sizeof(void*)*3 + 1, v_wantsRebuild_515_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_520_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object* v_trace_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lake_setTrace(v_trace_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object* v_caption_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_log_539_; uint8_t v_action_540_; uint8_t v_wantsRebuild_541_; lean_object* v_buildTime_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_552_; 
v_log_539_ = lean_ctor_get(v_a_537_, 0);
v_action_540_ = lean_ctor_get_uint8(v_a_537_, sizeof(void*)*3);
v_wantsRebuild_541_ = lean_ctor_get_uint8(v_a_537_, sizeof(void*)*3 + 1);
v_buildTime_542_ = lean_ctor_get(v_a_537_, 2);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_537_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_a_537_, 1);
lean_dec(v_unused_553_);
v___x_544_ = v_a_537_;
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_buildTime_542_);
lean_inc(v_log_539_);
lean_dec(v_a_537_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = l_Lake_BuildTrace_nil(v_caption_536_);
v___x_547_ = lean_box(0);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_546_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_log_539_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_buildTime_542_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*3, v_action_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*3 + 1, v_wantsRebuild_541_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_547_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg___boxed(lean_object* v_caption_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lake_newTrace___redArg(v_caption_554_, v_a_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object* v_caption_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_log_566_; uint8_t v_action_567_; uint8_t v_wantsRebuild_568_; lean_object* v_buildTime_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_579_; 
v_log_566_ = lean_ctor_get(v_a_564_, 0);
v_action_567_ = lean_ctor_get_uint8(v_a_564_, sizeof(void*)*3);
v_wantsRebuild_568_ = lean_ctor_get_uint8(v_a_564_, sizeof(void*)*3 + 1);
v_buildTime_569_ = lean_ctor_get(v_a_564_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_564_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v_a_564_, 1);
lean_dec(v_unused_580_);
v___x_571_ = v_a_564_;
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_buildTime_569_);
lean_inc(v_log_566_);
lean_dec(v_a_564_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = l_Lake_BuildTrace_nil(v_caption_558_);
v___x_574_ = lean_box(0);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_573_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_log_566_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_buildTime_569_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*3, v_action_567_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*3 + 1, v_wantsRebuild_568_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_574_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object* v_caption_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lake_newTrace(v_caption_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object* v_f_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_log_593_; uint8_t v_action_594_; uint8_t v_wantsRebuild_595_; lean_object* v_trace_596_; lean_object* v_buildTime_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_607_; 
v_log_593_ = lean_ctor_get(v_a_591_, 0);
v_action_594_ = lean_ctor_get_uint8(v_a_591_, sizeof(void*)*3);
v_wantsRebuild_595_ = lean_ctor_get_uint8(v_a_591_, sizeof(void*)*3 + 1);
v_trace_596_ = lean_ctor_get(v_a_591_, 1);
v_buildTime_597_ = lean_ctor_get(v_a_591_, 2);
v_isSharedCheck_607_ = !lean_is_exclusive(v_a_591_);
if (v_isSharedCheck_607_ == 0)
{
v___x_599_ = v_a_591_;
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_buildTime_597_);
lean_inc(v_trace_596_);
lean_inc(v_log_593_);
lean_dec(v_a_591_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_601_ = lean_box(0);
v___x_602_ = lean_apply_1(v_f_590_, v_trace_596_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v___x_602_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_log_593_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_buildTime_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_606_, sizeof(void*)*3, v_action_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_606_, sizeof(void*)*3 + 1, v_wantsRebuild_595_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_601_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg___boxed(lean_object* v_f_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lake_modifyTrace___redArg(v_f_608_, v_a_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object* v_f_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_log_620_; uint8_t v_action_621_; uint8_t v_wantsRebuild_622_; lean_object* v_trace_623_; lean_object* v_buildTime_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_634_; 
v_log_620_ = lean_ctor_get(v_a_618_, 0);
v_action_621_ = lean_ctor_get_uint8(v_a_618_, sizeof(void*)*3);
v_wantsRebuild_622_ = lean_ctor_get_uint8(v_a_618_, sizeof(void*)*3 + 1);
v_trace_623_ = lean_ctor_get(v_a_618_, 1);
v_buildTime_624_ = lean_ctor_get(v_a_618_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_634_ == 0)
{
v___x_626_ = v_a_618_;
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_buildTime_624_);
lean_inc(v_trace_623_);
lean_inc(v_log_620_);
lean_dec(v_a_618_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_box(0);
v___x_629_ = lean_apply_1(v_f_612_, v_trace_623_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_629_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_log_620_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_buildTime_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_633_, sizeof(void*)*3, v_action_621_);
lean_ctor_set_uint8(v_reuseFailAlloc_633_, sizeof(void*)*3 + 1, v_wantsRebuild_622_);
v___x_631_ = v_reuseFailAlloc_633_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_628_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object* v_f_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lake_modifyTrace(v_f_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object* v_caption_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_trace_647_; lean_object* v_log_648_; uint8_t v_action_649_; uint8_t v_wantsRebuild_650_; lean_object* v_buildTime_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_671_; 
v_trace_647_ = lean_ctor_get(v_a_645_, 1);
v_log_648_ = lean_ctor_get(v_a_645_, 0);
v_action_649_ = lean_ctor_get_uint8(v_a_645_, sizeof(void*)*3);
v_wantsRebuild_650_ = lean_ctor_get_uint8(v_a_645_, sizeof(void*)*3 + 1);
v_buildTime_651_ = lean_ctor_get(v_a_645_, 2);
v_isSharedCheck_671_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_671_ == 0)
{
v___x_653_ = v_a_645_;
v_isShared_654_ = v_isSharedCheck_671_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_buildTime_651_);
lean_inc(v_trace_647_);
lean_inc(v_log_648_);
lean_dec(v_a_645_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_671_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_inputs_655_; uint64_t v_hash_656_; lean_object* v_mtime_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_669_; 
v_inputs_655_ = lean_ctor_get(v_trace_647_, 1);
v_hash_656_ = lean_ctor_get_uint64(v_trace_647_, sizeof(void*)*3);
v_mtime_657_ = lean_ctor_get(v_trace_647_, 2);
v_isSharedCheck_669_ = !lean_is_exclusive(v_trace_647_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_trace_647_, 0);
lean_dec(v_unused_670_);
v___x_659_ = v_trace_647_;
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_mtime_657_);
lean_inc(v_inputs_655_);
lean_dec(v_trace_647_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_box(0);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_caption_644_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_caption_644_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_inputs_655_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_mtime_657_);
lean_ctor_set_uint64(v_reuseFailAlloc_668_, sizeof(void*)*3, v_hash_656_);
v___x_663_ = v_reuseFailAlloc_668_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_663_);
v___x_665_ = v___x_653_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_log_648_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_buildTime_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_667_, sizeof(void*)*3, v_action_649_);
lean_ctor_set_uint8(v_reuseFailAlloc_667_, sizeof(void*)*3 + 1, v_wantsRebuild_650_);
v___x_665_ = v_reuseFailAlloc_667_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_661_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
return v___x_666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg___boxed(lean_object* v_caption_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lake_setTraceCaption___redArg(v_caption_672_, v_a_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object* v_caption_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_trace_684_; lean_object* v_log_685_; uint8_t v_action_686_; uint8_t v_wantsRebuild_687_; lean_object* v_buildTime_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_708_; 
v_trace_684_ = lean_ctor_get(v_a_682_, 1);
v_log_685_ = lean_ctor_get(v_a_682_, 0);
v_action_686_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3);
v_wantsRebuild_687_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 1);
v_buildTime_688_ = lean_ctor_get(v_a_682_, 2);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_682_);
if (v_isSharedCheck_708_ == 0)
{
v___x_690_ = v_a_682_;
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_buildTime_688_);
lean_inc(v_trace_684_);
lean_inc(v_log_685_);
lean_dec(v_a_682_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_inputs_692_; uint64_t v_hash_693_; lean_object* v_mtime_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_706_; 
v_inputs_692_ = lean_ctor_get(v_trace_684_, 1);
v_hash_693_ = lean_ctor_get_uint64(v_trace_684_, sizeof(void*)*3);
v_mtime_694_ = lean_ctor_get(v_trace_684_, 2);
v_isSharedCheck_706_ = !lean_is_exclusive(v_trace_684_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_trace_684_, 0);
lean_dec(v_unused_707_);
v___x_696_ = v_trace_684_;
v_isShared_697_ = v_isSharedCheck_706_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_mtime_694_);
lean_inc(v_inputs_692_);
lean_dec(v_trace_684_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_706_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_box(0);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_caption_676_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_caption_676_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_inputs_692_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_mtime_694_);
lean_ctor_set_uint64(v_reuseFailAlloc_705_, sizeof(void*)*3, v_hash_693_);
v___x_700_ = v_reuseFailAlloc_705_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_700_);
v___x_702_ = v___x_690_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_log_685_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_buildTime_688_);
lean_ctor_set_uint8(v_reuseFailAlloc_704_, sizeof(void*)*3, v_action_686_);
lean_ctor_set_uint8(v_reuseFailAlloc_704_, sizeof(void*)*3 + 1, v_wantsRebuild_687_);
v___x_702_ = v_reuseFailAlloc_704_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_698_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
return v___x_703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object* v_caption_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lake_setTraceCaption(v_caption_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_717_;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lake_takeTrace___redArg___closed__0));
v___x_720_ = l_Lake_BuildTrace_nil(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object* v_a_721_){
_start:
{
lean_object* v_log_723_; uint8_t v_action_724_; uint8_t v_wantsRebuild_725_; lean_object* v_trace_726_; lean_object* v_buildTime_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v_log_723_ = lean_ctor_get(v_a_721_, 0);
v_action_724_ = lean_ctor_get_uint8(v_a_721_, sizeof(void*)*3);
v_wantsRebuild_725_ = lean_ctor_get_uint8(v_a_721_, sizeof(void*)*3 + 1);
v_trace_726_ = lean_ctor_get(v_a_721_, 1);
v_buildTime_727_ = lean_ctor_get(v_a_721_, 2);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_721_);
if (v_isSharedCheck_736_ == 0)
{
v___x_729_ = v_a_721_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_buildTime_727_);
lean_inc(v_trace_726_);
lean_inc(v_log_723_);
lean_dec(v_a_721_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_log_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_buildTime_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_735_, sizeof(void*)*3, v_action_724_);
lean_ctor_set_uint8(v_reuseFailAlloc_735_, sizeof(void*)*3 + 1, v_wantsRebuild_725_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_trace_726_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg___boxed(lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lake_takeTrace___redArg(v_a_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_log_747_; uint8_t v_action_748_; uint8_t v_wantsRebuild_749_; lean_object* v_trace_750_; lean_object* v_buildTime_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_760_; 
v_log_747_ = lean_ctor_get(v_a_745_, 0);
v_action_748_ = lean_ctor_get_uint8(v_a_745_, sizeof(void*)*3);
v_wantsRebuild_749_ = lean_ctor_get_uint8(v_a_745_, sizeof(void*)*3 + 1);
v_trace_750_ = lean_ctor_get(v_a_745_, 1);
v_buildTime_751_ = lean_ctor_get(v_a_745_, 2);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_745_);
if (v_isSharedCheck_760_ == 0)
{
v___x_753_ = v_a_745_;
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_buildTime_751_);
lean_inc(v_trace_750_);
lean_inc(v_log_747_);
lean_dec(v_a_745_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_log_747_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_buildTime_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_759_, sizeof(void*)*3, v_action_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_759_, sizeof(void*)*3 + 1, v_wantsRebuild_749_);
v___x_757_ = v_reuseFailAlloc_759_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_trace_750_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lake_takeTrace(v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object* v_trace_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_log_772_; uint8_t v_action_773_; uint8_t v_wantsRebuild_774_; lean_object* v_trace_775_; lean_object* v_buildTime_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
v_log_772_ = lean_ctor_get(v_a_770_, 0);
v_action_773_ = lean_ctor_get_uint8(v_a_770_, sizeof(void*)*3);
v_wantsRebuild_774_ = lean_ctor_get_uint8(v_a_770_, sizeof(void*)*3 + 1);
v_trace_775_ = lean_ctor_get(v_a_770_, 1);
v_buildTime_776_ = lean_ctor_get(v_a_770_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_784_ == 0)
{
v___x_778_ = v_a_770_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_buildTime_776_);
lean_inc(v_trace_775_);
lean_inc(v_log_772_);
lean_dec(v_a_770_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_trace_769_);
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_log_772_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_trace_769_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_buildTime_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*3, v_action_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*3 + 1, v_wantsRebuild_774_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_trace_775_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg___boxed(lean_object* v_trace_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lake_swapTrace___redArg(v_trace_785_, v_a_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object* v_trace_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_log_797_; uint8_t v_action_798_; uint8_t v_wantsRebuild_799_; lean_object* v_trace_800_; lean_object* v_buildTime_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_log_797_ = lean_ctor_get(v_a_795_, 0);
v_action_798_ = lean_ctor_get_uint8(v_a_795_, sizeof(void*)*3);
v_wantsRebuild_799_ = lean_ctor_get_uint8(v_a_795_, sizeof(void*)*3 + 1);
v_trace_800_ = lean_ctor_get(v_a_795_, 1);
v_buildTime_801_ = lean_ctor_get(v_a_795_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_a_795_);
if (v_isSharedCheck_809_ == 0)
{
v___x_803_ = v_a_795_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_buildTime_801_);
lean_inc(v_trace_800_);
lean_inc(v_log_797_);
lean_dec(v_a_795_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_trace_789_);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_log_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_trace_789_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_buildTime_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_808_, sizeof(void*)*3, v_action_798_);
lean_ctor_set_uint8(v_reuseFailAlloc_808_, sizeof(void*)*3 + 1, v_wantsRebuild_799_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_trace_800_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object* v_trace_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lake_swapTrace(v_trace_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object* v_trace_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_log_822_; uint8_t v_action_823_; uint8_t v_wantsRebuild_824_; lean_object* v_trace_825_; lean_object* v_buildTime_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_836_; 
v_log_822_ = lean_ctor_get(v_a_820_, 0);
v_action_823_ = lean_ctor_get_uint8(v_a_820_, sizeof(void*)*3);
v_wantsRebuild_824_ = lean_ctor_get_uint8(v_a_820_, sizeof(void*)*3 + 1);
v_trace_825_ = lean_ctor_get(v_a_820_, 1);
v_buildTime_826_ = lean_ctor_get(v_a_820_, 2);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_836_ == 0)
{
v___x_828_ = v_a_820_;
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_buildTime_826_);
lean_inc(v_trace_825_);
lean_inc(v_log_822_);
lean_dec(v_a_820_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_830_ = lean_box(0);
v___x_831_ = l_Lake_BuildTrace_mix(v_trace_825_, v_trace_819_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_log_822_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_buildTime_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*3, v_action_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*3 + 1, v_wantsRebuild_824_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_830_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg___boxed(lean_object* v_trace_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_addTrace___redArg(v_trace_837_, v_a_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object* v_trace_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_log_849_; uint8_t v_action_850_; uint8_t v_wantsRebuild_851_; lean_object* v_trace_852_; lean_object* v_buildTime_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_863_; 
v_log_849_ = lean_ctor_get(v_a_847_, 0);
v_action_850_ = lean_ctor_get_uint8(v_a_847_, sizeof(void*)*3);
v_wantsRebuild_851_ = lean_ctor_get_uint8(v_a_847_, sizeof(void*)*3 + 1);
v_trace_852_ = lean_ctor_get(v_a_847_, 1);
v_buildTime_853_ = lean_ctor_get(v_a_847_, 2);
v_isSharedCheck_863_ = !lean_is_exclusive(v_a_847_);
if (v_isSharedCheck_863_ == 0)
{
v___x_855_ = v_a_847_;
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_buildTime_853_);
lean_inc(v_trace_852_);
lean_inc(v_log_849_);
lean_dec(v_a_847_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = lean_box(0);
v___x_858_ = l_Lake_BuildTrace_mix(v_trace_852_, v_trace_841_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_log_849_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_buildTime_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_862_, sizeof(void*)*3, v_action_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_862_, sizeof(void*)*3 + 1, v_wantsRebuild_851_);
v___x_860_ = v_reuseFailAlloc_862_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_857_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object* v_trace_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lake_addTrace(v_trace_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg(lean_object* v_caption_873_, lean_object* v_x_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_log_882_; uint8_t v_action_883_; uint8_t v_wantsRebuild_884_; lean_object* v_trace_885_; lean_object* v_buildTime_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_917_; 
v_log_882_ = lean_ctor_get(v_a_880_, 0);
v_action_883_ = lean_ctor_get_uint8(v_a_880_, sizeof(void*)*3);
v_wantsRebuild_884_ = lean_ctor_get_uint8(v_a_880_, sizeof(void*)*3 + 1);
v_trace_885_ = lean_ctor_get(v_a_880_, 1);
v_buildTime_886_ = lean_ctor_get(v_a_880_, 2);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_880_);
if (v_isSharedCheck_917_ == 0)
{
v___x_888_ = v_a_880_;
v_isShared_889_ = v_isSharedCheck_917_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_buildTime_886_);
lean_inc(v_trace_885_);
lean_inc(v_log_882_);
lean_dec(v_a_880_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_917_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = l_Lake_BuildTrace_nil(v_caption_873_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_log_882_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_buildTime_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*3, v_action_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*3 + 1, v_wantsRebuild_884_);
v___x_892_ = v_reuseFailAlloc_916_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; 
v___x_893_ = lean_apply_7(v_x_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v___x_892_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_915_; 
v_a_894_ = lean_ctor_get(v___x_893_, 1);
v_a_895_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_915_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_915_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_894_);
lean_inc(v_a_895_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_915_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_log_899_; uint8_t v_action_900_; uint8_t v_wantsRebuild_901_; lean_object* v_trace_902_; lean_object* v_buildTime_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_914_; 
v_log_899_ = lean_ctor_get(v_a_894_, 0);
v_action_900_ = lean_ctor_get_uint8(v_a_894_, sizeof(void*)*3);
v_wantsRebuild_901_ = lean_ctor_get_uint8(v_a_894_, sizeof(void*)*3 + 1);
v_trace_902_ = lean_ctor_get(v_a_894_, 1);
v_buildTime_903_ = lean_ctor_get(v_a_894_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v_a_894_);
if (v_isSharedCheck_914_ == 0)
{
v___x_905_ = v_a_894_;
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_buildTime_903_);
lean_inc(v_trace_902_);
lean_inc(v_log_899_);
lean_dec(v_a_894_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = l_Lake_BuildTrace_mix(v_trace_885_, v_trace_902_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_907_);
v___x_909_ = v___x_905_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_log_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_buildTime_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3, v_action_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 1, v_wantsRebuild_901_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_909_);
v___x_911_ = v___x_897_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_895_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
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
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg___boxed(lean_object* v_caption_918_, lean_object* v_x_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lake_addSubTrace___redArg(v_caption_918_, v_x_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object* v_00_u03b1_928_, lean_object* v_caption_929_, lean_object* v_x_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_log_938_; uint8_t v_action_939_; uint8_t v_wantsRebuild_940_; lean_object* v_trace_941_; lean_object* v_buildTime_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_973_; 
v_log_938_ = lean_ctor_get(v_a_936_, 0);
v_action_939_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*3);
v_wantsRebuild_940_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*3 + 1);
v_trace_941_ = lean_ctor_get(v_a_936_, 1);
v_buildTime_942_ = lean_ctor_get(v_a_936_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_973_ == 0)
{
v___x_944_ = v_a_936_;
v_isShared_945_ = v_isSharedCheck_973_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_buildTime_942_);
lean_inc(v_trace_941_);
lean_inc(v_log_938_);
lean_dec(v_a_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_973_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = l_Lake_BuildTrace_nil(v_caption_929_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_log_938_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_buildTime_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_action_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 1, v_wantsRebuild_940_);
v___x_948_ = v_reuseFailAlloc_972_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
v___x_949_ = lean_apply_7(v_x_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v___x_948_, lean_box(0));
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_971_; 
v_a_950_ = lean_ctor_get(v___x_949_, 1);
v_a_951_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_971_ == 0)
{
v___x_953_ = v___x_949_;
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_950_);
lean_inc(v_a_951_);
lean_dec(v___x_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_log_955_; uint8_t v_action_956_; uint8_t v_wantsRebuild_957_; lean_object* v_trace_958_; lean_object* v_buildTime_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_970_; 
v_log_955_ = lean_ctor_get(v_a_950_, 0);
v_action_956_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*3);
v_wantsRebuild_957_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*3 + 1);
v_trace_958_ = lean_ctor_get(v_a_950_, 1);
v_buildTime_959_ = lean_ctor_get(v_a_950_, 2);
v_isSharedCheck_970_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_970_ == 0)
{
v___x_961_ = v_a_950_;
v_isShared_962_ = v_isSharedCheck_970_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_buildTime_959_);
lean_inc(v_trace_958_);
lean_inc(v_log_955_);
lean_dec(v_a_950_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_970_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = l_Lake_BuildTrace_mix(v_trace_941_, v_trace_958_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_log_955_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_buildTime_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*3, v_action_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*3 + 1, v_wantsRebuild_957_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_965_);
v___x_967_ = v___x_953_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_951_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
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
LEAN_EXPORT lean_object* l_Lake_addSubTrace___boxed(lean_object* v_00_u03b1_974_, lean_object* v_caption_975_, lean_object* v_x_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lake_addSubTrace(v_00_u03b1_974_, v_caption_975_, v_x_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg(lean_object* v_f_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_apply_7(v_f_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, lean_box(0));
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg___boxed(lean_object* v_f_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lake_SpawnM_ofFn___redArg(v_f_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn(lean_object* v_00_u03b1_1003_, lean_object* v_f_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_apply_7(v_f_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, lean_box(0));
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_f_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lake_SpawnM_ofFn(v_00_u03b1_1013_, v_f_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg(lean_object* v_self_1023_, lean_object* v_fetch_1024_, lean_object* v_pkg_x3f_1025_, lean_object* v_stack_1026_, lean_object* v_store_1027_, lean_object* v_ctx_1028_, lean_object* v_s_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_apply_7(v_self_1023_, v_fetch_1024_, v_pkg_x3f_1025_, v_stack_1026_, v_store_1027_, v_ctx_1028_, v_s_1029_, lean_box(0));
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg___boxed(lean_object* v_self_1032_, lean_object* v_fetch_1033_, lean_object* v_pkg_x3f_1034_, lean_object* v_stack_1035_, lean_object* v_store_1036_, lean_object* v_ctx_1037_, lean_object* v_s_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lake_SpawnM_toFn___redArg(v_self_1032_, v_fetch_1033_, v_pkg_x3f_1034_, v_stack_1035_, v_store_1036_, v_ctx_1037_, v_s_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn(lean_object* v_00_u03b1_1041_, lean_object* v_self_1042_, lean_object* v_fetch_1043_, lean_object* v_pkg_x3f_1044_, lean_object* v_stack_1045_, lean_object* v_store_1046_, lean_object* v_ctx_1047_, lean_object* v_s_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_apply_7(v_self_1042_, v_fetch_1043_, v_pkg_x3f_1044_, v_stack_1045_, v_store_1046_, v_ctx_1047_, v_s_1048_, lean_box(0));
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_self_1052_, lean_object* v_fetch_1053_, lean_object* v_pkg_x3f_1054_, lean_object* v_stack_1055_, lean_object* v_store_1056_, lean_object* v_ctx_1057_, lean_object* v_s_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lake_SpawnM_toFn(v_00_u03b1_1051_, v_self_1052_, v_fetch_1053_, v_pkg_x3f_1054_, v_stack_1055_, v_store_1056_, v_ctx_1057_, v_s_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object* v_x_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_trace_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_trace_1069_ = lean_ctor_get(v_a_1067_, 1);
lean_inc_ref(v_trace_1069_);
v___x_1070_ = lean_apply_7(v_x_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_trace_1069_, lean_box(0));
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_a_1067_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg___boxed(lean_object* v_x_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lake_JobM_runSpawnM___redArg(v_x_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object* v_00_u03b1_1081_, lean_object* v_x_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_trace_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_trace_1090_ = lean_ctor_get(v_a_1088_, 1);
lean_inc_ref(v_trace_1090_);
v___x_1091_ = lean_apply_7(v_x_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_trace_1090_, lean_box(0));
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v_a_1088_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_x_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lake_JobM_runSpawnM(v_00_u03b1_1093_, v_x_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object* v_x_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
uint8_t v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1113_ = 0;
v___x_1114_ = 0;
v___x_1115_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1117_, 0, v_a_1111_);
lean_ctor_set(v___x_1117_, 1, v___x_1115_);
lean_ctor_set(v___x_1117_, 2, v___x_1116_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*3, v___x_1113_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*3 + 1, v___x_1114_);
v___x_1118_ = lean_apply_7(v_x_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v___x_1117_, lean_box(0));
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 1);
v_a_1120_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1119_);
lean_inc(v_a_1120_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_log_1124_; lean_object* v___x_1126_; 
v_log_1124_ = lean_ctor_get(v_a_1119_, 0);
lean_inc_ref(v_log_1124_);
lean_dec(v_a_1119_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v_log_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1120_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_log_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_a_1129_ = lean_ctor_get(v___x_1118_, 1);
v_a_1130_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v___x_1118_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1129_);
lean_inc(v_a_1130_);
lean_dec(v___x_1118_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_log_1134_; lean_object* v___x_1136_; 
v_log_1134_ = lean_ctor_get(v_a_1129_, 0);
lean_inc_ref(v_log_1134_);
lean_dec(v_a_1129_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v_log_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_log_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg___boxed(lean_object* v_x_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lake_FetchM_runJobM___redArg(v_x_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object* v_00_u03b1_1148_, lean_object* v_x_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
uint8_t v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1157_ = 0;
v___x_1158_ = 0;
v___x_1159_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1161_, 0, v_a_1155_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
lean_ctor_set(v___x_1161_, 2, v___x_1160_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3, v___x_1157_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3 + 1, v___x_1158_);
v___x_1162_ = lean_apply_7(v_x_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v___x_1161_, lean_box(0));
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 1);
v_a_1164_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1162_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1163_);
lean_inc(v_a_1164_);
lean_dec(v___x_1162_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_log_1168_; lean_object* v___x_1170_; 
v_log_1168_ = lean_ctor_get(v_a_1163_, 0);
lean_inc_ref(v_log_1168_);
lean_dec(v_a_1163_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_log_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_log_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
v_a_1173_ = lean_ctor_get(v___x_1162_, 1);
v_a_1174_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1176_ = v___x_1162_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1173_);
lean_inc(v_a_1174_);
lean_dec(v___x_1162_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_log_1178_; lean_object* v___x_1180_; 
v_log_1178_ = lean_ctor_get(v_a_1173_, 0);
lean_inc_ref(v_log_1178_);
lean_dec(v_a_1173_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_log_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1174_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_log_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_x_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lake_FetchM_runJobM(v_00_u03b1_1183_, v_x_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object* v_x_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_log_1203_; uint8_t v_action_1204_; uint8_t v_wantsRebuild_1205_; lean_object* v_trace_1206_; lean_object* v_buildTime_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1236_; 
v_log_1203_ = lean_ctor_get(v_a_1201_, 0);
v_action_1204_ = lean_ctor_get_uint8(v_a_1201_, sizeof(void*)*3);
v_wantsRebuild_1205_ = lean_ctor_get_uint8(v_a_1201_, sizeof(void*)*3 + 1);
v_trace_1206_ = lean_ctor_get(v_a_1201_, 1);
v_buildTime_1207_ = lean_ctor_get(v_a_1201_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_a_1201_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1209_ = v_a_1201_;
v_isShared_1210_ = v_isSharedCheck_1236_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_buildTime_1207_);
lean_inc(v_trace_1206_);
lean_inc(v_log_1203_);
lean_dec(v_a_1201_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1236_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_apply_7(v_x_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_log_1203_, lean_box(0));
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1223_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_a_1213_ = lean_ctor_get(v___x_1211_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1215_ = v___x_1211_;
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v_a_1213_);
v___x_1218_ = v___x_1209_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1213_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_trace_1206_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_buildTime_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*3, v_action_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*3 + 1, v_wantsRebuild_1205_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1212_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1235_; 
v_a_1224_ = lean_ctor_get(v___x_1211_, 0);
v_a_1225_ = lean_ctor_get(v___x_1211_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1227_ = v___x_1211_;
v_isShared_1228_ = v_isSharedCheck_1235_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_dec(v___x_1211_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1235_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v_a_1225_);
v___x_1230_ = v___x_1209_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1225_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_trace_1206_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_buildTime_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3, v_action_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 1, v_wantsRebuild_1205_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1230_);
v___x_1232_ = v___x_1227_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1224_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg___boxed(lean_object* v_x_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lake_JobM_runFetchM___redArg(v_x_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object* v_00_u03b1_1246_, lean_object* v_x_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_log_1255_; uint8_t v_action_1256_; uint8_t v_wantsRebuild_1257_; lean_object* v_trace_1258_; lean_object* v_buildTime_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1288_; 
v_log_1255_ = lean_ctor_get(v_a_1253_, 0);
v_action_1256_ = lean_ctor_get_uint8(v_a_1253_, sizeof(void*)*3);
v_wantsRebuild_1257_ = lean_ctor_get_uint8(v_a_1253_, sizeof(void*)*3 + 1);
v_trace_1258_ = lean_ctor_get(v_a_1253_, 1);
v_buildTime_1259_ = lean_ctor_get(v_a_1253_, 2);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_a_1253_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1261_ = v_a_1253_;
v_isShared_1262_ = v_isSharedCheck_1288_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_buildTime_1259_);
lean_inc(v_trace_1258_);
lean_inc(v_log_1255_);
lean_dec(v_a_1253_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1288_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_apply_7(v_x_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_log_1255_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1275_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_a_1265_ = lean_ctor_get(v___x_1263_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1267_ = v___x_1263_;
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_a_1265_);
v___x_1270_ = v___x_1261_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1265_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_trace_1258_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_buildTime_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3, v_action_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3 + 1, v_wantsRebuild_1257_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v___x_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1264_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1287_; 
v_a_1276_ = lean_ctor_get(v___x_1263_, 0);
v_a_1277_ = lean_ctor_get(v___x_1263_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1279_ = v___x_1263_;
v_isShared_1280_ = v_isSharedCheck_1287_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_inc(v_a_1276_);
lean_dec(v___x_1263_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1287_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_a_1277_);
v___x_1282_ = v___x_1261_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1277_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_trace_1258_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_buildTime_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1286_, sizeof(void*)*3, v_action_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1286_, sizeof(void*)*3 + 1, v_wantsRebuild_1257_);
v___x_1282_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1284_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1276_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_x_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lake_JobM_runFetchM(v_00_u03b1_1289_, v_x_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object* v_inst_1301_, lean_object* v_caption_1302_, uint8_t v_optional_1303_, lean_object* v_toPure_1304_, lean_object* v_____do__lift_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1306_, 0, v_____do__lift_1305_);
lean_ctor_set(v___x_1306_, 1, v_inst_1301_);
lean_ctor_set(v___x_1306_, 2, v_caption_1302_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3, v_optional_1303_);
v___x_1307_ = lean_apply_2(v_toPure_1304_, lean_box(0), v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object* v_inst_1308_, lean_object* v_caption_1309_, lean_object* v_optional_1310_, lean_object* v_toPure_1311_, lean_object* v_____do__lift_1312_){
_start:
{
uint8_t v_optional_boxed_1313_; lean_object* v_res_1314_; 
v_optional_boxed_1313_ = lean_unbox(v_optional_1310_);
v_res_1314_ = l_Lake_Job_bindTask___redArg___lam__0(v_inst_1308_, v_caption_1309_, v_optional_boxed_1313_, v_toPure_1311_, v_____do__lift_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_f_1317_, lean_object* v_self_1318_){
_start:
{
lean_object* v_toApplicative_1319_; lean_object* v_toBind_1320_; lean_object* v_task_1321_; lean_object* v_caption_1322_; uint8_t v_optional_1323_; lean_object* v_toPure_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___f_1327_; lean_object* v___x_1328_; 
v_toApplicative_1319_ = lean_ctor_get(v_inst_1315_, 0);
lean_inc_ref(v_toApplicative_1319_);
v_toBind_1320_ = lean_ctor_get(v_inst_1315_, 1);
lean_inc(v_toBind_1320_);
lean_dec_ref(v_inst_1315_);
v_task_1321_ = lean_ctor_get(v_self_1318_, 0);
lean_inc_ref(v_task_1321_);
v_caption_1322_ = lean_ctor_get(v_self_1318_, 2);
lean_inc_ref(v_caption_1322_);
v_optional_1323_ = lean_ctor_get_uint8(v_self_1318_, sizeof(void*)*3);
lean_dec_ref(v_self_1318_);
v_toPure_1324_ = lean_ctor_get(v_toApplicative_1319_, 1);
lean_inc(v_toPure_1324_);
lean_dec_ref(v_toApplicative_1319_);
v___x_1325_ = lean_apply_1(v_f_1317_, v_task_1321_);
v___x_1326_ = lean_box(v_optional_1323_);
v___f_1327_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1327_, 0, v_inst_1316_);
lean_closure_set(v___f_1327_, 1, v_caption_1322_);
lean_closure_set(v___f_1327_, 2, v___x_1326_);
lean_closure_set(v___f_1327_, 3, v_toPure_1324_);
v___x_1328_ = lean_apply_4(v_toBind_1320_, lean_box(0), lean_box(0), v___x_1325_, v___f_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object* v_m_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_00_u03b1_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_f_1334_, lean_object* v_self_1335_){
_start:
{
lean_object* v_toApplicative_1336_; lean_object* v_toBind_1337_; lean_object* v_task_1338_; lean_object* v_caption_1339_; uint8_t v_optional_1340_; lean_object* v_toPure_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; 
v_toApplicative_1336_ = lean_ctor_get(v_inst_1332_, 0);
lean_inc_ref(v_toApplicative_1336_);
v_toBind_1337_ = lean_ctor_get(v_inst_1332_, 1);
lean_inc(v_toBind_1337_);
lean_dec_ref(v_inst_1332_);
v_task_1338_ = lean_ctor_get(v_self_1335_, 0);
lean_inc_ref(v_task_1338_);
v_caption_1339_ = lean_ctor_get(v_self_1335_, 2);
lean_inc_ref(v_caption_1339_);
v_optional_1340_ = lean_ctor_get_uint8(v_self_1335_, sizeof(void*)*3);
lean_dec_ref(v_self_1335_);
v_toPure_1341_ = lean_ctor_get(v_toApplicative_1336_, 1);
lean_inc(v_toPure_1341_);
lean_dec_ref(v_toApplicative_1336_);
v___x_1342_ = lean_apply_1(v_f_1334_, v_task_1338_);
v___x_1343_ = lean_box(v_optional_1340_);
v___f_1344_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1344_, 0, v_inst_1333_);
lean_closure_set(v___f_1344_, 1, v_caption_1339_);
lean_closure_set(v___f_1344_, 2, v___x_1343_);
lean_closure_set(v___f_1344_, 3, v_toPure_1341_);
v___x_1345_ = lean_apply_4(v_toBind_1337_, lean_box(0), lean_box(0), v___x_1342_, v___f_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Job_sync_spec__0(lean_object* v_msg_1347_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_1349_ = lean_panic_fn(v___x_1348_, v_msg_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0(lean_object* v_val_1350_, lean_object* v_val_1351_, lean_object* v_a_x3f_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1355_ = lean_get_set_stdout(v_val_1350_);
lean_dec_ref(v___x_1355_);
v___x_1356_ = lean_get_set_stderr(v_val_1351_);
lean_dec_ref(v___x_1356_);
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___y_1353_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0___boxed(lean_object* v_val_1359_, lean_object* v_val_1360_, lean_object* v_a_x3f_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lake_Job_sync___redArg___lam__0(v_val_1359_, v_val_1360_, v_a_x3f_1361_, v___y_1362_);
lean_dec(v_a_x3f_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1(lean_object* v_a_1365_, lean_object* v_____r_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1365_);
lean_ctor_set(v___x_1374_, 1, v___y_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1___boxed(lean_object* v_a_1375_, lean_object* v_____r_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lake_Job_sync___redArg___lam__1(v_a_1375_, v_____r_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1384_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__0(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = l_ByteArray_empty;
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___x_1385_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__2(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1392_ = 0;
v___x_1393_ = 0;
v___x_1394_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1395_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1391_);
lean_ctor_set(v___x_1395_, 2, v___x_1390_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3, v___x_1393_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3 + 1, v___x_1392_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__7(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__6));
v___x_1401_ = lean_unsigned_to_nat(46u);
v___x_1402_ = lean_unsigned_to_nat(193u);
v___x_1403_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__5));
v___x_1404_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__4));
v___x_1405_ = l_mkPanicMessageWithDecl(v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg(lean_object* v_inst_1406_, lean_object* v_act_1407_, lean_object* v_caption_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_val_1416_; lean_object* v___y_1421_; lean_object* v_a_1423_; lean_object* v_a_1424_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1428_ = lean_st_mk_ref(v___x_1427_);
lean_inc(v___x_1428_);
v___x_1429_ = l_IO_FS_Stream_ofBuffer(v___x_1428_);
lean_inc_ref(v___x_1429_);
v___x_1430_ = lean_get_set_stdout(v___x_1429_);
v___x_1431_ = lean_get_set_stderr(v___x_1429_);
v___x_1432_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__2, &l_Lake_Job_sync___redArg___closed__2_once, _init_l_Lake_Job_sync___redArg___closed__2);
lean_inc_ref(v_a_1413_);
lean_inc(v_a_1412_);
lean_inc(v_a_1411_);
lean_inc(v_a_1410_);
lean_inc_ref(v_a_1409_);
v___x_1433_ = lean_apply_7(v_act_1407_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v___x_1432_, lean_box(0));
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v_log_1440_; uint8_t v_action_1441_; uint8_t v_wantsRebuild_1442_; lean_object* v_trace_1443_; lean_object* v_buildTime_1444_; lean_object* v_data_1445_; lean_object* v___y_1447_; uint8_t v___x_1472_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
v_a_1435_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1433_);
lean_inc(v_a_1434_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1434_);
v___x_1437_ = l_Lake_Job_sync___redArg___lam__0(v___x_1430_, v___x_1431_, v___x_1436_, v_a_1435_);
lean_dec_ref(v___x_1436_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = lean_st_ref_get(v___x_1428_);
lean_dec(v___x_1428_);
v_log_1440_ = lean_ctor_get(v_a_1438_, 0);
v_action_1441_ = lean_ctor_get_uint8(v_a_1438_, sizeof(void*)*3);
v_wantsRebuild_1442_ = lean_ctor_get_uint8(v_a_1438_, sizeof(void*)*3 + 1);
v_trace_1443_ = lean_ctor_get(v_a_1438_, 1);
v_buildTime_1444_ = lean_ctor_get(v_a_1438_, 2);
v_data_1445_ = lean_ctor_get(v___x_1439_, 0);
lean_inc_ref(v_data_1445_);
lean_dec(v___x_1439_);
v___x_1472_ = lean_string_validate_utf8(v_data_1445_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v_data_1445_);
v___x_1473_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1474_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1473_);
v___y_1447_ = v___x_1474_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_string_from_utf8_unchecked(v_data_1445_);
v___y_1447_ = v___x_1475_;
goto v___jp_1446_;
}
v___jp_1446_:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = lean_string_utf8_byte_size(v___y_1447_);
v___x_1449_ = lean_nat_dec_eq(v___x_1448_, v___x_1426_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1466_; 
lean_inc(v_buildTime_1444_);
lean_inc_ref(v_trace_1443_);
lean_inc_ref(v_log_1440_);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1467_ = lean_ctor_get(v_a_1438_, 2);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_a_1438_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_a_1438_, 0);
lean_dec(v_unused_1469_);
v___x_1451_ = v_a_1438_;
v_isShared_1452_ = v_isSharedCheck_1466_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_a_1438_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1466_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1453_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1454_, 0, v___y_1447_);
lean_ctor_set(v___x_1454_, 1, v___x_1426_);
lean_ctor_set(v___x_1454_, 2, v___x_1448_);
v___x_1455_ = l_String_Slice_trimAscii(v___x_1454_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = l_String_Slice_toString(v___x_1455_);
lean_dec_ref(v___x_1455_);
v___x_1457_ = lean_string_append(v___x_1453_, v___x_1456_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = 1;
v___x_1459_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*1, v___x_1458_);
v___x_1460_ = lean_box(0);
v___x_1461_ = lean_array_push(v_log_1440_, v___x_1459_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1461_);
v___x_1463_ = v___x_1451_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_trace_1443_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_buildTime_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*3, v_action_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*3 + 1, v_wantsRebuild_1442_);
v___x_1463_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lake_Job_sync___redArg___lam__1(v_a_1434_, v___x_1460_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v___x_1463_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
v___y_1421_ = v___x_1464_;
goto v___jp_1420_;
}
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v___y_1447_);
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Lake_Job_sync___redArg___lam__1(v_a_1434_, v___x_1470_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1438_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
v___y_1421_ = v___x_1471_;
goto v___jp_1420_;
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v_a_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_a_1480_; 
lean_dec(v___x_1428_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
v_a_1476_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1476_);
v_a_1477_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1433_);
v___x_1478_ = lean_box(0);
v___x_1479_ = l_Lake_Job_sync___redArg___lam__0(v___x_1430_, v___x_1431_, v___x_1478_, v_a_1477_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_a_1480_);
lean_dec_ref(v___x_1479_);
v_a_1423_ = v_a_1476_;
v_a_1424_ = v_a_1480_;
goto v___jp_1422_;
}
v___jp_1415_:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_task_pure(v_val_1416_);
v___x_1418_ = 0;
v___x_1419_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v_inst_1406_);
lean_ctor_set(v___x_1419_, 2, v_caption_1408_);
lean_ctor_set_uint8(v___x_1419_, sizeof(void*)*3, v___x_1418_);
return v___x_1419_;
}
v___jp_1420_:
{
v_val_1416_ = v___y_1421_;
goto v___jp_1415_;
}
v___jp_1422_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1423_);
lean_ctor_set(v___x_1425_, 1, v_a_1424_);
v_val_1416_ = v___x_1425_;
goto v___jp_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___boxed(lean_object* v_inst_1481_, lean_object* v_act_1482_, lean_object* v_caption_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lake_Job_sync___redArg(v_inst_1481_, v_act_1482_, v_caption_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync(lean_object* v_00_u03b1_1491_, lean_object* v_inst_1492_, lean_object* v_act_1493_, lean_object* v_caption_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lake_Job_sync___redArg(v_inst_1492_, v_act_1493_, v_caption_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_inst_1504_, lean_object* v_act_1505_, lean_object* v_caption_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lake_Job_sync(v_00_u03b1_1503_, v_inst_1504_, v_act_1505_, v_caption_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
lean_dec_ref(v_a_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1(lean_object* v___x_1515_, lean_object* v___x_1516_, uint8_t v___x_1517_, uint8_t v___x_1518_, lean_object* v___x_1519_, lean_object* v___x_1520_, lean_object* v_act_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_a_1529_; lean_object* v_a_1530_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1532_ = lean_st_mk_ref(v___x_1515_);
lean_inc(v___x_1532_);
v___x_1533_ = l_IO_FS_Stream_ofBuffer(v___x_1532_);
lean_inc_ref(v___x_1533_);
v___x_1534_ = lean_get_set_stdout(v___x_1533_);
v___x_1535_ = lean_get_set_stderr(v___x_1533_);
lean_inc(v___x_1520_);
v___x_1536_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1536_, 0, v___x_1516_);
lean_ctor_set(v___x_1536_, 1, v___x_1519_);
lean_ctor_set(v___x_1536_, 2, v___x_1520_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*3, v___x_1517_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*3 + 1, v___x_1518_);
v___x_1537_ = lean_apply_7(v_act_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v___x_1536_, lean_box(0));
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1584_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_a_1539_ = lean_ctor_get(v___x_1537_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1541_ = v___x_1537_;
v_isShared_1542_ = v_isSharedCheck_1584_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1584_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___y_1544_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v_log_1552_; uint8_t v_action_1553_; uint8_t v_wantsRebuild_1554_; lean_object* v_trace_1555_; lean_object* v_buildTime_1556_; lean_object* v___y_1558_; lean_object* v_data_1579_; uint8_t v___x_1580_; 
lean_inc(v_a_1538_);
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1538_);
v___x_1549_ = l_Lake_Job_sync___redArg___lam__0(v___x_1534_, v___x_1535_, v___x_1548_, v_a_1539_);
lean_dec_ref(v___x_1548_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 1);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = lean_st_ref_get(v___x_1532_);
lean_dec(v___x_1532_);
v_log_1552_ = lean_ctor_get(v_a_1550_, 0);
v_action_1553_ = lean_ctor_get_uint8(v_a_1550_, sizeof(void*)*3);
v_wantsRebuild_1554_ = lean_ctor_get_uint8(v_a_1550_, sizeof(void*)*3 + 1);
v_trace_1555_ = lean_ctor_get(v_a_1550_, 1);
v_buildTime_1556_ = lean_ctor_get(v_a_1550_, 2);
v_data_1579_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_ref(v_data_1579_);
lean_dec(v___x_1551_);
v___x_1580_ = lean_string_validate_utf8(v_data_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec_ref(v_data_1579_);
v___x_1581_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1582_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1581_);
v___y_1558_ = v___x_1582_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_string_from_utf8_unchecked(v_data_1579_);
v___y_1558_ = v___x_1583_;
goto v___jp_1557_;
}
v___jp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 1, v___y_1544_);
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1538_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___y_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
v___jp_1557_:
{
lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = lean_string_utf8_byte_size(v___y_1558_);
v___x_1560_ = lean_nat_dec_eq(v___x_1559_, v___x_1520_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1575_; 
lean_inc(v_buildTime_1556_);
lean_inc_ref(v_trace_1555_);
lean_inc_ref(v_log_1552_);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_a_1550_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1576_ = lean_ctor_get(v_a_1550_, 2);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_a_1550_, 1);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_a_1550_, 0);
lean_dec(v_unused_1578_);
v___x_1562_ = v_a_1550_;
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_a_1550_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1575_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1564_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___y_1558_);
lean_ctor_set(v___x_1565_, 1, v___x_1520_);
lean_ctor_set(v___x_1565_, 2, v___x_1559_);
v___x_1566_ = l_String_Slice_trimAscii(v___x_1565_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = l_String_Slice_toString(v___x_1566_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = lean_string_append(v___x_1564_, v___x_1567_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = 1;
v___x_1570_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*1, v___x_1569_);
v___x_1571_ = lean_array_push(v_log_1552_, v___x_1570_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1571_);
v___x_1573_ = v___x_1562_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_trace_1555_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_buildTime_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1574_, sizeof(void*)*3, v_action_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1574_, sizeof(void*)*3 + 1, v_wantsRebuild_1554_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
v___y_1544_ = v___x_1573_;
goto v___jp_1543_;
}
}
}
else
{
lean_dec_ref(v___y_1558_);
lean_dec(v___x_1520_);
v___y_1544_ = v_a_1550_;
goto v___jp_1543_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_a_1589_; 
lean_dec(v___x_1532_);
lean_dec(v___x_1520_);
v_a_1585_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1585_);
v_a_1586_ = lean_ctor_get(v___x_1537_, 1);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1537_);
v___x_1587_ = lean_box(0);
v___x_1588_ = l_Lake_Job_sync___redArg___lam__0(v___x_1534_, v___x_1535_, v___x_1587_, v_a_1586_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
v_a_1529_ = v_a_1585_;
v_a_1530_ = v_a_1589_;
goto v___jp_1528_;
}
v___jp_1528_:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_a_1529_);
lean_ctor_set(v___x_1531_, 1, v_a_1530_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1___boxed(lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v_act_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v___x_25174__boxed_1603_; uint8_t v___x_25175__boxed_1604_; lean_object* v_res_1605_; 
v___x_25174__boxed_1603_ = lean_unbox(v___x_1592_);
v___x_25175__boxed_1604_ = lean_unbox(v___x_1593_);
v_res_1605_ = l_Lake_Job_async___redArg___lam__1(v___x_1590_, v___x_1591_, v___x_25174__boxed_1603_, v___x_25175__boxed_1604_, v___x_1594_, v___x_1595_, v_act_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object* v_inst_1606_, lean_object* v_act_1607_, lean_object* v_prio_1608_, lean_object* v_caption_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1618_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1619_ = 0;
v___x_1620_ = 0;
v___x_1621_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1622_ = lean_box(v___x_1619_);
v___x_1623_ = lean_box(v___x_1620_);
v___f_1624_ = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_1624_, 0, v___x_1617_);
lean_closure_set(v___f_1624_, 1, v___x_1618_);
lean_closure_set(v___f_1624_, 2, v___x_1622_);
lean_closure_set(v___f_1624_, 3, v___x_1623_);
lean_closure_set(v___f_1624_, 4, v___x_1621_);
lean_closure_set(v___f_1624_, 5, v___x_1616_);
lean_closure_set(v___f_1624_, 6, v_act_1607_);
lean_closure_set(v___f_1624_, 7, v_a_1610_);
lean_closure_set(v___f_1624_, 8, v_a_1611_);
lean_closure_set(v___f_1624_, 9, v_a_1612_);
lean_closure_set(v___f_1624_, 10, v_a_1613_);
lean_closure_set(v___f_1624_, 11, v_a_1614_);
v___x_1625_ = lean_io_as_task(v___f_1624_, v_prio_1608_);
v___x_1626_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v_inst_1606_);
lean_ctor_set(v___x_1626_, 2, v_caption_1609_);
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*3, v___x_1620_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___boxed(lean_object* v_inst_1627_, lean_object* v_act_1628_, lean_object* v_prio_1629_, lean_object* v_caption_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lake_Job_async___redArg(v_inst_1627_, v_act_1628_, v_prio_1629_, v_caption_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object* v_00_u03b1_1638_, lean_object* v_inst_1639_, lean_object* v_act_1640_, lean_object* v_prio_1641_, lean_object* v_caption_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lake_Job_async___redArg(v_inst_1639_, v_act_1640_, v_prio_1641_, v_caption_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_inst_1652_, lean_object* v_act_1653_, lean_object* v_prio_1654_, lean_object* v_caption_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lake_Job_async(v_00_u03b1_1651_, v_inst_1652_, v_act_1653_, v_prio_1654_, v_caption_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec_ref(v_a_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object* v_self_1664_){
_start:
{
lean_object* v_task_1666_; lean_object* v___x_1667_; 
v_task_1666_ = lean_ctor_get(v_self_1664_, 0);
lean_inc_ref(v_task_1666_);
lean_dec_ref(v_self_1664_);
v___x_1667_ = lean_io_wait(v_task_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg___boxed(lean_object* v_self_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lake_Job_wait___redArg(v_self_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object* v_00_u03b1_1671_, lean_object* v_self_1672_){
_start:
{
lean_object* v_task_1674_; lean_object* v___x_1675_; 
v_task_1674_ = lean_ctor_get(v_self_1672_, 0);
lean_inc_ref(v_task_1674_);
lean_dec_ref(v_self_1672_);
v___x_1675_ = lean_io_wait(v_task_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_self_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lake_Job_wait(v_00_u03b1_1676_, v_self_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object* v_self_1680_){
_start:
{
lean_object* v_task_1682_; lean_object* v___x_1683_; 
v_task_1682_ = lean_ctor_get(v_self_1680_, 0);
lean_inc_ref(v_task_1682_);
lean_dec_ref(v_self_1680_);
v___x_1683_ = lean_io_wait(v_task_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_a_1684_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; 
lean_dec_ref(v___x_1683_);
v___x_1686_ = lean_box(0);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg___boxed(lean_object* v_self_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lake_Job_wait_x3f___redArg(v_self_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object* v_00_u03b1_1690_, lean_object* v_self_1691_){
_start:
{
lean_object* v_task_1693_; lean_object* v___x_1694_; 
v_task_1693_ = lean_ctor_get(v_self_1691_, 0);
lean_inc_ref(v_task_1693_);
lean_dec_ref(v_self_1691_);
v___x_1694_ = lean_io_wait(v_task_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1695_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; 
lean_dec_ref(v___x_1694_);
v___x_1697_ = lean_box(0);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___boxed(lean_object* v_00_u03b1_1698_, lean_object* v_self_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lake_Job_wait_x3f(v_00_u03b1_1698_, v_self_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(lean_object* v_as_1702_, size_t v_i_1703_, size_t v_stop_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_eq(v_i_1703_, v_stop_1704_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; 
v___x_1709_ = lean_array_uget_borrowed(v_as_1702_, v_i_1703_);
v___x_1710_ = lean_box(0);
lean_inc(v___x_1709_);
v___x_1711_ = lean_array_push(v___y_1706_, v___x_1709_);
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1703_, v___x_1712_);
v_i_1703_ = v___x_1713_;
v_b_1705_ = v___x_1710_;
v___y_1706_ = v___x_1711_;
goto _start;
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_b_1705_);
lean_ctor_set(v___x_1715_, 1, v___y_1706_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(lean_object* v_as_1716_, lean_object* v_i_1717_, lean_object* v_stop_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
size_t v_i_boxed_1722_; size_t v_stop_boxed_1723_; lean_object* v_res_1724_; 
v_i_boxed_1722_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_stop_boxed_1723_ = lean_unbox_usize(v_stop_1718_);
lean_dec(v_stop_1718_);
v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_1716_, v_i_boxed_1722_, v_stop_boxed_1723_, v_b_1719_, v___y_1720_);
lean_dec_ref(v_as_1716_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object* v_self_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_task_1728_; lean_object* v___x_1729_; 
v_task_1728_ = lean_ctor_get(v_self_1725_, 0);
lean_inc_ref(v_task_1728_);
lean_dec_ref(v_self_1725_);
v___x_1729_ = lean_io_wait(v_task_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1764_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_a_1731_ = lean_ctor_get(v___x_1729_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1733_ = v___x_1729_;
v_isShared_1734_ = v_isSharedCheck_1764_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1764_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_a_1736_; lean_object* v___y_1741_; lean_object* v_log_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_log_1752_ = lean_ctor_get(v_a_1731_, 0);
lean_inc_ref(v_log_1752_);
lean_dec(v_a_1731_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_array_get_size(v_log_1752_);
v___x_1755_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_dec_ref(v_log_1752_);
v_a_1736_ = v_a_1726_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_nat_dec_le(v___x_1754_, v___x_1754_);
if (v___x_1757_ == 0)
{
if (v___x_1755_ == 0)
{
lean_dec_ref(v_log_1752_);
v_a_1736_ = v_a_1726_;
goto v___jp_1735_;
}
else
{
size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = ((size_t)0ULL);
v___x_1759_ = lean_usize_of_nat(v___x_1754_);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1752_, v___x_1758_, v___x_1759_, v___x_1756_, v_a_1726_);
lean_dec_ref(v_log_1752_);
v___y_1741_ = v___x_1760_;
goto v___jp_1740_;
}
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_of_nat(v___x_1754_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1752_, v___x_1761_, v___x_1762_, v___x_1756_, v_a_1726_);
lean_dec_ref(v_log_1752_);
v___y_1741_ = v___x_1763_;
goto v___jp_1740_;
}
}
v___jp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_a_1736_);
v___x_1738_ = v___x_1733_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1730_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
v___jp_1740_:
{
if (lean_obj_tag(v___y_1741_) == 0)
{
lean_object* v_a_1742_; 
v_a_1742_ = lean_ctor_get(v___y_1741_, 1);
lean_inc(v_a_1742_);
lean_dec_ref(v___y_1741_);
v_a_1736_ = v_a_1742_;
goto v___jp_1735_;
}
else
{
lean_object* v_a_1743_; lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_del_object(v___x_1733_);
lean_dec(v_a_1730_);
v_a_1743_ = lean_ctor_get(v___y_1741_, 0);
v_a_1744_ = lean_ctor_get(v___y_1741_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___y_1741_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___y_1741_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_inc(v_a_1743_);
lean_dec(v___y_1741_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1743_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1799_; 
v_a_1765_ = lean_ctor_get(v___x_1729_, 0);
v_a_1766_ = lean_ctor_get(v___x_1729_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1768_ = v___x_1729_;
v_isShared_1769_ = v_isSharedCheck_1799_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_inc(v_a_1765_);
lean_dec(v___x_1729_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1799_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_a_1771_; lean_object* v___y_1776_; lean_object* v_log_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_log_1787_ = lean_ctor_get(v_a_1766_, 0);
lean_inc_ref(v_log_1787_);
lean_dec(v_a_1766_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_array_get_size(v_log_1787_);
v___x_1790_ = lean_nat_dec_lt(v___x_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v_log_1787_);
v_a_1771_ = v_a_1726_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_nat_dec_le(v___x_1789_, v___x_1789_);
if (v___x_1792_ == 0)
{
if (v___x_1790_ == 0)
{
lean_dec_ref(v_log_1787_);
v_a_1771_ = v_a_1726_;
goto v___jp_1770_;
}
else
{
size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = lean_usize_of_nat(v___x_1789_);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1787_, v___x_1793_, v___x_1794_, v___x_1791_, v_a_1726_);
lean_dec_ref(v_log_1787_);
v___y_1776_ = v___x_1795_;
goto v___jp_1775_;
}
}
else
{
size_t v___x_1796_; size_t v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = ((size_t)0ULL);
v___x_1797_ = lean_usize_of_nat(v___x_1789_);
v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1787_, v___x_1796_, v___x_1797_, v___x_1791_, v_a_1726_);
lean_dec_ref(v_log_1787_);
v___y_1776_ = v___x_1798_;
goto v___jp_1775_;
}
}
v___jp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v_a_1771_);
v___x_1773_ = v___x_1768_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1765_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_a_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
v___jp_1775_:
{
if (lean_obj_tag(v___y_1776_) == 0)
{
lean_object* v_a_1777_; 
v_a_1777_ = lean_ctor_get(v___y_1776_, 1);
lean_inc(v_a_1777_);
lean_dec_ref(v___y_1776_);
v_a_1771_ = v_a_1777_;
goto v___jp_1770_;
}
else
{
lean_object* v_a_1778_; lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_del_object(v___x_1768_);
lean_dec(v_a_1765_);
v_a_1778_ = lean_ctor_get(v___y_1776_, 0);
v_a_1779_ = lean_ctor_get(v___y_1776_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___y_1776_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___y_1776_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_inc(v_a_1778_);
lean_dec(v___y_1776_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1778_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object* v_self_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lake_Job_await___redArg(v_self_1800_, v_a_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object* v_00_u03b1_1804_, lean_object* v_self_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lake_Job_await___redArg(v_self_1805_, v_a_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_self_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lake_Job_await(v_00_u03b1_1809_, v_self_1810_, v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object* v_a_1814_, lean_object* v_f_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v_a_1824_; lean_object* v_a_1825_; 
if (lean_obj_tag(v_x_1821_) == 0)
{
lean_object* v_a_1827_; lean_object* v_a_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_log_1835_; uint8_t v_action_1836_; uint8_t v_wantsRebuild_1837_; lean_object* v_trace_1838_; lean_object* v_buildTime_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1900_; 
v_a_1827_ = lean_ctor_get(v_x_1821_, 0);
lean_inc(v_a_1827_);
v_a_1828_ = lean_ctor_get(v_x_1821_, 1);
lean_inc(v_a_1828_);
lean_dec_ref(v_x_1821_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1831_ = lean_st_mk_ref(v___x_1830_);
lean_inc(v___x_1831_);
v___x_1832_ = l_IO_FS_Stream_ofBuffer(v___x_1831_);
lean_inc_ref(v___x_1832_);
v___x_1833_ = lean_get_set_stdout(v___x_1832_);
v___x_1834_ = lean_get_set_stderr(v___x_1832_);
v_log_1835_ = lean_ctor_get(v_a_1828_, 0);
v_action_1836_ = lean_ctor_get_uint8(v_a_1828_, sizeof(void*)*3);
v_wantsRebuild_1837_ = lean_ctor_get_uint8(v_a_1828_, sizeof(void*)*3 + 1);
v_trace_1838_ = lean_ctor_get(v_a_1828_, 1);
v_buildTime_1839_ = lean_ctor_get(v_a_1828_, 2);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_a_1828_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1841_ = v_a_1828_;
v_isShared_1842_ = v_isSharedCheck_1900_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_buildTime_1839_);
lean_inc(v_trace_1838_);
lean_inc(v_log_1835_);
lean_dec(v_a_1828_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1900_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_trace_1843_; lean_object* v___x_1845_; 
v_trace_1843_ = l_Lake_BuildTrace_mix(v_a_1814_, v_trace_1838_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v_trace_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_log_1835_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_trace_1843_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_buildTime_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*3, v_action_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*3 + 1, v_wantsRebuild_1837_);
v___x_1845_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_apply_8(v_f_1815_, v_a_1827_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v___x_1845_, lean_box(0));
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1893_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_a_1848_ = lean_ctor_get(v___x_1846_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1850_ = v___x_1846_;
v_isShared_1851_ = v_isSharedCheck_1893_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1893_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___y_1853_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___x_1860_; lean_object* v_log_1861_; uint8_t v_action_1862_; uint8_t v_wantsRebuild_1863_; lean_object* v_trace_1864_; lean_object* v_buildTime_1865_; lean_object* v___y_1867_; lean_object* v_data_1888_; uint8_t v___x_1889_; 
lean_inc(v_a_1847_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_a_1847_);
v___x_1858_ = l_Lake_Job_sync___redArg___lam__0(v___x_1833_, v___x_1834_, v___x_1857_, v_a_1848_);
lean_dec_ref(v___x_1857_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 1);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = lean_st_ref_get(v___x_1831_);
lean_dec(v___x_1831_);
v_log_1861_ = lean_ctor_get(v_a_1859_, 0);
v_action_1862_ = lean_ctor_get_uint8(v_a_1859_, sizeof(void*)*3);
v_wantsRebuild_1863_ = lean_ctor_get_uint8(v_a_1859_, sizeof(void*)*3 + 1);
v_trace_1864_ = lean_ctor_get(v_a_1859_, 1);
v_buildTime_1865_ = lean_ctor_get(v_a_1859_, 2);
v_data_1888_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_data_1888_);
lean_dec(v___x_1860_);
v___x_1889_ = lean_string_validate_utf8(v_data_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v_data_1888_);
v___x_1890_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1891_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1890_);
v___y_1867_ = v___x_1891_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_string_from_utf8_unchecked(v_data_1888_);
v___y_1867_ = v___x_1892_;
goto v___jp_1866_;
}
v___jp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v___y_1853_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1847_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___y_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
v___jp_1866_:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_string_utf8_byte_size(v___y_1867_);
v___x_1869_ = lean_nat_dec_eq(v___x_1868_, v___x_1829_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1884_; 
lean_inc(v_buildTime_1865_);
lean_inc_ref(v_trace_1864_);
lean_inc_ref(v_log_1861_);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_a_1859_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; lean_object* v_unused_1886_; lean_object* v_unused_1887_; 
v_unused_1885_ = lean_ctor_get(v_a_1859_, 2);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_a_1859_, 1);
lean_dec(v_unused_1886_);
v_unused_1887_ = lean_ctor_get(v_a_1859_, 0);
lean_dec(v_unused_1887_);
v___x_1871_ = v_a_1859_;
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v_a_1859_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1873_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1874_, 0, v___y_1867_);
lean_ctor_set(v___x_1874_, 1, v___x_1829_);
lean_ctor_set(v___x_1874_, 2, v___x_1868_);
v___x_1875_ = l_String_Slice_trimAscii(v___x_1874_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = l_String_Slice_toString(v___x_1875_);
lean_dec_ref(v___x_1875_);
v___x_1877_ = lean_string_append(v___x_1873_, v___x_1876_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = 1;
v___x_1879_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*1, v___x_1878_);
v___x_1880_ = lean_array_push(v_log_1861_, v___x_1879_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1880_);
v___x_1882_ = v___x_1871_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_trace_1864_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_buildTime_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1883_, sizeof(void*)*3, v_action_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1883_, sizeof(void*)*3 + 1, v_wantsRebuild_1863_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v___y_1853_ = v___x_1882_;
goto v___jp_1852_;
}
}
}
else
{
lean_dec_ref(v___y_1867_);
v___y_1853_ = v_a_1859_;
goto v___jp_1852_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_a_1898_; 
lean_dec(v___x_1831_);
v_a_1894_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1894_);
v_a_1895_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1846_);
v___x_1896_ = lean_box(0);
v___x_1897_ = l_Lake_Job_sync___redArg___lam__0(v___x_1833_, v___x_1834_, v___x_1896_, v_a_1895_);
v_a_1898_ = lean_ctor_get(v___x_1897_, 1);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v_a_1824_ = v_a_1894_;
v_a_1825_ = v_a_1898_;
goto v___jp_1823_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec_ref(v_f_1815_);
lean_dec_ref(v_a_1814_);
v_a_1901_ = lean_ctor_get(v_x_1821_, 0);
v_a_1902_ = lean_ctor_get(v_x_1821_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_x_1821_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v_x_1821_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_inc(v_a_1901_);
lean_dec(v_x_1821_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1901_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
v___jp_1823_:
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_a_1824_);
lean_ctor_set(v___x_1826_, 1, v_a_1825_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object* v_a_1910_, lean_object* v_f_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_x_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lake_Job_mapM___redArg___lam__1(v_a_1910_, v_f_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_x_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object* v_kind_1920_, lean_object* v_self_1921_, lean_object* v_f_1922_, lean_object* v_prio_1923_, uint8_t v_sync_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_task_1932_; lean_object* v_caption_1933_; uint8_t v_optional_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1943_; 
v_task_1932_ = lean_ctor_get(v_self_1921_, 0);
v_caption_1933_ = lean_ctor_get(v_self_1921_, 2);
v_optional_1934_ = lean_ctor_get_uint8(v_self_1921_, sizeof(void*)*3);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_self_1921_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v_self_1921_, 1);
lean_dec(v_unused_1944_);
v___x_1936_ = v_self_1921_;
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_caption_1933_);
lean_inc(v_task_1932_);
lean_dec(v_self_1921_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___f_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___f_1938_ = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_1938_, 0, v_a_1930_);
lean_closure_set(v___f_1938_, 1, v_f_1922_);
lean_closure_set(v___f_1938_, 2, v_a_1925_);
lean_closure_set(v___f_1938_, 3, v_a_1926_);
lean_closure_set(v___f_1938_, 4, v_a_1927_);
lean_closure_set(v___f_1938_, 5, v_a_1928_);
lean_closure_set(v___f_1938_, 6, v_a_1929_);
v___x_1939_ = lean_io_map_task(v___f_1938_, v_task_1932_, v_prio_1923_, v_sync_1924_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 1, v_kind_1920_);
lean_ctor_set(v___x_1936_, 0, v___x_1939_);
v___x_1941_ = v___x_1936_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_kind_1920_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_caption_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1942_, sizeof(void*)*3, v_optional_1934_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* v_kind_1945_, lean_object* v_self_1946_, lean_object* v_f_1947_, lean_object* v_prio_1948_, lean_object* v_sync_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
uint8_t v_sync_boxed_1957_; lean_object* v_res_1958_; 
v_sync_boxed_1957_ = lean_unbox(v_sync_1949_);
v_res_1958_ = l_Lake_Job_mapM___redArg(v_kind_1945_, v_self_1946_, v_f_1947_, v_prio_1948_, v_sync_boxed_1957_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object* v_00_u03b2_1959_, lean_object* v_00_u03b1_1960_, lean_object* v_kind_1961_, lean_object* v_self_1962_, lean_object* v_f_1963_, lean_object* v_prio_1964_, uint8_t v_sync_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lake_Job_mapM___redArg(v_kind_1961_, v_self_1962_, v_f_1963_, v_prio_1964_, v_sync_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* v_00_u03b2_1974_, lean_object* v_00_u03b1_1975_, lean_object* v_kind_1976_, lean_object* v_self_1977_, lean_object* v_f_1978_, lean_object* v_prio_1979_, lean_object* v_sync_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
uint8_t v_sync_boxed_1988_; lean_object* v_res_1989_; 
v_sync_boxed_1988_ = lean_unbox(v_sync_1980_);
v_res_1989_ = l_Lake_Job_mapM(v_00_u03b2_1974_, v_00_u03b1_1975_, v_kind_1976_, v_self_1977_, v_f_1978_, v_prio_1979_, v_sync_boxed_1988_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* v_val_1990_, lean_object* v_val_1991_, lean_object* v_a_x3f_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = lean_get_set_stdout(v_val_1990_);
lean_dec_ref(v___x_1995_);
v___x_1996_ = lean_get_set_stderr(v_val_1991_);
lean_dec_ref(v___x_1996_);
v___x_1997_ = lean_box(0);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v___y_1993_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0___boxed(lean_object* v_val_1999_, lean_object* v_val_2000_, lean_object* v_a_x3f_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lake_Job_bindM___redArg___lam__0(v_val_1999_, v_val_2000_, v_a_x3f_2001_, v___y_2002_);
lean_dec(v_a_x3f_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* v_a_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2030_; 
v_a_2007_ = lean_ctor_get(v_x_2006_, 0);
v_a_2008_ = lean_ctor_get(v_x_2006_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2010_ = v_x_2006_;
v_isShared_2011_ = v_isSharedCheck_2030_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_inc(v_a_2007_);
lean_dec(v_x_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2030_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v_log_2013_; uint8_t v_action_2014_; uint8_t v_wantsRebuild_2015_; lean_object* v_buildTime_2016_; lean_object* v_trace_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2027_; 
lean_inc(v_a_2008_);
v___x_2012_ = l_Lake_JobState_merge(v_a_2005_, v_a_2008_);
v_log_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_ref(v_log_2013_);
v_action_2014_ = lean_ctor_get_uint8(v___x_2012_, sizeof(void*)*3);
v_wantsRebuild_2015_ = lean_ctor_get_uint8(v___x_2012_, sizeof(void*)*3 + 1);
v_buildTime_2016_ = lean_ctor_get(v___x_2012_, 2);
lean_inc(v_buildTime_2016_);
lean_dec_ref(v___x_2012_);
v_trace_2017_ = lean_ctor_get(v_a_2008_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_a_2008_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; lean_object* v_unused_2029_; 
v_unused_2028_ = lean_ctor_get(v_a_2008_, 2);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_a_2008_, 0);
lean_dec(v_unused_2029_);
v___x_2019_ = v_a_2008_;
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_trace_2017_);
lean_dec(v_a_2008_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 2, v_buildTime_2016_);
lean_ctor_set(v___x_2019_, 0, v_log_2013_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_log_2013_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_trace_2017_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_buildTime_2016_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*3, v_action_2014_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*3 + 1, v_wantsRebuild_2015_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2022_);
v___x_2024_ = v___x_2010_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2007_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2057_; 
v_a_2031_ = lean_ctor_get(v_x_2006_, 0);
v_a_2032_ = lean_ctor_get(v_x_2006_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2034_ = v_x_2006_;
v_isShared_2035_ = v_isSharedCheck_2057_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_inc(v_a_2031_);
lean_dec(v_x_2006_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2057_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_log_2036_; lean_object* v___x_2037_; lean_object* v_log_2038_; uint8_t v_action_2039_; uint8_t v_wantsRebuild_2040_; lean_object* v_buildTime_2041_; lean_object* v_trace_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2054_; 
v_log_2036_ = lean_ctor_get(v_a_2005_, 0);
lean_inc_ref(v_log_2036_);
lean_inc(v_a_2032_);
v___x_2037_ = l_Lake_JobState_merge(v_a_2005_, v_a_2032_);
v_log_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref(v_log_2038_);
v_action_2039_ = lean_ctor_get_uint8(v___x_2037_, sizeof(void*)*3);
v_wantsRebuild_2040_ = lean_ctor_get_uint8(v___x_2037_, sizeof(void*)*3 + 1);
v_buildTime_2041_ = lean_ctor_get(v___x_2037_, 2);
lean_inc(v_buildTime_2041_);
lean_dec_ref(v___x_2037_);
v_trace_2042_ = lean_ctor_get(v_a_2032_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_a_2032_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2055_ = lean_ctor_get(v_a_2032_, 2);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_a_2032_, 0);
lean_dec(v_unused_2056_);
v___x_2044_ = v_a_2032_;
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_trace_2042_);
lean_dec(v_a_2032_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2046_ = lean_array_get_size(v_log_2036_);
lean_dec_ref(v_log_2036_);
v___x_2047_ = lean_nat_add(v___x_2046_, v_a_2031_);
lean_dec(v_a_2031_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 2, v_buildTime_2041_);
lean_ctor_set(v___x_2044_, 0, v_log_2038_);
v___x_2049_ = v___x_2044_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_log_2038_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_trace_2042_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_buildTime_2041_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*3, v_action_2039_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*3 + 1, v_wantsRebuild_2040_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v___x_2049_);
lean_ctor_set(v___x_2034_, 0, v___x_2047_);
v___x_2051_ = v___x_2034_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* v_a_2058_, lean_object* v_____r_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v_a_2058_);
lean_ctor_set(v___x_2067_, 1, v___y_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object* v_a_2068_, lean_object* v_____r_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2068_, v_____r_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2078_, lean_object* v_f_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_prio_2085_, lean_object* v_x_2086_){
_start:
{
lean_object* v_a_2089_; lean_object* v_a_2090_; lean_object* v___y_2094_; 
if (lean_obj_tag(v_x_2086_) == 0)
{
lean_object* v_a_2103_; lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v_log_2111_; uint8_t v_action_2112_; uint8_t v_wantsRebuild_2113_; lean_object* v_trace_2114_; lean_object* v_buildTime_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2171_; 
v_a_2103_ = lean_ctor_get(v_x_2086_, 0);
lean_inc(v_a_2103_);
v_a_2104_ = lean_ctor_get(v_x_2086_, 1);
lean_inc(v_a_2104_);
lean_dec_ref(v_x_2086_);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2107_ = lean_st_mk_ref(v___x_2106_);
lean_inc(v___x_2107_);
v___x_2108_ = l_IO_FS_Stream_ofBuffer(v___x_2107_);
lean_inc_ref(v___x_2108_);
v___x_2109_ = lean_get_set_stdout(v___x_2108_);
v___x_2110_ = lean_get_set_stderr(v___x_2108_);
v_log_2111_ = lean_ctor_get(v_a_2104_, 0);
v_action_2112_ = lean_ctor_get_uint8(v_a_2104_, sizeof(void*)*3);
v_wantsRebuild_2113_ = lean_ctor_get_uint8(v_a_2104_, sizeof(void*)*3 + 1);
v_trace_2114_ = lean_ctor_get(v_a_2104_, 1);
v_buildTime_2115_ = lean_ctor_get(v_a_2104_, 2);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_a_2104_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2117_ = v_a_2104_;
v_isShared_2118_ = v_isSharedCheck_2171_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_buildTime_2115_);
lean_inc(v_trace_2114_);
lean_inc(v_log_2111_);
lean_dec(v_a_2104_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2171_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_trace_2119_; lean_object* v___x_2121_; 
v_trace_2119_ = l_Lake_BuildTrace_mix(v_a_2078_, v_trace_2114_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v_trace_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_log_2111_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_trace_2119_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_buildTime_2115_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*3, v_action_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*3 + 1, v_wantsRebuild_2113_);
v___x_2121_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; 
lean_inc_ref(v_a_2084_);
lean_inc(v_a_2083_);
lean_inc(v_a_2082_);
lean_inc(v_a_2081_);
lean_inc_ref(v_a_2080_);
v___x_2122_ = lean_apply_8(v_f_2079_, v_a_2103_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v___x_2121_, lean_box(0));
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v_log_2129_; uint8_t v_action_2130_; uint8_t v_wantsRebuild_2131_; lean_object* v_trace_2132_; lean_object* v_buildTime_2133_; lean_object* v_data_2134_; lean_object* v___y_2136_; uint8_t v___x_2161_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
v_a_2124_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2122_);
lean_inc(v_a_2123_);
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_a_2123_);
v___x_2126_ = l_Lake_Job_bindM___redArg___lam__0(v___x_2109_, v___x_2110_, v___x_2125_, v_a_2124_);
lean_dec_ref(v___x_2125_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 1);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = lean_st_ref_get(v___x_2107_);
lean_dec(v___x_2107_);
v_log_2129_ = lean_ctor_get(v_a_2127_, 0);
v_action_2130_ = lean_ctor_get_uint8(v_a_2127_, sizeof(void*)*3);
v_wantsRebuild_2131_ = lean_ctor_get_uint8(v_a_2127_, sizeof(void*)*3 + 1);
v_trace_2132_ = lean_ctor_get(v_a_2127_, 1);
v_buildTime_2133_ = lean_ctor_get(v_a_2127_, 2);
v_data_2134_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_ref(v_data_2134_);
lean_dec(v___x_2128_);
v___x_2161_ = lean_string_validate_utf8(v_data_2134_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v_data_2134_);
v___x_2162_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2163_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2162_);
v___y_2136_ = v___x_2163_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_string_from_utf8_unchecked(v_data_2134_);
v___y_2136_ = v___x_2164_;
goto v___jp_2135_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = lean_string_utf8_byte_size(v___y_2136_);
v___x_2138_ = lean_nat_dec_eq(v___x_2137_, v___x_2105_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2155_; 
lean_inc(v_buildTime_2133_);
lean_inc_ref(v_trace_2132_);
lean_inc_ref(v_log_2129_);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2156_ = lean_ctor_get(v_a_2127_, 2);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_a_2127_, 1);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_a_2127_, 0);
lean_dec(v_unused_2158_);
v___x_2140_ = v_a_2127_;
v_isShared_2141_ = v_isSharedCheck_2155_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v_a_2127_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2155_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2142_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2143_, 0, v___y_2136_);
lean_ctor_set(v___x_2143_, 1, v___x_2105_);
lean_ctor_set(v___x_2143_, 2, v___x_2137_);
v___x_2144_ = l_String_Slice_trimAscii(v___x_2143_);
lean_dec_ref(v___x_2143_);
v___x_2145_ = l_String_Slice_toString(v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = lean_string_append(v___x_2142_, v___x_2145_);
lean_dec_ref(v___x_2145_);
v___x_2147_ = 1;
v___x_2148_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*1, v___x_2147_);
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_array_push(v_log_2129_, v___x_2148_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2150_);
v___x_2152_ = v___x_2140_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_trace_2132_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_buildTime_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*3, v_action_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*3 + 1, v_wantsRebuild_2131_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2123_, v___x_2149_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v___x_2152_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
v___y_2094_ = v___x_2153_;
goto v___jp_2093_;
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v___y_2136_);
v___x_2159_ = lean_box(0);
v___x_2160_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2123_, v___x_2159_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2127_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
v___y_2094_ = v___x_2160_;
goto v___jp_2093_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v_a_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_a_2169_; 
lean_dec(v___x_2107_);
lean_dec(v_prio_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
v_a_2165_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2165_);
v_a_2166_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2122_);
v___x_2167_ = lean_box(0);
v___x_2168_ = l_Lake_Job_bindM___redArg___lam__0(v___x_2109_, v___x_2110_, v___x_2167_, v_a_2166_);
v_a_2169_ = lean_ctor_get(v___x_2168_, 1);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
v_a_2089_ = v_a_2165_;
v_a_2090_ = v_a_2169_;
goto v___jp_2088_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_prio_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec_ref(v_f_2079_);
lean_dec_ref(v_a_2078_);
v_a_2172_ = lean_ctor_get(v_x_2086_, 0);
v_a_2173_ = lean_ctor_get(v_x_2086_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_x_2086_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2175_ = v_x_2086_;
v_isShared_2176_ = v_isSharedCheck_2181_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_inc(v_a_2172_);
lean_dec(v_x_2086_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2181_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2172_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_task_pure(v___x_2178_);
return v___x_2179_;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_a_2089_);
lean_ctor_set(v___x_2091_, 1, v_a_2090_);
v___x_2092_ = lean_task_pure(v___x_2091_);
return v___x_2092_;
}
v___jp_2093_:
{
if (lean_obj_tag(v___y_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v_a_2096_; lean_object* v_task_2097_; lean_object* v___f_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; 
v_a_2095_ = lean_ctor_get(v___y_2094_, 0);
lean_inc(v_a_2095_);
v_a_2096_ = lean_ctor_get(v___y_2094_, 1);
lean_inc(v_a_2096_);
lean_dec_ref(v___y_2094_);
v_task_2097_ = lean_ctor_get(v_a_2095_, 0);
lean_inc_ref(v_task_2097_);
lean_dec(v_a_2095_);
v___f_2098_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2098_, 0, v_a_2096_);
v___x_2099_ = 1;
v___x_2100_ = lean_task_map(v___f_2098_, v_task_2097_, v_prio_2085_, v___x_2099_);
return v___x_2100_;
}
else
{
lean_object* v_a_2101_; lean_object* v_a_2102_; 
lean_dec(v_prio_2085_);
v_a_2101_ = lean_ctor_get(v___y_2094_, 0);
lean_inc(v_a_2101_);
v_a_2102_ = lean_ctor_get(v___y_2094_, 1);
lean_inc(v_a_2102_);
lean_dec_ref(v___y_2094_);
v_a_2089_ = v_a_2101_;
v_a_2090_ = v_a_2102_;
goto v___jp_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object* v_a_2182_, lean_object* v_f_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_prio_2189_, lean_object* v_x_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2182_, v_f_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_prio_2189_, v_x_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object* v_kind_2193_, lean_object* v_self_2194_, lean_object* v_f_2195_, lean_object* v_prio_2196_, uint8_t v_sync_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_task_2205_; lean_object* v_caption_2206_; uint8_t v_optional_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2216_; 
v_task_2205_ = lean_ctor_get(v_self_2194_, 0);
v_caption_2206_ = lean_ctor_get(v_self_2194_, 2);
v_optional_2207_ = lean_ctor_get_uint8(v_self_2194_, sizeof(void*)*3);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_self_2194_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v_self_2194_, 1);
lean_dec(v_unused_2217_);
v___x_2209_ = v_self_2194_;
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_caption_2206_);
lean_inc(v_task_2205_);
lean_dec(v_self_2194_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_inc(v_prio_2196_);
v___f_2211_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2211_, 0, v_a_2203_);
lean_closure_set(v___f_2211_, 1, v_f_2195_);
lean_closure_set(v___f_2211_, 2, v_a_2198_);
lean_closure_set(v___f_2211_, 3, v_a_2199_);
lean_closure_set(v___f_2211_, 4, v_a_2200_);
lean_closure_set(v___f_2211_, 5, v_a_2201_);
lean_closure_set(v___f_2211_, 6, v_a_2202_);
lean_closure_set(v___f_2211_, 7, v_prio_2196_);
v___x_2212_ = lean_io_bind_task(v_task_2205_, v___f_2211_, v_prio_2196_, v_sync_2197_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v_kind_2193_);
lean_ctor_set(v___x_2209_, 0, v___x_2212_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_kind_2193_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_caption_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*3, v_optional_2207_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* v_kind_2218_, lean_object* v_self_2219_, lean_object* v_f_2220_, lean_object* v_prio_2221_, lean_object* v_sync_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
uint8_t v_sync_boxed_2230_; lean_object* v_res_2231_; 
v_sync_boxed_2230_ = lean_unbox(v_sync_2222_);
v_res_2231_ = l_Lake_Job_bindM___redArg(v_kind_2218_, v_self_2219_, v_f_2220_, v_prio_2221_, v_sync_boxed_2230_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object* v_00_u03b2_2232_, lean_object* v_00_u03b1_2233_, lean_object* v_kind_2234_, lean_object* v_self_2235_, lean_object* v_f_2236_, lean_object* v_prio_2237_, uint8_t v_sync_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lake_Job_bindM___redArg(v_kind_2234_, v_self_2235_, v_f_2236_, v_prio_2237_, v_sync_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* v_00_u03b2_2247_, lean_object* v_00_u03b1_2248_, lean_object* v_kind_2249_, lean_object* v_self_2250_, lean_object* v_f_2251_, lean_object* v_prio_2252_, lean_object* v_sync_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
uint8_t v_sync_boxed_2261_; lean_object* v_res_2262_; 
v_sync_boxed_2261_ = lean_unbox(v_sync_2253_);
v_res_2262_ = l_Lake_Job_bindM(v_00_u03b2_2247_, v_00_u03b1_2248_, v_kind_2249_, v_self_2250_, v_f_2251_, v_prio_2252_, v_sync_boxed_2261_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* v_f_2263_, lean_object* v_rx_2264_, lean_object* v_ry_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_apply_2(v_f_2263_, v_rx_2264_, v_ry_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* v_other_2267_, lean_object* v_f_2268_, lean_object* v_prio_2269_, uint8_t v_sync_2270_, lean_object* v_rx_2271_){
_start:
{
lean_object* v_task_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; 
v_task_2272_ = lean_ctor_get(v_other_2267_, 0);
lean_inc_ref(v_task_2272_);
lean_dec_ref(v_other_2267_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2273_, 0, v_f_2268_);
lean_closure_set(v___f_2273_, 1, v_rx_2271_);
v___x_2274_ = lean_task_map(v___f_2273_, v_task_2272_, v_prio_2269_, v_sync_2270_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* v_other_2275_, lean_object* v_f_2276_, lean_object* v_prio_2277_, lean_object* v_sync_2278_, lean_object* v_rx_2279_){
_start:
{
uint8_t v_sync_boxed_2280_; lean_object* v_res_2281_; 
v_sync_boxed_2280_ = lean_unbox(v_sync_2278_);
v_res_2281_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2275_, v_f_2276_, v_prio_2277_, v_sync_boxed_2280_, v_rx_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* v_inst_2282_, lean_object* v_f_2283_, lean_object* v_self_2284_, lean_object* v_other_2285_, lean_object* v_prio_2286_, uint8_t v_sync_2287_){
_start:
{
lean_object* v_task_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2301_; 
v_task_2288_ = lean_ctor_get(v_self_2284_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_self_2284_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; lean_object* v_unused_2303_; 
v_unused_2302_ = lean_ctor_get(v_self_2284_, 2);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_self_2284_, 1);
lean_dec(v_unused_2303_);
v___x_2290_ = v_self_2284_;
v_isShared_2291_ = v_isSharedCheck_2301_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_task_2288_);
lean_dec(v_self_2284_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2301_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___f_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2299_; 
v___x_2292_ = lean_box(v_sync_2287_);
lean_inc(v_prio_2286_);
v___f_2293_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2293_, 0, v_other_2285_);
lean_closure_set(v___f_2293_, 1, v_f_2283_);
lean_closure_set(v___f_2293_, 2, v_prio_2286_);
lean_closure_set(v___f_2293_, 3, v___x_2292_);
v___x_2294_ = 1;
v___x_2295_ = lean_task_bind(v_task_2288_, v___f_2293_, v_prio_2286_, v___x_2294_);
v___x_2296_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2297_ = 0;
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 2, v___x_2296_);
lean_ctor_set(v___x_2290_, 1, v_inst_2282_);
lean_ctor_set(v___x_2290_, 0, v___x_2295_);
v___x_2299_ = v___x_2290_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_inst_2282_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v___x_2296_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*3, v___x_2297_);
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* v_inst_2304_, lean_object* v_f_2305_, lean_object* v_self_2306_, lean_object* v_other_2307_, lean_object* v_prio_2308_, lean_object* v_sync_2309_){
_start:
{
uint8_t v_sync_boxed_2310_; lean_object* v_res_2311_; 
v_sync_boxed_2310_ = lean_unbox(v_sync_2309_);
v_res_2311_ = l_Lake_Job_zipResultWith___redArg(v_inst_2304_, v_f_2305_, v_self_2306_, v_other_2307_, v_prio_2308_, v_sync_boxed_2310_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object* v_00_u03b3_2312_, lean_object* v_00_u03b1_2313_, lean_object* v_00_u03b2_2314_, lean_object* v_inst_2315_, lean_object* v_f_2316_, lean_object* v_self_2317_, lean_object* v_other_2318_, lean_object* v_prio_2319_, uint8_t v_sync_2320_){
_start:
{
lean_object* v_task_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2334_; 
v_task_2321_ = lean_ctor_get(v_self_2317_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_self_2317_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; lean_object* v_unused_2336_; 
v_unused_2335_ = lean_ctor_get(v_self_2317_, 2);
lean_dec(v_unused_2335_);
v_unused_2336_ = lean_ctor_get(v_self_2317_, 1);
lean_dec(v_unused_2336_);
v___x_2323_ = v_self_2317_;
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_task_2321_);
lean_dec(v_self_2317_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___f_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2332_; 
v___x_2325_ = lean_box(v_sync_2320_);
lean_inc(v_prio_2319_);
v___f_2326_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2326_, 0, v_other_2318_);
lean_closure_set(v___f_2326_, 1, v_f_2316_);
lean_closure_set(v___f_2326_, 2, v_prio_2319_);
lean_closure_set(v___f_2326_, 3, v___x_2325_);
v___x_2327_ = 1;
v___x_2328_ = lean_task_bind(v_task_2321_, v___f_2326_, v_prio_2319_, v___x_2327_);
v___x_2329_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2330_ = 0;
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 2, v___x_2329_);
lean_ctor_set(v___x_2323_, 1, v_inst_2315_);
lean_ctor_set(v___x_2323_, 0, v___x_2328_);
v___x_2332_ = v___x_2323_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_inst_2315_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v___x_2329_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*3, v___x_2330_);
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* v_00_u03b3_2337_, lean_object* v_00_u03b1_2338_, lean_object* v_00_u03b2_2339_, lean_object* v_inst_2340_, lean_object* v_f_2341_, lean_object* v_self_2342_, lean_object* v_other_2343_, lean_object* v_prio_2344_, lean_object* v_sync_2345_){
_start:
{
uint8_t v_sync_boxed_2346_; lean_object* v_res_2347_; 
v_sync_boxed_2346_ = lean_unbox(v_sync_2345_);
v_res_2347_ = l_Lake_Job_zipResultWith(v_00_u03b3_2337_, v_00_u03b1_2338_, v_00_u03b2_2339_, v_inst_2340_, v_f_2341_, v_self_2342_, v_other_2343_, v_prio_2344_, v_sync_boxed_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* v_rx_2348_, lean_object* v_f_2349_, lean_object* v_ry_2350_){
_start:
{
lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v_a_2363_; 
if (lean_obj_tag(v_rx_2348_) == 0)
{
if (lean_obj_tag(v_ry_2350_) == 0)
{
lean_object* v_a_2365_; lean_object* v_a_2366_; lean_object* v_a_2367_; lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2377_; 
v_a_2365_ = lean_ctor_get(v_rx_2348_, 0);
lean_inc(v_a_2365_);
v_a_2366_ = lean_ctor_get(v_rx_2348_, 1);
lean_inc(v_a_2366_);
lean_dec_ref(v_rx_2348_);
v_a_2367_ = lean_ctor_get(v_ry_2350_, 0);
v_a_2368_ = lean_ctor_get(v_ry_2350_, 1);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_ry_2350_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2370_ = v_ry_2350_;
v_isShared_2371_ = v_isSharedCheck_2377_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_inc(v_a_2367_);
lean_dec(v_ry_2350_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2377_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2372_ = lean_apply_2(v_f_2349_, v_a_2365_, v_a_2367_);
v___x_2373_ = l_Lake_JobState_merge(v_a_2366_, v_a_2368_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___x_2373_);
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2378_; 
lean_dec(v_f_2349_);
v_a_2378_ = lean_ctor_get(v_rx_2348_, 1);
lean_inc(v_a_2378_);
lean_dec_ref(v_rx_2348_);
v_a_2363_ = v_a_2378_;
goto v___jp_2362_;
}
}
else
{
lean_dec(v_f_2349_);
if (lean_obj_tag(v_rx_2348_) == 0)
{
lean_object* v_a_2379_; 
v_a_2379_ = lean_ctor_get(v_rx_2348_, 1);
lean_inc(v_a_2379_);
lean_dec_ref(v_rx_2348_);
v_a_2363_ = v_a_2379_;
goto v___jp_2362_;
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2381_; 
v_a_2380_ = lean_ctor_get(v_rx_2348_, 1);
lean_inc(v_a_2380_);
lean_dec_ref(v_rx_2348_);
v___x_2381_ = lean_unsigned_to_nat(0u);
v___y_2358_ = v_ry_2350_;
v___y_2359_ = v___x_2381_;
v___y_2360_ = v_a_2380_;
goto v___jp_2357_;
}
}
v___jp_2351_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = l_Lake_JobState_merge(v___y_2353_, v___y_2354_);
v___x_2356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___y_2352_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
return v___x_2356_;
}
v___jp_2357_:
{
lean_object* v_a_2361_; 
v_a_2361_ = lean_ctor_get(v___y_2358_, 1);
lean_inc(v_a_2361_);
lean_dec_ref(v___y_2358_);
v___y_2352_ = v___y_2359_;
v___y_2353_ = v___y_2360_;
v___y_2354_ = v_a_2361_;
goto v___jp_2351_;
}
v___jp_2362_:
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_unsigned_to_nat(0u);
v___y_2358_ = v_ry_2350_;
v___y_2359_ = v___x_2364_;
v___y_2360_ = v_a_2363_;
goto v___jp_2357_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* v_other_2382_, lean_object* v_f_2383_, lean_object* v_prio_2384_, uint8_t v_sync_2385_, lean_object* v_rx_2386_){
_start:
{
lean_object* v_task_2387_; lean_object* v___f_2388_; lean_object* v___x_2389_; 
v_task_2387_ = lean_ctor_get(v_other_2382_, 0);
lean_inc_ref(v_task_2387_);
lean_dec_ref(v_other_2382_);
v___f_2388_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2388_, 0, v_rx_2386_);
lean_closure_set(v___f_2388_, 1, v_f_2383_);
v___x_2389_ = lean_task_map(v___f_2388_, v_task_2387_, v_prio_2384_, v_sync_2385_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* v_other_2390_, lean_object* v_f_2391_, lean_object* v_prio_2392_, lean_object* v_sync_2393_, lean_object* v_rx_2394_){
_start:
{
uint8_t v_sync_boxed_2395_; lean_object* v_res_2396_; 
v_sync_boxed_2395_ = lean_unbox(v_sync_2393_);
v_res_2396_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2390_, v_f_2391_, v_prio_2392_, v_sync_boxed_2395_, v_rx_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object* v_inst_2397_, lean_object* v_f_2398_, lean_object* v_self_2399_, lean_object* v_other_2400_, lean_object* v_prio_2401_, uint8_t v_sync_2402_){
_start:
{
lean_object* v_task_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2416_; 
v_task_2403_ = lean_ctor_get(v_self_2399_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_self_2399_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2417_ = lean_ctor_get(v_self_2399_, 2);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_self_2399_, 1);
lean_dec(v_unused_2418_);
v___x_2405_ = v_self_2399_;
v_isShared_2406_ = v_isSharedCheck_2416_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_task_2403_);
lean_dec(v_self_2399_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2416_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___f_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2414_; 
v___x_2407_ = lean_box(v_sync_2402_);
lean_inc(v_prio_2401_);
v___f_2408_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2408_, 0, v_other_2400_);
lean_closure_set(v___f_2408_, 1, v_f_2398_);
lean_closure_set(v___f_2408_, 2, v_prio_2401_);
lean_closure_set(v___f_2408_, 3, v___x_2407_);
v___x_2409_ = 1;
v___x_2410_ = lean_task_bind(v_task_2403_, v___f_2408_, v_prio_2401_, v___x_2409_);
v___x_2411_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2412_ = 0;
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 2, v___x_2411_);
lean_ctor_set(v___x_2405_, 1, v_inst_2397_);
lean_ctor_set(v___x_2405_, 0, v___x_2410_);
v___x_2414_ = v___x_2405_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_inst_2397_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v___x_2411_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_ctor_set_uint8(v___x_2414_, sizeof(void*)*3, v___x_2412_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* v_inst_2419_, lean_object* v_f_2420_, lean_object* v_self_2421_, lean_object* v_other_2422_, lean_object* v_prio_2423_, lean_object* v_sync_2424_){
_start:
{
uint8_t v_sync_boxed_2425_; lean_object* v_res_2426_; 
v_sync_boxed_2425_ = lean_unbox(v_sync_2424_);
v_res_2426_ = l_Lake_Job_zipWith___redArg(v_inst_2419_, v_f_2420_, v_self_2421_, v_other_2422_, v_prio_2423_, v_sync_boxed_2425_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object* v_rx_2427_, lean_object* v_f_2428_, lean_object* v_ry_2429_){
_start:
{
lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v_a_2442_; lean_object* v_rb_2443_; 
if (lean_obj_tag(v_rx_2427_) == 0)
{
if (lean_obj_tag(v_ry_2429_) == 0)
{
lean_object* v_a_2445_; lean_object* v_a_2446_; lean_object* v_a_2447_; lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2457_; 
v_a_2445_ = lean_ctor_get(v_rx_2427_, 0);
lean_inc(v_a_2445_);
v_a_2446_ = lean_ctor_get(v_rx_2427_, 1);
lean_inc(v_a_2446_);
lean_dec_ref(v_rx_2427_);
v_a_2447_ = lean_ctor_get(v_ry_2429_, 0);
v_a_2448_ = lean_ctor_get(v_ry_2429_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_ry_2429_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2450_ = v_ry_2429_;
v_isShared_2451_ = v_isSharedCheck_2457_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_inc(v_a_2447_);
lean_dec(v_ry_2429_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2457_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2452_ = lean_apply_2(v_f_2428_, v_a_2445_, v_a_2447_);
v___x_2453_ = l_Lake_JobState_merge(v_a_2446_, v_a_2448_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2453_);
lean_ctor_set(v___x_2450_, 0, v___x_2452_);
v___x_2455_ = v___x_2450_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_object* v_a_2458_; 
lean_dec(v_f_2428_);
v_a_2458_ = lean_ctor_get(v_rx_2427_, 1);
lean_inc(v_a_2458_);
lean_dec_ref(v_rx_2427_);
v_a_2442_ = v_a_2458_;
v_rb_2443_ = v_ry_2429_;
goto v___jp_2441_;
}
}
else
{
lean_dec(v_f_2428_);
if (lean_obj_tag(v_rx_2427_) == 0)
{
lean_object* v_a_2459_; 
v_a_2459_ = lean_ctor_get(v_rx_2427_, 1);
lean_inc(v_a_2459_);
lean_dec_ref(v_rx_2427_);
v_a_2442_ = v_a_2459_;
v_rb_2443_ = v_ry_2429_;
goto v___jp_2441_;
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2461_; 
v_a_2460_ = lean_ctor_get(v_rx_2427_, 1);
lean_inc(v_a_2460_);
lean_dec_ref(v_rx_2427_);
v___x_2461_ = lean_unsigned_to_nat(0u);
v___y_2437_ = v_ry_2429_;
v___y_2438_ = v___x_2461_;
v___y_2439_ = v_a_2460_;
goto v___jp_2436_;
}
}
v___jp_2430_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = l_Lake_JobState_merge(v___y_2432_, v___y_2433_);
v___x_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___y_2431_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
return v___x_2435_;
}
v___jp_2436_:
{
lean_object* v_a_2440_; 
v_a_2440_ = lean_ctor_get(v___y_2437_, 1);
lean_inc(v_a_2440_);
lean_dec_ref(v___y_2437_);
v___y_2431_ = v___y_2438_;
v___y_2432_ = v___y_2439_;
v___y_2433_ = v_a_2440_;
goto v___jp_2430_;
}
v___jp_2441_:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_unsigned_to_nat(0u);
v___y_2437_ = v_rb_2443_;
v___y_2438_ = v___x_2444_;
v___y_2439_ = v_a_2442_;
goto v___jp_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1(lean_object* v_other_2462_, lean_object* v_f_2463_, lean_object* v_prio_2464_, uint8_t v_sync_2465_, lean_object* v_rx_2466_){
_start:
{
lean_object* v_task_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; 
v_task_2467_ = lean_ctor_get(v_other_2462_, 0);
lean_inc_ref(v_task_2467_);
lean_dec_ref(v_other_2462_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__0), 3, 2);
lean_closure_set(v___f_2468_, 0, v_rx_2466_);
lean_closure_set(v___f_2468_, 1, v_f_2463_);
v___x_2469_ = lean_task_map(v___f_2468_, v_task_2467_, v_prio_2464_, v_sync_2465_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object* v_other_2470_, lean_object* v_f_2471_, lean_object* v_prio_2472_, lean_object* v_sync_2473_, lean_object* v_rx_2474_){
_start:
{
uint8_t v_sync_boxed_2475_; lean_object* v_res_2476_; 
v_sync_boxed_2475_ = lean_unbox(v_sync_2473_);
v_res_2476_ = l_Lake_Job_zipWith___lam__1(v_other_2470_, v_f_2471_, v_prio_2472_, v_sync_boxed_2475_, v_rx_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object* v_00_u03b3_2477_, lean_object* v_00_u03b1_2478_, lean_object* v_00_u03b2_2479_, lean_object* v_inst_2480_, lean_object* v_f_2481_, lean_object* v_self_2482_, lean_object* v_other_2483_, lean_object* v_prio_2484_, uint8_t v_sync_2485_){
_start:
{
lean_object* v_task_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2499_; 
v_task_2486_ = lean_ctor_get(v_self_2482_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_self_2482_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; lean_object* v_unused_2501_; 
v_unused_2500_ = lean_ctor_get(v_self_2482_, 2);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_self_2482_, 1);
lean_dec(v_unused_2501_);
v___x_2488_ = v_self_2482_;
v_isShared_2489_ = v_isSharedCheck_2499_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_task_2486_);
lean_dec(v_self_2482_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2499_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___f_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2497_; 
v___x_2490_ = lean_box(v_sync_2485_);
lean_inc(v_prio_2484_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2491_, 0, v_other_2483_);
lean_closure_set(v___f_2491_, 1, v_f_2481_);
lean_closure_set(v___f_2491_, 2, v_prio_2484_);
lean_closure_set(v___f_2491_, 3, v___x_2490_);
v___x_2492_ = 1;
v___x_2493_ = lean_task_bind(v_task_2486_, v___f_2491_, v_prio_2484_, v___x_2492_);
v___x_2494_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2495_ = 0;
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 2, v___x_2494_);
lean_ctor_set(v___x_2488_, 1, v_inst_2480_);
lean_ctor_set(v___x_2488_, 0, v___x_2493_);
v___x_2497_ = v___x_2488_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_inst_2480_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v___x_2494_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*3, v___x_2495_);
return v___x_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* v_00_u03b3_2502_, lean_object* v_00_u03b1_2503_, lean_object* v_00_u03b2_2504_, lean_object* v_inst_2505_, lean_object* v_f_2506_, lean_object* v_self_2507_, lean_object* v_other_2508_, lean_object* v_prio_2509_, lean_object* v_sync_2510_){
_start:
{
uint8_t v_sync_boxed_2511_; lean_object* v_res_2512_; 
v_sync_boxed_2511_ = lean_unbox(v_sync_2510_);
v_res_2512_ = l_Lake_Job_zipWith(v_00_u03b3_2502_, v_00_u03b1_2503_, v_00_u03b2_2504_, v_inst_2505_, v_f_2506_, v_self_2507_, v_other_2508_, v_prio_2509_, v_sync_boxed_2511_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* v___x_2513_, lean_object* v_rx_2514_, lean_object* v_ry_2515_){
_start:
{
lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2536_; lean_object* v___y_2537_; 
if (lean_obj_tag(v_rx_2514_) == 0)
{
if (lean_obj_tag(v_ry_2515_) == 0)
{
lean_object* v_a_2539_; lean_object* v_a_2540_; lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v___x_2513_);
v_a_2539_ = lean_ctor_get(v_rx_2514_, 0);
lean_inc(v_a_2539_);
v_a_2540_ = lean_ctor_get(v_rx_2514_, 1);
lean_inc(v_a_2540_);
lean_dec_ref(v_rx_2514_);
v_a_2541_ = lean_ctor_get(v_ry_2515_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_ry_2515_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v_ry_2515_, 0);
lean_dec(v_unused_2564_);
v___x_2543_ = v_ry_2515_;
v_isShared_2544_ = v_isSharedCheck_2563_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v_ry_2515_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2563_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v_log_2546_; uint8_t v_action_2547_; uint8_t v_wantsRebuild_2548_; lean_object* v_buildTime_2549_; lean_object* v_trace_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2560_; 
lean_inc(v_a_2540_);
v___x_2545_ = l_Lake_JobState_merge(v_a_2540_, v_a_2541_);
v_log_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc_ref(v_log_2546_);
v_action_2547_ = lean_ctor_get_uint8(v___x_2545_, sizeof(void*)*3);
v_wantsRebuild_2548_ = lean_ctor_get_uint8(v___x_2545_, sizeof(void*)*3 + 1);
v_buildTime_2549_ = lean_ctor_get(v___x_2545_, 2);
lean_inc(v_buildTime_2549_);
lean_dec_ref(v___x_2545_);
v_trace_2550_ = lean_ctor_get(v_a_2540_, 1);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2540_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; lean_object* v_unused_2562_; 
v_unused_2561_ = lean_ctor_get(v_a_2540_, 2);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_a_2540_, 0);
lean_dec(v_unused_2562_);
v___x_2552_ = v_a_2540_;
v_isShared_2553_ = v_isSharedCheck_2560_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_trace_2550_);
lean_dec(v_a_2540_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2560_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 2, v_buildTime_2549_);
lean_ctor_set(v___x_2552_, 0, v_log_2546_);
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_log_2546_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_trace_2550_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_buildTime_2549_);
v___x_2555_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*3, v_action_2547_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*3 + 1, v_wantsRebuild_2548_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v___x_2555_);
lean_ctor_set(v___x_2543_, 0, v_a_2539_);
v___x_2557_ = v___x_2543_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2539_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
else
{
lean_object* v_a_2565_; 
v_a_2565_ = lean_ctor_get(v_rx_2514_, 1);
lean_inc(v_a_2565_);
lean_dec_ref(v_rx_2514_);
v___y_2536_ = v_ry_2515_;
v___y_2537_ = v_a_2565_;
goto v___jp_2535_;
}
}
else
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v_rx_2514_, 1);
lean_inc(v_a_2566_);
lean_dec_ref(v_rx_2514_);
v___y_2536_ = v_ry_2515_;
v___y_2537_ = v_a_2566_;
goto v___jp_2535_;
}
v___jp_2516_:
{
lean_object* v___x_2519_; lean_object* v_log_2520_; uint8_t v_action_2521_; uint8_t v_wantsRebuild_2522_; lean_object* v_buildTime_2523_; lean_object* v_trace_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
lean_inc_ref(v___y_2517_);
v___x_2519_ = l_Lake_JobState_merge(v___y_2517_, v___y_2518_);
v_log_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_log_2520_);
v_action_2521_ = lean_ctor_get_uint8(v___x_2519_, sizeof(void*)*3);
v_wantsRebuild_2522_ = lean_ctor_get_uint8(v___x_2519_, sizeof(void*)*3 + 1);
v_buildTime_2523_ = lean_ctor_get(v___x_2519_, 2);
lean_inc(v_buildTime_2523_);
lean_dec_ref(v___x_2519_);
v_trace_2524_ = lean_ctor_get(v___y_2517_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___y_2517_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; 
v_unused_2533_ = lean_ctor_get(v___y_2517_, 2);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v___y_2517_, 0);
lean_dec(v_unused_2534_);
v___x_2526_ = v___y_2517_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_trace_2524_);
lean_dec(v___y_2517_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 2, v_buildTime_2523_);
lean_ctor_set(v___x_2526_, 0, v_log_2520_);
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_log_2520_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_trace_2524_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_buildTime_2523_);
v___x_2529_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; 
lean_ctor_set_uint8(v___x_2529_, sizeof(void*)*3, v_action_2521_);
lean_ctor_set_uint8(v___x_2529_, sizeof(void*)*3 + 1, v_wantsRebuild_2522_);
v___x_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2513_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
return v___x_2530_;
}
}
}
v___jp_2535_:
{
lean_object* v_a_2538_; 
v_a_2538_ = lean_ctor_get(v___y_2536_, 1);
lean_inc(v_a_2538_);
lean_dec_ref(v___y_2536_);
v___y_2517_ = v___y_2537_;
v___y_2518_ = v_a_2538_;
goto v___jp_2516_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* v_other_2567_, lean_object* v___x_2568_, uint8_t v___x_2569_, lean_object* v_rx_2570_){
_start:
{
lean_object* v_task_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; 
v_task_2571_ = lean_ctor_get(v_other_2567_, 0);
lean_inc_ref(v_task_2571_);
lean_dec_ref(v_other_2567_);
lean_inc(v___x_2568_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2572_, 0, v___x_2568_);
lean_closure_set(v___f_2572_, 1, v_rx_2570_);
v___x_2573_ = lean_task_map(v___f_2572_, v_task_2571_, v___x_2568_, v___x_2569_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* v_other_2574_, lean_object* v___x_2575_, lean_object* v___x_2576_, lean_object* v_rx_2577_){
_start:
{
uint8_t v___x_262__boxed_2578_; lean_object* v_res_2579_; 
v___x_262__boxed_2578_ = lean_unbox(v___x_2576_);
v_res_2579_ = l_Lake_Job_add___redArg___lam__1(v_other_2574_, v___x_2575_, v___x_262__boxed_2578_, v_rx_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* v_self_2580_, lean_object* v_other_2581_){
_start:
{
lean_object* v_task_2582_; lean_object* v_kind_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2597_; 
v_task_2582_ = lean_ctor_get(v_self_2580_, 0);
v_kind_2583_ = lean_ctor_get(v_self_2580_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_self_2580_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v_self_2580_, 2);
lean_dec(v_unused_2598_);
v___x_2585_ = v_self_2580_;
v_isShared_2586_ = v_isSharedCheck_2597_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_kind_2583_);
lean_inc(v_task_2582_);
lean_dec(v_self_2580_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2597_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___f_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = 0;
v___x_2589_ = lean_box(v___x_2588_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2590_, 0, v_other_2581_);
lean_closure_set(v___f_2590_, 1, v___x_2587_);
lean_closure_set(v___f_2590_, 2, v___x_2589_);
v___x_2591_ = 1;
v___x_2592_ = lean_task_bind(v_task_2582_, v___f_2590_, v___x_2587_, v___x_2591_);
v___x_2593_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 2, v___x_2593_);
lean_ctor_set(v___x_2585_, 0, v___x_2592_);
v___x_2595_ = v___x_2585_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_kind_2583_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*3, v___x_2588_);
return v___x_2595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* v_00_u03b1_2599_, lean_object* v_00_u03b2_2600_, lean_object* v_self_2601_, lean_object* v_other_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lake_Job_add___redArg(v_self_2601_, v_other_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* v___x_2604_, lean_object* v_rx_2605_, lean_object* v_ry_2606_){
_start:
{
lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2613_; lean_object* v___y_2614_; 
if (lean_obj_tag(v_rx_2605_) == 0)
{
if (lean_obj_tag(v_ry_2606_) == 0)
{
lean_object* v_a_2616_; lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v___x_2604_);
v_a_2616_ = lean_ctor_get(v_rx_2605_, 1);
lean_inc(v_a_2616_);
lean_dec_ref(v_rx_2605_);
v_a_2617_ = lean_ctor_get(v_ry_2606_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_ry_2606_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v_ry_2606_, 0);
lean_dec(v_unused_2627_);
v___x_2619_ = v_ry_2606_;
v_isShared_2620_ = v_isSharedCheck_2626_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v_ry_2606_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2626_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Lake_JobState_merge(v_a_2616_, v_a_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 1, v___x_2622_);
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2624_ = v___x_2619_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v_rx_2605_, 1);
lean_inc(v_a_2628_);
lean_dec_ref(v_rx_2605_);
v___y_2613_ = v_ry_2606_;
v___y_2614_ = v_a_2628_;
goto v___jp_2612_;
}
}
else
{
lean_object* v_a_2629_; 
v_a_2629_ = lean_ctor_get(v_rx_2605_, 1);
lean_inc(v_a_2629_);
lean_dec_ref(v_rx_2605_);
v___y_2613_ = v_ry_2606_;
v___y_2614_ = v_a_2629_;
goto v___jp_2612_;
}
v___jp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = l_Lake_JobState_merge(v___y_2608_, v___y_2609_);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2604_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
return v___x_2611_;
}
v___jp_2612_:
{
lean_object* v_a_2615_; 
v_a_2615_ = lean_ctor_get(v___y_2613_, 1);
lean_inc(v_a_2615_);
lean_dec_ref(v___y_2613_);
v___y_2608_ = v___y_2614_;
v___y_2609_ = v_a_2615_;
goto v___jp_2607_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* v_other_2630_, lean_object* v___x_2631_, uint8_t v___x_2632_, lean_object* v_rx_2633_){
_start:
{
lean_object* v_task_2634_; lean_object* v___f_2635_; lean_object* v___x_2636_; 
v_task_2634_ = lean_ctor_get(v_other_2630_, 0);
lean_inc_ref(v_task_2634_);
lean_dec_ref(v_other_2630_);
lean_inc(v___x_2631_);
v___f_2635_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2635_, 0, v___x_2631_);
lean_closure_set(v___f_2635_, 1, v_rx_2633_);
v___x_2636_ = lean_task_map(v___f_2635_, v_task_2634_, v___x_2631_, v___x_2632_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* v_other_2637_, lean_object* v___x_2638_, lean_object* v___x_2639_, lean_object* v_rx_2640_){
_start:
{
uint8_t v___x_142__boxed_2641_; lean_object* v_res_2642_; 
v___x_142__boxed_2641_ = lean_unbox(v___x_2639_);
v_res_2642_ = l_Lake_Job_mix___redArg___lam__1(v_other_2637_, v___x_2638_, v___x_142__boxed_2641_, v_rx_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* v_self_2643_, lean_object* v_other_2644_){
_start:
{
lean_object* v_task_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2660_; 
v_task_2645_ = lean_ctor_get(v_self_2643_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_self_2643_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; lean_object* v_unused_2662_; 
v_unused_2661_ = lean_ctor_get(v_self_2643_, 2);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_self_2643_, 1);
lean_dec(v_unused_2662_);
v___x_2647_ = v_self_2643_;
v_isShared_2648_ = v_isSharedCheck_2660_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_task_2645_);
lean_dec(v_self_2643_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2660_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; lean_object* v___x_2658_; 
v___x_2649_ = l_Lake_instDataKindUnit;
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = 1;
v___x_2652_ = lean_box(v___x_2651_);
v___f_2653_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2653_, 0, v_other_2644_);
lean_closure_set(v___f_2653_, 1, v___x_2650_);
lean_closure_set(v___f_2653_, 2, v___x_2652_);
v___x_2654_ = lean_task_bind(v_task_2645_, v___f_2653_, v___x_2650_, v___x_2651_);
v___x_2655_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2656_ = 0;
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 2, v___x_2655_);
lean_ctor_set(v___x_2647_, 1, v___x_2649_);
lean_ctor_set(v___x_2647_, 0, v___x_2654_);
v___x_2658_ = v___x_2647_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v___x_2655_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*3, v___x_2656_);
return v___x_2658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* v_00_u03b1_2663_, lean_object* v_00_u03b2_2664_, lean_object* v_self_2665_, lean_object* v_other_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lake_Job_mix___redArg(v_self_2665_, v_other_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* v_as_2668_, size_t v_i_2669_, size_t v_stop_2670_, lean_object* v_b_2671_){
_start:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_eq(v_i_2669_, v_stop_2670_);
if (v___x_2672_ == 0)
{
size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2673_ = ((size_t)1ULL);
v___x_2674_ = lean_usize_sub(v_i_2669_, v___x_2673_);
v___x_2675_ = lean_array_uget_borrowed(v_as_2668_, v___x_2674_);
lean_inc(v___x_2675_);
v___x_2676_ = l_Lake_Job_mix___redArg(v___x_2675_, v_b_2671_);
v_i_2669_ = v___x_2674_;
v_b_2671_ = v___x_2676_;
goto _start;
}
else
{
return v_b_2671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2678_, lean_object* v_i_2679_, lean_object* v_stop_2680_, lean_object* v_b_2681_){
_start:
{
size_t v_i_boxed_2682_; size_t v_stop_boxed_2683_; lean_object* v_res_2684_; 
v_i_boxed_2682_ = lean_unbox_usize(v_i_2679_);
lean_dec(v_i_2679_);
v_stop_boxed_2683_ = lean_unbox_usize(v_stop_2680_);
lean_dec(v_stop_2680_);
v_res_2684_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2678_, v_i_boxed_2682_, v_stop_boxed_2683_, v_b_2681_);
lean_dec_ref(v_as_2678_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object* v_init_2685_, lean_object* v_l_2686_){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2687_ = lean_array_mk(v_l_2686_);
v___x_2688_ = lean_array_get_size(v___x_2687_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_nat_dec_lt(v___x_2689_, v___x_2688_);
if (v___x_2690_ == 0)
{
lean_dec_ref(v___x_2687_);
return v_init_2685_;
}
else
{
size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_usize_of_nat(v___x_2688_);
v___x_2692_ = ((size_t)0ULL);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_2687_, v___x_2691_, v___x_2692_, v_init_2685_);
lean_dec_ref(v___x_2687_);
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* v_jobs_2694_, lean_object* v_traceCaption_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_box(0);
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2700_ = 0;
v___x_2701_ = 0;
v___x_2702_ = l_Lake_BuildTrace_nil(v_traceCaption_2695_);
v___x_2703_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2703_, 0, v___x_2699_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
lean_ctor_set(v___x_2703_, 2, v___x_2698_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*3, v___x_2700_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*3 + 1, v___x_2701_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2696_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_task_pure(v___x_2704_);
v___x_2706_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2707_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2697_);
lean_ctor_set(v___x_2707_, 2, v___x_2706_);
lean_ctor_set_uint8(v___x_2707_, sizeof(void*)*3, v___x_2701_);
v___x_2708_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_2707_, v_jobs_2694_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* v_00_u03b1_2709_, lean_object* v_jobs_2710_, lean_object* v_traceCaption_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lake_Job_mixList___redArg(v_jobs_2710_, v_traceCaption_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object* v_00_u03b1_2713_, lean_object* v_init_2714_, lean_object* v_l_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_2714_, v_l_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object* v_00_u03b1_2717_, lean_object* v_as_2718_, size_t v_i_2719_, size_t v_stop_2720_, lean_object* v_b_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2718_, v_i_2719_, v_stop_2720_, v_b_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_as_2724_, lean_object* v_i_2725_, lean_object* v_stop_2726_, lean_object* v_b_2727_){
_start:
{
size_t v_i_boxed_2728_; size_t v_stop_boxed_2729_; lean_object* v_res_2730_; 
v_i_boxed_2728_ = lean_unbox_usize(v_i_2725_);
lean_dec(v_i_2725_);
v_stop_boxed_2729_ = lean_unbox_usize(v_stop_2726_);
lean_dec(v_stop_2726_);
v_res_2730_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_2723_, v_as_2724_, v_i_boxed_2728_, v_stop_boxed_2729_, v_b_2727_);
lean_dec_ref(v_as_2724_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object* v_as_2731_, size_t v_i_2732_, size_t v_stop_2733_, lean_object* v_b_2734_){
_start:
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_usize_dec_eq(v_i_2732_, v_stop_2733_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; size_t v___x_2738_; size_t v___x_2739_; 
v___x_2736_ = lean_array_uget_borrowed(v_as_2731_, v_i_2732_);
lean_inc(v___x_2736_);
v___x_2737_ = l_Lake_Job_mix___redArg(v_b_2734_, v___x_2736_);
v___x_2738_ = ((size_t)1ULL);
v___x_2739_ = lean_usize_add(v_i_2732_, v___x_2738_);
v_i_2732_ = v___x_2739_;
v_b_2734_ = v___x_2737_;
goto _start;
}
else
{
return v_b_2734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* v_as_2741_, lean_object* v_i_2742_, lean_object* v_stop_2743_, lean_object* v_b_2744_){
_start:
{
size_t v_i_boxed_2745_; size_t v_stop_boxed_2746_; lean_object* v_res_2747_; 
v_i_boxed_2745_ = lean_unbox_usize(v_i_2742_);
lean_dec(v_i_2742_);
v_stop_boxed_2746_ = lean_unbox_usize(v_stop_2743_);
lean_dec(v_stop_2743_);
v_res_2747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2741_, v_i_boxed_2745_, v_stop_boxed_2746_, v_b_2744_);
lean_dec_ref(v_as_2741_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* v_jobs_2748_, lean_object* v_traceCaption_2749_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_box(0);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2754_ = 0;
v___x_2755_ = 0;
v___x_2756_ = l_Lake_BuildTrace_nil(v_traceCaption_2749_);
v___x_2757_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2757_, 0, v___x_2753_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_ctor_set(v___x_2757_, 2, v___x_2752_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3, v___x_2754_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3 + 1, v___x_2755_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2750_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_task_pure(v___x_2758_);
v___x_2760_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2761_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2751_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*3, v___x_2755_);
v___x_2762_ = lean_array_get_size(v_jobs_2748_);
v___x_2763_ = lean_nat_dec_lt(v___x_2752_, v___x_2762_);
if (v___x_2763_ == 0)
{
return v___x_2761_;
}
else
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_nat_dec_le(v___x_2762_, v___x_2762_);
if (v___x_2764_ == 0)
{
if (v___x_2763_ == 0)
{
return v___x_2761_;
}
else
{
size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = lean_usize_of_nat(v___x_2762_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2748_, v___x_2765_, v___x_2766_, v___x_2761_);
return v___x_2767_;
}
}
else
{
size_t v___x_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = ((size_t)0ULL);
v___x_2769_ = lean_usize_of_nat(v___x_2762_);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2748_, v___x_2768_, v___x_2769_, v___x_2761_);
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_2771_, lean_object* v_traceCaption_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lake_Job_mixArray___redArg(v_jobs_2771_, v_traceCaption_2772_);
lean_dec_ref(v_jobs_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_2774_, lean_object* v_jobs_2775_, lean_object* v_traceCaption_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lake_Job_mixArray___redArg(v_jobs_2775_, v_traceCaption_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_jobs_2779_, lean_object* v_traceCaption_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lake_Job_mixArray(v_00_u03b1_2778_, v_jobs_2779_, v_traceCaption_2780_);
lean_dec_ref(v_jobs_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_2782_, lean_object* v_as_2783_, size_t v_i_2784_, size_t v_stop_2785_, lean_object* v_b_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2783_, v_i_2784_, v_stop_2785_, v_b_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_2788_, lean_object* v_as_2789_, lean_object* v_i_2790_, lean_object* v_stop_2791_, lean_object* v_b_2792_){
_start:
{
size_t v_i_boxed_2793_; size_t v_stop_boxed_2794_; lean_object* v_res_2795_; 
v_i_boxed_2793_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_stop_boxed_2794_ = lean_unbox_usize(v_stop_2791_);
lean_dec(v_stop_2791_);
v_res_2795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_2788_, v_as_2789_, v_i_boxed_2793_, v_stop_boxed_2794_, v_b_2792_);
lean_dec_ref(v_as_2789_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_2796_, lean_object* v_rx_2797_, lean_object* v_ry_2798_){
_start:
{
lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2805_; lean_object* v___y_2806_; 
if (lean_obj_tag(v_rx_2797_) == 0)
{
if (lean_obj_tag(v_ry_2798_) == 0)
{
lean_object* v_a_2808_; lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___x_2796_);
v_a_2808_ = lean_ctor_get(v_rx_2797_, 0);
v_a_2809_ = lean_ctor_get(v_rx_2797_, 1);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_rx_2797_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2811_ = v_rx_2797_;
v_isShared_2812_ = v_isSharedCheck_2826_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_inc(v_a_2808_);
lean_dec(v_rx_2797_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2826_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_a_2813_; lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2825_; 
v_a_2813_ = lean_ctor_get(v_ry_2798_, 0);
v_a_2814_ = lean_ctor_get(v_ry_2798_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_ry_2798_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2816_ = v_ry_2798_;
v_isShared_2817_ = v_isSharedCheck_2825_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_inc(v_a_2813_);
lean_dec(v_ry_2798_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2825_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 1);
lean_ctor_set(v___x_2811_, 1, v_a_2813_);
v___x_2819_ = v___x_2811_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2808_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_a_2813_);
v___x_2819_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2820_ = l_Lake_JobState_merge(v_a_2809_, v_a_2814_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 1, v___x_2820_);
lean_ctor_set(v___x_2816_, 0, v___x_2819_);
v___x_2822_ = v___x_2816_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
else
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v_rx_2797_, 1);
lean_inc(v_a_2827_);
lean_dec_ref(v_rx_2797_);
v___y_2805_ = v_ry_2798_;
v___y_2806_ = v_a_2827_;
goto v___jp_2804_;
}
}
else
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v_rx_2797_, 1);
lean_inc(v_a_2828_);
lean_dec_ref(v_rx_2797_);
v___y_2805_ = v_ry_2798_;
v___y_2806_ = v_a_2828_;
goto v___jp_2804_;
}
v___jp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = l_Lake_JobState_merge(v___y_2800_, v___y_2801_);
v___x_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2796_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
return v___x_2803_;
}
v___jp_2804_:
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___y_2805_, 1);
lean_inc(v_a_2807_);
lean_dec_ref(v___y_2805_);
v___y_2800_ = v___y_2806_;
v___y_2801_ = v_a_2807_;
goto v___jp_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_2829_, lean_object* v___x_2830_, uint8_t v___x_2831_, lean_object* v_rx_2832_){
_start:
{
lean_object* v_task_2833_; lean_object* v___f_2834_; lean_object* v___x_2835_; 
v_task_2833_ = lean_ctor_get(v_b_2829_, 0);
lean_inc_ref(v_task_2833_);
lean_dec_ref(v_b_2829_);
lean_inc(v___x_2830_);
v___f_2834_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2834_, 0, v___x_2830_);
lean_closure_set(v___f_2834_, 1, v_rx_2832_);
v___x_2835_ = lean_task_map(v___f_2834_, v_task_2833_, v___x_2830_, v___x_2831_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_2836_, lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v_rx_2839_){
_start:
{
uint8_t v___x_480__boxed_2840_; lean_object* v_res_2841_; 
v___x_480__boxed_2840_ = lean_unbox(v___x_2838_);
v_res_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_2836_, v___x_2837_, v___x_480__boxed_2840_, v_rx_2839_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_2842_, size_t v_i_2843_, size_t v_stop_2844_, lean_object* v_b_2845_){
_start:
{
uint8_t v___x_2846_; 
v___x_2846_ = lean_usize_dec_eq(v_i_2843_, v_stop_2844_);
if (v___x_2846_ == 0)
{
size_t v___x_2847_; size_t v___x_2848_; lean_object* v___x_2849_; lean_object* v_task_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2865_; 
v___x_2847_ = ((size_t)1ULL);
v___x_2848_ = lean_usize_sub(v_i_2843_, v___x_2847_);
v___x_2849_ = lean_array_uget(v_as_2842_, v___x_2848_);
v_task_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; lean_object* v_unused_2867_; 
v_unused_2866_ = lean_ctor_get(v___x_2849_, 2);
lean_dec(v_unused_2866_);
v_unused_2867_ = lean_ctor_get(v___x_2849_, 1);
lean_dec(v_unused_2867_);
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2865_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_task_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2865_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___f_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_unsigned_to_nat(0u);
v___x_2856_ = 1;
v___x_2857_ = lean_box(v___x_2856_);
v___f_2858_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2858_, 0, v_b_2845_);
lean_closure_set(v___f_2858_, 1, v___x_2855_);
lean_closure_set(v___f_2858_, 2, v___x_2857_);
v___x_2859_ = lean_task_bind(v_task_2850_, v___f_2858_, v___x_2855_, v___x_2856_);
v___x_2860_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 2, v___x_2860_);
lean_ctor_set(v___x_2852_, 1, v___x_2854_);
lean_ctor_set(v___x_2852_, 0, v___x_2859_);
v___x_2862_ = v___x_2852_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_ctor_set_uint8(v___x_2862_, sizeof(void*)*3, v___x_2846_);
v_i_2843_ = v___x_2848_;
v_b_2845_ = v___x_2862_;
goto _start;
}
}
}
else
{
return v_b_2845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2868_, lean_object* v_i_2869_, lean_object* v_stop_2870_, lean_object* v_b_2871_){
_start:
{
size_t v_i_boxed_2872_; size_t v_stop_boxed_2873_; lean_object* v_res_2874_; 
v_i_boxed_2872_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_stop_boxed_2873_ = lean_unbox_usize(v_stop_2870_);
lean_dec(v_stop_2870_);
v_res_2874_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2868_, v_i_boxed_2872_, v_stop_boxed_2873_, v_b_2871_);
lean_dec_ref(v_as_2868_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_2875_, lean_object* v_l_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2877_ = lean_array_mk(v_l_2876_);
v___x_2878_ = lean_array_get_size(v___x_2877_);
v___x_2879_ = lean_unsigned_to_nat(0u);
v___x_2880_ = lean_nat_dec_lt(v___x_2879_, v___x_2878_);
if (v___x_2880_ == 0)
{
lean_dec_ref(v___x_2877_);
return v_init_2875_;
}
else
{
size_t v___x_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_usize_of_nat(v___x_2878_);
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_2877_, v___x_2881_, v___x_2882_, v_init_2875_);
lean_dec_ref(v___x_2877_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_2884_, lean_object* v_traceCaption_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; uint8_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_unsigned_to_nat(0u);
v___x_2889_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2890_ = 0;
v___x_2891_ = 0;
v___x_2892_ = l_Lake_BuildTrace_nil(v_traceCaption_2885_);
v___x_2893_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2893_, 0, v___x_2889_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
lean_ctor_set(v___x_2893_, 2, v___x_2888_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*3, v___x_2890_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*3 + 1, v___x_2891_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2886_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_task_pure(v___x_2894_);
v___x_2896_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2897_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2887_);
lean_ctor_set(v___x_2897_, 2, v___x_2896_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*3, v___x_2891_);
v___x_2898_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_2897_, v_jobs_2884_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_2899_, lean_object* v_jobs_2900_, lean_object* v_traceCaption_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lake_Job_collectList___redArg(v_jobs_2900_, v_traceCaption_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_2903_, lean_object* v_init_2904_, lean_object* v_l_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_2904_, v_l_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_2907_, lean_object* v_as_2908_, size_t v_i_2909_, size_t v_stop_2910_, lean_object* v_b_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2908_, v_i_2909_, v_stop_2910_, v_b_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2913_, lean_object* v_as_2914_, lean_object* v_i_2915_, lean_object* v_stop_2916_, lean_object* v_b_2917_){
_start:
{
size_t v_i_boxed_2918_; size_t v_stop_boxed_2919_; lean_object* v_res_2920_; 
v_i_boxed_2918_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_stop_boxed_2919_ = lean_unbox_usize(v_stop_2916_);
lean_dec(v_stop_2916_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_2913_, v_as_2914_, v_i_boxed_2918_, v_stop_boxed_2919_, v_b_2917_);
lean_dec_ref(v_as_2914_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_2921_, lean_object* v_rx_2922_, lean_object* v_ry_2923_){
_start:
{
lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2930_; lean_object* v___y_2931_; 
if (lean_obj_tag(v_rx_2922_) == 0)
{
if (lean_obj_tag(v_ry_2923_) == 0)
{
lean_object* v_a_2933_; lean_object* v_a_2934_; lean_object* v_a_2935_; lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v___x_2921_);
v_a_2933_ = lean_ctor_get(v_rx_2922_, 0);
lean_inc(v_a_2933_);
v_a_2934_ = lean_ctor_get(v_rx_2922_, 1);
lean_inc(v_a_2934_);
lean_dec_ref(v_rx_2922_);
v_a_2935_ = lean_ctor_get(v_ry_2923_, 0);
v_a_2936_ = lean_ctor_get(v_ry_2923_, 1);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_ry_2923_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2938_ = v_ry_2923_;
v_isShared_2939_ = v_isSharedCheck_2945_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_inc(v_a_2935_);
lean_dec(v_ry_2923_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2945_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2940_ = lean_array_push(v_a_2933_, v_a_2935_);
v___x_2941_ = l_Lake_JobState_merge(v_a_2934_, v_a_2936_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 1, v___x_2941_);
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2943_ = v___x_2938_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; 
v_a_2946_ = lean_ctor_get(v_rx_2922_, 1);
lean_inc(v_a_2946_);
lean_dec_ref(v_rx_2922_);
v___y_2930_ = v_ry_2923_;
v___y_2931_ = v_a_2946_;
goto v___jp_2929_;
}
}
else
{
lean_object* v_a_2947_; 
v_a_2947_ = lean_ctor_get(v_rx_2922_, 1);
lean_inc(v_a_2947_);
lean_dec_ref(v_rx_2922_);
v___y_2930_ = v_ry_2923_;
v___y_2931_ = v_a_2947_;
goto v___jp_2929_;
}
v___jp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = l_Lake_JobState_merge(v___y_2925_, v___y_2926_);
v___x_2928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2921_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
return v___x_2928_;
}
v___jp_2929_:
{
lean_object* v_a_2932_; 
v_a_2932_ = lean_ctor_get(v___y_2930_, 1);
lean_inc(v_a_2932_);
lean_dec_ref(v___y_2930_);
v___y_2925_ = v___y_2931_;
v___y_2926_ = v_a_2932_;
goto v___jp_2924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_2948_, lean_object* v___x_2949_, uint8_t v___x_2950_, lean_object* v_rx_2951_){
_start:
{
lean_object* v_task_2952_; lean_object* v___f_2953_; lean_object* v___x_2954_; 
v_task_2952_ = lean_ctor_get(v___x_2948_, 0);
lean_inc_ref(v_task_2952_);
lean_dec_ref(v___x_2948_);
lean_inc(v___x_2949_);
v___f_2953_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2953_, 0, v___x_2949_);
lean_closure_set(v___f_2953_, 1, v_rx_2951_);
v___x_2954_ = lean_task_map(v___f_2953_, v_task_2952_, v___x_2949_, v___x_2950_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_2955_, lean_object* v___x_2956_, lean_object* v___x_2957_, lean_object* v_rx_2958_){
_start:
{
uint8_t v___x_411__boxed_2959_; lean_object* v_res_2960_; 
v___x_411__boxed_2959_ = lean_unbox(v___x_2957_);
v_res_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_2955_, v___x_2956_, v___x_411__boxed_2959_, v_rx_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_2961_, size_t v_i_2962_, size_t v_stop_2963_, lean_object* v_b_2964_){
_start:
{
uint8_t v___x_2965_; 
v___x_2965_ = lean_usize_dec_eq(v_i_2962_, v_stop_2963_);
if (v___x_2965_ == 0)
{
lean_object* v_task_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2984_; 
v_task_2966_ = lean_ctor_get(v_b_2964_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_b_2964_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; lean_object* v_unused_2986_; 
v_unused_2985_ = lean_ctor_get(v_b_2964_, 2);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_b_2964_, 1);
lean_dec(v_unused_2986_);
v___x_2968_ = v_b_2964_;
v_isShared_2969_ = v_isSharedCheck_2984_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_task_2966_);
lean_dec(v_b_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2984_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2970_ = lean_box(0);
v___x_2971_ = lean_array_uget_borrowed(v_as_2961_, v_i_2962_);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = 1;
v___x_2974_ = lean_box(v___x_2973_);
lean_inc(v___x_2971_);
v___f_2975_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2975_, 0, v___x_2971_);
lean_closure_set(v___f_2975_, 1, v___x_2972_);
lean_closure_set(v___f_2975_, 2, v___x_2974_);
v___x_2976_ = lean_task_bind(v_task_2966_, v___f_2975_, v___x_2972_, v___x_2973_);
v___x_2977_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 2, v___x_2977_);
lean_ctor_set(v___x_2968_, 1, v___x_2970_);
lean_ctor_set(v___x_2968_, 0, v___x_2976_);
v___x_2979_ = v___x_2968_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
size_t v___x_2980_; size_t v___x_2981_; 
lean_ctor_set_uint8(v___x_2979_, sizeof(void*)*3, v___x_2965_);
v___x_2980_ = ((size_t)1ULL);
v___x_2981_ = lean_usize_add(v_i_2962_, v___x_2980_);
v_i_2962_ = v___x_2981_;
v_b_2964_ = v___x_2979_;
goto _start;
}
}
}
else
{
return v_b_2964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_2987_, lean_object* v_i_2988_, lean_object* v_stop_2989_, lean_object* v_b_2990_){
_start:
{
size_t v_i_boxed_2991_; size_t v_stop_boxed_2992_; lean_object* v_res_2993_; 
v_i_boxed_2991_ = lean_unbox_usize(v_i_2988_);
lean_dec(v_i_2988_);
v_stop_boxed_2992_ = lean_unbox_usize(v_stop_2989_);
lean_dec(v_stop_2989_);
v_res_2993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_2987_, v_i_boxed_2991_, v_stop_boxed_2992_, v_b_2990_);
lean_dec_ref(v_as_2987_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_2994_, lean_object* v_traceCaption_2995_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_2996_ = lean_array_get_size(v_jobs_2994_);
v___x_2997_ = lean_mk_empty_array_with_capacity(v___x_2996_);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3001_ = 0;
v___x_3002_ = 0;
v___x_3003_ = l_Lake_BuildTrace_nil(v_traceCaption_2995_);
v___x_3004_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3004_, 0, v___x_3000_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
lean_ctor_set(v___x_3004_, 2, v___x_2999_);
lean_ctor_set_uint8(v___x_3004_, sizeof(void*)*3, v___x_3001_);
lean_ctor_set_uint8(v___x_3004_, sizeof(void*)*3 + 1, v___x_3002_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_2997_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_task_pure(v___x_3005_);
v___x_3007_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_2998_);
lean_ctor_set(v___x_3008_, 2, v___x_3007_);
lean_ctor_set_uint8(v___x_3008_, sizeof(void*)*3, v___x_3002_);
v___x_3009_ = lean_nat_dec_lt(v___x_2999_, v___x_2996_);
if (v___x_3009_ == 0)
{
return v___x_3008_;
}
else
{
uint8_t v___x_3010_; 
v___x_3010_ = lean_nat_dec_le(v___x_2996_, v___x_2996_);
if (v___x_3010_ == 0)
{
if (v___x_3009_ == 0)
{
return v___x_3008_;
}
else
{
size_t v___x_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = ((size_t)0ULL);
v___x_3012_ = lean_usize_of_nat(v___x_2996_);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_2994_, v___x_3011_, v___x_3012_, v___x_3008_);
return v___x_3013_;
}
}
else
{
size_t v___x_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((size_t)0ULL);
v___x_3015_ = lean_usize_of_nat(v___x_2996_);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_2994_, v___x_3014_, v___x_3015_, v___x_3008_);
return v___x_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_3017_, lean_object* v_traceCaption_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lake_Job_collectArray___redArg(v_jobs_3017_, v_traceCaption_3018_);
lean_dec_ref(v_jobs_3017_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_3020_, lean_object* v_jobs_3021_, lean_object* v_traceCaption_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lake_Job_collectArray___redArg(v_jobs_3021_, v_traceCaption_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3024_, lean_object* v_jobs_3025_, lean_object* v_traceCaption_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lake_Job_collectArray(v_00_u03b1_3024_, v_jobs_3025_, v_traceCaption_3026_);
lean_dec_ref(v_jobs_3025_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3028_, lean_object* v_as_3029_, size_t v_i_3030_, size_t v_stop_3031_, lean_object* v_b_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3029_, v_i_3030_, v_stop_3031_, v_b_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3034_, lean_object* v_as_3035_, lean_object* v_i_3036_, lean_object* v_stop_3037_, lean_object* v_b_3038_){
_start:
{
size_t v_i_boxed_3039_; size_t v_stop_boxed_3040_; lean_object* v_res_3041_; 
v_i_boxed_3039_ = lean_unbox_usize(v_i_3036_);
lean_dec(v_i_3036_);
v_stop_boxed_3040_ = lean_unbox_usize(v_stop_3037_);
lean_dec(v_stop_3037_);
v_res_3041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3034_, v_as_3035_, v_i_boxed_3039_, v_stop_boxed_3040_, v_b_3038_);
lean_dec_ref(v_as_3035_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3042_, lean_object* v_inst_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_box(0);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3045_, lean_object* v_rx_3046_, lean_object* v_i_3047_, lean_object* v_ry_3048_){
_start:
{
lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3055_; lean_object* v___y_3056_; 
if (lean_obj_tag(v_rx_3046_) == 0)
{
if (lean_obj_tag(v_ry_3048_) == 0)
{
lean_object* v_a_3058_; lean_object* v_a_3059_; lean_object* v_a_3060_; lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v___x_3045_);
v_a_3058_ = lean_ctor_get(v_rx_3046_, 0);
lean_inc(v_a_3058_);
v_a_3059_ = lean_ctor_get(v_rx_3046_, 1);
lean_inc(v_a_3059_);
lean_dec_ref(v_rx_3046_);
v_a_3060_ = lean_ctor_get(v_ry_3048_, 0);
v_a_3061_ = lean_ctor_get(v_ry_3048_, 1);
v_isSharedCheck_3070_ = !lean_is_exclusive(v_ry_3048_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3063_ = v_ry_3048_;
v_isShared_3064_ = v_isSharedCheck_3070_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_inc(v_a_3060_);
lean_dec(v_ry_3048_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3070_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3065_ = lean_array_fset(v_a_3058_, v_i_3047_, v_a_3060_);
v___x_3066_ = l_Lake_JobState_merge(v_a_3059_, v_a_3061_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 1, v___x_3066_);
lean_ctor_set(v___x_3063_, 0, v___x_3065_);
v___x_3068_ = v___x_3063_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3065_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
else
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v_rx_3046_, 1);
lean_inc(v_a_3071_);
lean_dec_ref(v_rx_3046_);
v___y_3055_ = v_ry_3048_;
v___y_3056_ = v_a_3071_;
goto v___jp_3054_;
}
}
else
{
lean_object* v_a_3072_; 
v_a_3072_ = lean_ctor_get(v_rx_3046_, 1);
lean_inc(v_a_3072_);
lean_dec_ref(v_rx_3046_);
v___y_3055_ = v_ry_3048_;
v___y_3056_ = v_a_3072_;
goto v___jp_3054_;
}
v___jp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = l_Lake_JobState_merge(v___y_3050_, v___y_3051_);
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3045_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
return v___x_3053_;
}
v___jp_3054_:
{
lean_object* v_a_3057_; 
v_a_3057_ = lean_ctor_get(v___y_3055_, 1);
lean_inc(v_a_3057_);
lean_dec_ref(v___y_3055_);
v___y_3050_ = v___y_3056_;
v___y_3051_ = v_a_3057_;
goto v___jp_3049_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3073_, lean_object* v_rx_3074_, lean_object* v_i_3075_, lean_object* v_ry_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3073_, v_rx_3074_, v_i_3075_, v_ry_3076_);
lean_dec(v_i_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3078_, lean_object* v___x_3079_, lean_object* v_i_3080_, uint8_t v___x_3081_, lean_object* v_rx_3082_){
_start:
{
lean_object* v_task_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; 
v_task_3083_ = lean_ctor_get(v___x_3078_, 0);
lean_inc_ref(v_task_3083_);
lean_dec_ref(v___x_3078_);
lean_inc(v___x_3079_);
v___f_3084_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3084_, 0, v___x_3079_);
lean_closure_set(v___f_3084_, 1, v_rx_3082_);
lean_closure_set(v___f_3084_, 2, v_i_3080_);
v___x_3085_ = lean_task_map(v___f_3084_, v_task_3083_, v___x_3079_, v___x_3081_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3086_, lean_object* v___x_3087_, lean_object* v_i_3088_, lean_object* v___x_3089_, lean_object* v_rx_3090_){
_start:
{
uint8_t v___x_191__boxed_3091_; lean_object* v_res_3092_; 
v___x_191__boxed_3091_ = lean_unbox(v___x_3089_);
v_res_3092_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3086_, v___x_3087_, v_i_3088_, v___x_191__boxed_3091_, v_rx_3090_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3093_, lean_object* v___x_3094_, lean_object* v_i_3095_, lean_object* v_h_3096_, lean_object* v_job_3097_){
_start:
{
lean_object* v_task_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3113_; 
v_task_3098_ = lean_ctor_get(v_job_3097_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_job_3097_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; lean_object* v_unused_3115_; 
v_unused_3114_ = lean_ctor_get(v_job_3097_, 2);
lean_dec(v_unused_3114_);
v_unused_3115_ = lean_ctor_get(v_job_3097_, 1);
lean_dec(v_unused_3115_);
v___x_3100_ = v_job_3097_;
v_isShared_3101_ = v_isSharedCheck_3113_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_task_3098_);
lean_dec(v_job_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3113_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; lean_object* v___x_3111_; 
v___x_3102_ = lean_array_fget_borrowed(v_jobs_3093_, v_i_3095_);
v___x_3103_ = lean_unsigned_to_nat(0u);
v___x_3104_ = 1;
v___x_3105_ = lean_box(v___x_3104_);
lean_inc(v___x_3102_);
v___f_3106_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3106_, 0, v___x_3102_);
lean_closure_set(v___f_3106_, 1, v___x_3103_);
lean_closure_set(v___f_3106_, 2, v_i_3095_);
lean_closure_set(v___f_3106_, 3, v___x_3105_);
v___x_3107_ = lean_task_bind(v_task_3098_, v___f_3106_, v___x_3103_, v___x_3104_);
v___x_3108_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3109_ = 0;
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 2, v___x_3108_);
lean_ctor_set(v___x_3100_, 1, v___x_3094_);
lean_ctor_set(v___x_3100_, 0, v___x_3107_);
v___x_3111_ = v___x_3100_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v___x_3108_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*3, v___x_3109_);
return v___x_3111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3116_, lean_object* v___x_3117_, lean_object* v_i_3118_, lean_object* v_h_3119_, lean_object* v_job_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3116_, v___x_3117_, v_i_3118_, v_h_3119_, v_job_3120_);
lean_dec_ref(v_jobs_3116_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3122_, lean_object* v_jobs_3123_, lean_object* v_traceCaption_3124_){
_start:
{
lean_object* v_placeholder_3125_; lean_object* v___x_3126_; lean_object* v___f_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_placeholder_3125_ = lean_box(0);
v___x_3126_ = lean_box(0);
v___f_3127_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3127_, 0, v_jobs_3123_);
lean_closure_set(v___f_3127_, 1, v___x_3126_);
lean_inc(v_n_3122_);
v___x_3128_ = lean_mk_array(v_n_3122_, v_placeholder_3125_);
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3131_ = 0;
v___x_3132_ = 0;
v___x_3133_ = l_Lake_BuildTrace_nil(v_traceCaption_3124_);
v___x_3134_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3134_, 0, v___x_3130_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
lean_ctor_set(v___x_3134_, 2, v___x_3129_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*3, v___x_3131_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*3 + 1, v___x_3132_);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3128_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_task_pure(v___x_3135_);
v___x_3137_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3138_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3126_);
lean_ctor_set(v___x_3138_, 2, v___x_3137_);
lean_ctor_set_uint8(v___x_3138_, sizeof(void*)*3, v___x_3132_);
lean_inc(v_n_3122_);
v___x_3139_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3122_, v___f_3127_, v_n_3122_, lean_box(0), v___x_3138_);
lean_dec(v_n_3122_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3140_, lean_object* v_00_u03b1_3141_, lean_object* v_inst_3142_, lean_object* v_jobs_3143_, lean_object* v_traceCaption_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lake_Job_collectVector___redArg(v_n_3140_, v_jobs_3143_, v_traceCaption_3144_);
return v___x_3145_;
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
