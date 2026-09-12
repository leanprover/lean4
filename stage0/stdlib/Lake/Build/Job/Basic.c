// Lean compiler output
// Module: Lake.Build.Job.Basic
// Imports: public import Lake.Util.Log public import Lake.Util.Task public import Lake.Util.Opaque public import Lake.Build.Trace public import Lake.Build.Data
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_LogLevel_ctorIdx(uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedJobAction_default;
LEAN_EXPORT uint8_t l_Lake_instInhabitedJobAction;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lake.JobAction.unknown"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__0 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__1 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__1_value;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.JobAction.reuse"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__2 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__3 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__3_value;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.JobAction.replay"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__4 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__5 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__5_value;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.JobAction.unpack"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__6 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__7 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__7_value;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.JobAction.fetch"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__8 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__9 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__9_value;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.JobAction.build"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__10 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__10_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__10_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__11 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__11_value;
static lean_once_cell_t l_Lake_instReprJobAction_repr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprJobAction_repr___closed__12;
static lean_once_cell_t l_Lake_instReprJobAction_repr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprJobAction_repr___closed__13;
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprJobAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprJobAction_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprJobAction___closed__0 = (const lean_object*)&l_Lake_instReprJobAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprJobAction = (const lean_object*)&l_Lake_instReprJobAction___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_JobAction_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqJobAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqJobAction___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdJobAction_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instOrdJobAction_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdJobAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdJobAction_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdJobAction___closed__0 = (const lean_object*)&l_Lake_instOrdJobAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdJobAction = (const lean_object*)&l_Lake_instOrdJobAction___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_JobAction_instLT;
LEAN_EXPORT lean_object* l_Lake_JobAction_instLE;
LEAN_EXPORT uint8_t l_Lake_JobAction_instMin___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_JobAction_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_JobAction_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_JobAction_instMin___closed__0 = (const lean_object*)&l_Lake_JobAction_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_JobAction_instMin = (const lean_object*)&l_Lake_JobAction_instMin___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_JobAction_instMax___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_JobAction_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_JobAction_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_JobAction_instMax___closed__0 = (const lean_object*)&l_Lake_JobAction_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_JobAction_instMax = (const lean_object*)&l_Lake_JobAction_instMax___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_merge___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_JobAction_verb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ran"};
static const lean_object* l_Lake_JobAction_verb___closed__0 = (const lean_object*)&l_Lake_JobAction_verb___closed__0_value;
static const lean_string_object l_Lake_JobAction_verb___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Running"};
static const lean_object* l_Lake_JobAction_verb___closed__1 = (const lean_object*)&l_Lake_JobAction_verb___closed__1_value;
static const lean_string_object l_Lake_JobAction_verb___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Reused"};
static const lean_object* l_Lake_JobAction_verb___closed__2 = (const lean_object*)&l_Lake_JobAction_verb___closed__2_value;
static const lean_string_object l_Lake_JobAction_verb___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reusing"};
static const lean_object* l_Lake_JobAction_verb___closed__3 = (const lean_object*)&l_Lake_JobAction_verb___closed__3_value;
static const lean_string_object l_Lake_JobAction_verb___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Replayed"};
static const lean_object* l_Lake_JobAction_verb___closed__4 = (const lean_object*)&l_Lake_JobAction_verb___closed__4_value;
static const lean_string_object l_Lake_JobAction_verb___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Replaying"};
static const lean_object* l_Lake_JobAction_verb___closed__5 = (const lean_object*)&l_Lake_JobAction_verb___closed__5_value;
static const lean_string_object l_Lake_JobAction_verb___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Unpacked"};
static const lean_object* l_Lake_JobAction_verb___closed__6 = (const lean_object*)&l_Lake_JobAction_verb___closed__6_value;
static const lean_string_object l_Lake_JobAction_verb___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Unpacking"};
static const lean_object* l_Lake_JobAction_verb___closed__7 = (const lean_object*)&l_Lake_JobAction_verb___closed__7_value;
static const lean_string_object l_Lake_JobAction_verb___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Fetched"};
static const lean_object* l_Lake_JobAction_verb___closed__8 = (const lean_object*)&l_Lake_JobAction_verb___closed__8_value;
static const lean_string_object l_Lake_JobAction_verb___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Fetching"};
static const lean_object* l_Lake_JobAction_verb___closed__9 = (const lean_object*)&l_Lake_JobAction_verb___closed__9_value;
static const lean_string_object l_Lake_JobAction_verb___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Built"};
static const lean_object* l_Lake_JobAction_verb___closed__10 = (const lean_object*)&l_Lake_JobAction_verb___closed__10_value;
static const lean_string_object l_Lake_JobAction_verb___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Building"};
static const lean_object* l_Lake_JobAction_verb___closed__11 = (const lean_object*)&l_Lake_JobAction_verb___closed__11_value;
LEAN_EXPORT lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lake_instInhabitedJobState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedJobState_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedJobState_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedJobState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_instInhabitedJobState_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedJobState_default___closed__1_value;
static lean_once_cell_t l_Lake_instInhabitedJobState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJobState_default___closed__2;
static lean_once_cell_t l_Lake_instInhabitedJobState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJobState_default___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedJobState_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedJobState;
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_cancelMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "canceled after earlier build failure"};
static const lean_object* l_Lake_cancelMessage___closed__0 = (const lean_object*)&l_Lake_cancelMessage___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_cancelMessage = (const lean_object*)&l_Lake_cancelMessage___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___closed__0;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_JobResult_isCanceled___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_JobResult_isCanceled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedJob___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJob___redArg___closed__0;
static lean_once_cell_t l_Lake_instInhabitedJob___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJob___redArg___closed__1;
static const lean_string_object l_Lake_instInhabitedJob___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedJob___redArg___closed__2 = (const lean_object*)&l_Lake_instInhabitedJob___redArg___closed__2_value;
static lean_once_cell_t l_Lake_instInhabitedJob___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJob___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_instInhabitedJob___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJob___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Job_instPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Job_instPure___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Job_instPure___closed__0 = (const lean_object*)&l_Lake_Job_instPure___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Job_instPure = (const lean_object*)&l_Lake_Job_instPure___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Job_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Job_instFunctor___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Job_instFunctor___closed__0 = (const lean_object*)&l_Lake_Job_instFunctor___closed__0_value;
static const lean_closure_object l_Lake_Job_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Job_instFunctor___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_Job_instFunctor___closed__0_value)} };
static const lean_object* l_Lake_Job_instFunctor___closed__1 = (const lean_object*)&l_Lake_Job_instFunctor___closed__1_value;
static const lean_ctor_object l_Lake_Job_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Job_instFunctor___closed__0_value),((lean_object*)&l_Lake_Job_instFunctor___closed__1_value)}};
static const lean_object* l_Lake_Job_instFunctor___closed__2 = (const lean_object*)&l_Lake_Job_instFunctor___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_Job_instFunctor = (const lean_object*)&l_Lake_Job_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0 = (const lean_object*)&l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg();
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Job_toOpaque, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0 = (const lean_object*)&l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg();
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_x_boxed_9_; lean_object* v_res_10_; 
v_x_boxed_9_ = lean_unbox(v_x_8_);
v_res_10_ = l_Lake_JobAction_ctorIdx(v_x_boxed_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg(lean_object* v_k_11_){
_start:
{
lean_inc(v_k_11_);
return v_k_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg___boxed(lean_object* v_k_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lake_JobAction_ctorElim___redArg(v_k_12_);
lean_dec(v_k_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, uint8_t v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_inc(v_k_18_);
return v_k_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
uint8_t v_t_boxed_24_; lean_object* v_res_25_; 
v_t_boxed_24_ = lean_unbox(v_t_21_);
v_res_25_ = l_Lake_JobAction_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_boxed_24_, v_h_22_, v_k_23_);
lean_dec(v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg(lean_object* v_unknown_26_){
_start:
{
lean_inc(v_unknown_26_);
return v_unknown_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg___boxed(lean_object* v_unknown_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_JobAction_unknown_elim___redArg(v_unknown_27_);
lean_dec(v_unknown_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim(lean_object* v_motive_29_, uint8_t v_t_30_, lean_object* v_h_31_, lean_object* v_unknown_32_){
_start:
{
lean_inc(v_unknown_32_);
return v_unknown_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___boxed(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_unknown_36_){
_start:
{
uint8_t v_t_boxed_37_; lean_object* v_res_38_; 
v_t_boxed_37_ = lean_unbox(v_t_34_);
v_res_38_ = l_Lake_JobAction_unknown_elim(v_motive_33_, v_t_boxed_37_, v_h_35_, v_unknown_36_);
lean_dec(v_unknown_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg(lean_object* v_reuse_39_){
_start:
{
lean_inc(v_reuse_39_);
return v_reuse_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg___boxed(lean_object* v_reuse_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lake_JobAction_reuse_elim___redArg(v_reuse_40_);
lean_dec(v_reuse_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim(lean_object* v_motive_42_, uint8_t v_t_43_, lean_object* v_h_44_, lean_object* v_reuse_45_){
_start:
{
lean_inc(v_reuse_45_);
return v_reuse_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_reuse_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lake_JobAction_reuse_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_reuse_49_);
lean_dec(v_reuse_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg(lean_object* v_replay_52_){
_start:
{
lean_inc(v_replay_52_);
return v_replay_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg___boxed(lean_object* v_replay_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_JobAction_replay_elim___redArg(v_replay_53_);
lean_dec(v_replay_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_replay_58_){
_start:
{
lean_inc(v_replay_58_);
return v_replay_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___boxed(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_replay_62_){
_start:
{
uint8_t v_t_boxed_63_; lean_object* v_res_64_; 
v_t_boxed_63_ = lean_unbox(v_t_60_);
v_res_64_ = l_Lake_JobAction_replay_elim(v_motive_59_, v_t_boxed_63_, v_h_61_, v_replay_62_);
lean_dec(v_replay_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg(lean_object* v_unpack_65_){
_start:
{
lean_inc(v_unpack_65_);
return v_unpack_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg___boxed(lean_object* v_unpack_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lake_JobAction_unpack_elim___redArg(v_unpack_66_);
lean_dec(v_unpack_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim(lean_object* v_motive_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_unpack_71_){
_start:
{
lean_inc(v_unpack_71_);
return v_unpack_71_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_unpack_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Lake_JobAction_unpack_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_unpack_75_);
lean_dec(v_unpack_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg(lean_object* v_fetch_78_){
_start:
{
lean_inc(v_fetch_78_);
return v_fetch_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg___boxed(lean_object* v_fetch_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_JobAction_fetch_elim___redArg(v_fetch_79_);
lean_dec(v_fetch_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim(lean_object* v_motive_81_, uint8_t v_t_82_, lean_object* v_h_83_, lean_object* v_fetch_84_){
_start:
{
lean_inc(v_fetch_84_);
return v_fetch_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___boxed(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_fetch_88_){
_start:
{
uint8_t v_t_boxed_89_; lean_object* v_res_90_; 
v_t_boxed_89_ = lean_unbox(v_t_86_);
v_res_90_ = l_Lake_JobAction_fetch_elim(v_motive_85_, v_t_boxed_89_, v_h_87_, v_fetch_88_);
lean_dec(v_fetch_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg(lean_object* v_build_91_){
_start:
{
lean_inc(v_build_91_);
return v_build_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg___boxed(lean_object* v_build_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lake_JobAction_build_elim___redArg(v_build_92_);
lean_dec(v_build_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim(lean_object* v_motive_94_, uint8_t v_t_95_, lean_object* v_h_96_, lean_object* v_build_97_){
_start:
{
lean_inc(v_build_97_);
return v_build_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___boxed(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_build_101_){
_start:
{
uint8_t v_t_boxed_102_; lean_object* v_res_103_; 
v_t_boxed_102_ = lean_unbox(v_t_99_);
v_res_103_ = l_Lake_JobAction_build_elim(v_motive_98_, v_t_boxed_102_, v_h_100_, v_build_101_);
lean_dec(v_build_101_);
return v_res_103_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction_default(void){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction(void){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__12(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__13(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr(uint8_t v_x_128_, lean_object* v_prec_129_){
_start:
{
lean_object* v___y_131_; lean_object* v___y_138_; lean_object* v___y_145_; lean_object* v___y_152_; lean_object* v___y_159_; lean_object* v___y_166_; 
switch(v_x_128_)
{
case 0:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_129_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_131_ = v___x_174_;
goto v___jp_130_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_131_ = v___x_175_;
goto v___jp_130_;
}
}
case 1:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_nat_dec_le(v___x_176_, v_prec_129_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_138_ = v___x_178_;
goto v___jp_137_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_138_ = v___x_179_;
goto v___jp_137_;
}
}
case 2:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1024u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_prec_129_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_145_ = v___x_182_;
goto v___jp_144_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_145_ = v___x_183_;
goto v___jp_144_;
}
}
case 3:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_185_ = lean_nat_dec_le(v___x_184_, v_prec_129_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_152_ = v___x_186_;
goto v___jp_151_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_152_ = v___x_187_;
goto v___jp_151_;
}
}
case 4:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1024u);
v___x_189_ = lean_nat_dec_le(v___x_188_, v_prec_129_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_159_ = v___x_190_;
goto v___jp_158_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_159_ = v___x_191_;
goto v___jp_158_;
}
}
default: 
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1024u);
v___x_193_ = lean_nat_dec_le(v___x_192_, v_prec_129_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_166_ = v___x_194_;
goto v___jp_165_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_166_ = v___x_195_;
goto v___jp_165_;
}
}
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__1));
lean_inc(v___y_131_);
v___x_133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_133_, 0, v___y_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v_prec_129_);
return v___x_136_;
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__3));
lean_inc(v___y_138_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_129_);
return v___x_143_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__5));
lean_inc(v___y_145_);
v___x_147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_147_, 0, v___y_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = 0;
v___x_149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = l_Repr_addAppParen(v___x_149_, v_prec_129_);
return v___x_150_;
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__7));
lean_inc(v___y_152_);
v___x_154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_154_, 0, v___y_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = 0;
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_155_);
v___x_157_ = l_Repr_addAppParen(v___x_156_, v_prec_129_);
return v___x_157_;
}
v___jp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_160_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__9));
lean_inc(v___y_159_);
v___x_161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = 0;
v___x_163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_162_);
v___x_164_ = l_Repr_addAppParen(v___x_163_, v_prec_129_);
return v___x_164_;
}
v___jp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_167_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__11));
lean_inc(v___y_166_);
v___x_168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_168_, 0, v___y_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = 0;
v___x_170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*1, v___x_169_);
v___x_171_ = l_Repr_addAppParen(v___x_170_, v_prec_129_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr___boxed(lean_object* v_x_196_, lean_object* v_prec_197_){
_start:
{
uint8_t v_x_333__boxed_198_; lean_object* v_res_199_; 
v_x_333__boxed_198_ = lean_unbox(v_x_196_);
v_res_199_ = l_Lake_instReprJobAction_repr(v_x_333__boxed_198_, v_prec_197_);
lean_dec(v_prec_197_);
return v_res_199_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_ofNat(lean_object* v_n_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(2u);
v___x_204_ = lean_nat_dec_le(v_n_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(3u);
v___x_206_ = lean_nat_dec_le(v_n_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(4u);
v___x_208_ = lean_nat_dec_le(v_n_202_, v___x_207_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
v___x_209_ = 5;
return v___x_209_;
}
else
{
uint8_t v___x_210_; 
v___x_210_ = 4;
return v___x_210_;
}
}
else
{
uint8_t v___x_211_; 
v___x_211_ = 3;
return v___x_211_;
}
}
else
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_nat_dec_le(v_n_202_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_dec_le(v_n_202_, v___x_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; 
v___x_216_ = 2;
return v___x_216_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = 1;
return v___x_217_;
}
}
else
{
uint8_t v___x_218_; 
v___x_218_ = 0;
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ofNat___boxed(lean_object* v_n_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Lake_JobAction_ofNat(v_n_219_);
lean_dec(v_n_219_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqJobAction(uint8_t v_x_222_, uint8_t v_y_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = l_Lake_JobAction_ctorIdx(v_x_222_);
v___x_225_ = l_Lake_JobAction_ctorIdx(v_y_223_);
v___x_226_ = lean_nat_dec_eq(v___x_224_, v___x_225_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqJobAction___boxed(lean_object* v_x_227_, lean_object* v_y_228_){
_start:
{
uint8_t v_x_20__boxed_229_; uint8_t v_y_21__boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v_x_20__boxed_229_ = lean_unbox(v_x_227_);
v_y_21__boxed_230_ = lean_unbox(v_y_228_);
v_res_231_ = l_Lake_instDecidableEqJobAction(v_x_20__boxed_229_, v_y_21__boxed_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdJobAction_ord(uint8_t v_x_233_, uint8_t v_y_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_235_ = l_Lake_JobAction_ctorIdx(v_x_233_);
v___x_236_ = l_Lake_JobAction_ctorIdx(v_y_234_);
v___x_237_ = lean_nat_dec_lt(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
uint8_t v___x_238_; 
v___x_238_ = lean_nat_dec_eq(v___x_235_, v___x_236_);
lean_dec(v___x_236_);
lean_dec(v___x_235_);
if (v___x_238_ == 0)
{
uint8_t v___x_239_; 
v___x_239_ = 2;
return v___x_239_;
}
else
{
uint8_t v___x_240_; 
v___x_240_ = 1;
return v___x_240_;
}
}
else
{
uint8_t v___x_241_; 
lean_dec(v___x_236_);
lean_dec(v___x_235_);
v___x_241_ = 0;
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdJobAction_ord___boxed(lean_object* v_x_242_, lean_object* v_y_243_){
_start:
{
uint8_t v_x_30__boxed_244_; uint8_t v_y_31__boxed_245_; uint8_t v_res_246_; lean_object* v_r_247_; 
v_x_30__boxed_244_ = lean_unbox(v_x_242_);
v_y_31__boxed_245_ = lean_unbox(v_y_243_);
v_res_246_ = l_Lake_instOrdJobAction_ord(v_x_30__boxed_244_, v_y_31__boxed_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
static lean_object* _init_l_Lake_JobAction_instLT(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_box(0);
return v___x_250_;
}
}
static lean_object* _init_l_Lake_JobAction_instLE(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_instMin___lam__0(uint8_t v_x_252_, uint8_t v_y_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = l_Lake_instOrdJobAction_ord(v_x_252_, v_y_253_);
if (v___x_254_ == 2)
{
return v_y_253_;
}
else
{
return v_x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMin___lam__0___boxed(lean_object* v_x_255_, lean_object* v_y_256_){
_start:
{
uint8_t v_x_boxed_257_; uint8_t v_y_boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v_x_boxed_257_ = lean_unbox(v_x_255_);
v_y_boxed_258_ = lean_unbox(v_y_256_);
v_res_259_ = l_Lake_JobAction_instMin___lam__0(v_x_boxed_257_, v_y_boxed_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_instMax___lam__0(uint8_t v_x_263_, uint8_t v_y_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l_Lake_instOrdJobAction_ord(v_x_263_, v_y_264_);
if (v___x_265_ == 2)
{
return v_x_263_;
}
else
{
return v_y_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMax___lam__0___boxed(lean_object* v_x_266_, lean_object* v_y_267_){
_start:
{
uint8_t v_x_boxed_268_; uint8_t v_y_boxed_269_; uint8_t v_res_270_; lean_object* v_r_271_; 
v_x_boxed_268_ = lean_unbox(v_x_266_);
v_y_boxed_269_ = lean_unbox(v_y_267_);
v_res_270_ = l_Lake_JobAction_instMax___lam__0(v_x_boxed_268_, v_y_boxed_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_merge(uint8_t v_a_274_, uint8_t v_b_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = l_Lake_instOrdJobAction_ord(v_a_274_, v_b_275_);
if (v___x_276_ == 2)
{
return v_a_274_;
}
else
{
return v_b_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_merge___boxed(lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
uint8_t v_a_boxed_279_; uint8_t v_b_boxed_280_; uint8_t v_res_281_; lean_object* v_r_282_; 
v_a_boxed_279_ = lean_unbox(v_a_277_);
v_b_boxed_280_ = lean_unbox(v_b_278_);
v_res_281_ = l_Lake_JobAction_merge(v_a_boxed_279_, v_b_boxed_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb(uint8_t v_failed_295_, uint8_t v_x_296_){
_start:
{
switch(v_x_296_)
{
case 0:
{
if (v_failed_295_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l_Lake_JobAction_verb___closed__0));
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lake_JobAction_verb___closed__1));
return v___x_298_;
}
}
case 1:
{
if (v_failed_295_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l_Lake_JobAction_verb___closed__2));
return v___x_299_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = ((lean_object*)(l_Lake_JobAction_verb___closed__3));
return v___x_300_;
}
}
case 2:
{
if (v_failed_295_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lake_JobAction_verb___closed__4));
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = ((lean_object*)(l_Lake_JobAction_verb___closed__5));
return v___x_302_;
}
}
case 3:
{
if (v_failed_295_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = ((lean_object*)(l_Lake_JobAction_verb___closed__6));
return v___x_303_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l_Lake_JobAction_verb___closed__7));
return v___x_304_;
}
}
case 4:
{
if (v_failed_295_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = ((lean_object*)(l_Lake_JobAction_verb___closed__8));
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l_Lake_JobAction_verb___closed__9));
return v___x_306_;
}
}
default: 
{
if (v_failed_295_ == 0)
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Lake_JobAction_verb___closed__10));
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = ((lean_object*)(l_Lake_JobAction_verb___closed__11));
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object* v_failed_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_failed_boxed_311_; uint8_t v_x_136__boxed_312_; lean_object* v_res_313_; 
v_failed_boxed_311_ = lean_unbox(v_failed_309_);
v_x_136__boxed_312_ = lean_unbox(v_x_310_);
v_res_313_ = l_Lake_JobAction_verb(v_failed_boxed_311_, v_x_136__boxed_312_);
return v_res_313_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__1));
v___x_318_ = l_Lake_BuildTrace_nil(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_321_ = 0;
v___x_322_ = 0;
v___x_323_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_324_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_320_);
lean_ctor_set(v___x_324_, 2, v___x_319_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*3, v___x_322_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*3 + 1, v___x_321_);
return v___x_324_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
return v___x_325_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState(void){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lake_instInhabitedJobState_default;
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_log_329_; uint8_t v_action_330_; uint8_t v_wantsRebuild_331_; lean_object* v_trace_332_; lean_object* v_buildTime_333_; lean_object* v_log_334_; uint8_t v_action_335_; uint8_t v_wantsRebuild_336_; lean_object* v_trace_337_; lean_object* v_buildTime_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_351_; 
v_log_329_ = lean_ctor_get(v_a_327_, 0);
lean_inc_ref(v_log_329_);
v_action_330_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*3);
v_wantsRebuild_331_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*3 + 1);
v_trace_332_ = lean_ctor_get(v_a_327_, 1);
lean_inc_ref(v_trace_332_);
v_buildTime_333_ = lean_ctor_get(v_a_327_, 2);
lean_inc(v_buildTime_333_);
lean_dec_ref(v_a_327_);
v_log_334_ = lean_ctor_get(v_b_328_, 0);
v_action_335_ = lean_ctor_get_uint8(v_b_328_, sizeof(void*)*3);
v_wantsRebuild_336_ = lean_ctor_get_uint8(v_b_328_, sizeof(void*)*3 + 1);
v_trace_337_ = lean_ctor_get(v_b_328_, 1);
v_buildTime_338_ = lean_ctor_get(v_b_328_, 2);
v_isSharedCheck_351_ = !lean_is_exclusive(v_b_328_);
if (v_isSharedCheck_351_ == 0)
{
v___x_340_ = v_b_328_;
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_buildTime_338_);
lean_inc(v_trace_337_);
lean_inc(v_log_334_);
lean_dec(v_b_328_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; uint8_t v___x_343_; uint8_t v___y_345_; 
v___x_342_ = l_Array_append___redArg(v_log_329_, v_log_334_);
lean_dec_ref(v_log_334_);
v___x_343_ = l_Lake_JobAction_merge(v_action_330_, v_action_335_);
if (v_wantsRebuild_331_ == 0)
{
v___y_345_ = v_wantsRebuild_336_;
goto v___jp_344_;
}
else
{
v___y_345_ = v_wantsRebuild_331_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_346_ = l_Lake_BuildTrace_mix(v_trace_332_, v_trace_337_);
v___x_347_ = lean_nat_add(v_buildTime_333_, v_buildTime_338_);
lean_dec(v_buildTime_338_);
lean_dec(v_buildTime_333_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 2, v___x_347_);
lean_ctor_set(v___x_340_, 1, v___x_346_);
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_349_ = v___x_340_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*3, v___x_343_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*3 + 1, v___y_345_);
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object* v_f_352_, lean_object* v_s_353_){
_start:
{
lean_object* v_log_354_; uint8_t v_action_355_; uint8_t v_wantsRebuild_356_; lean_object* v_trace_357_; lean_object* v_buildTime_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_log_354_ = lean_ctor_get(v_s_353_, 0);
v_action_355_ = lean_ctor_get_uint8(v_s_353_, sizeof(void*)*3);
v_wantsRebuild_356_ = lean_ctor_get_uint8(v_s_353_, sizeof(void*)*3 + 1);
v_trace_357_ = lean_ctor_get(v_s_353_, 1);
v_buildTime_358_ = lean_ctor_get(v_s_353_, 2);
v_isSharedCheck_366_ = !lean_is_exclusive(v_s_353_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v_s_353_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_buildTime_358_);
lean_inc(v_trace_357_);
lean_inc(v_log_354_);
lean_dec(v_s_353_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_apply_1(v_f_352_, v_log_354_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_trace_357_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_buildTime_358_);
lean_ctor_set_uint8(v_reuseFailAlloc_365_, sizeof(void*)*3, v_action_355_);
lean_ctor_set_uint8(v_reuseFailAlloc_365_, sizeof(void*)*3 + 1, v_wantsRebuild_356_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object* v_e_367_, lean_object* v_s_368_){
_start:
{
lean_object* v_log_369_; uint8_t v_action_370_; uint8_t v_wantsRebuild_371_; lean_object* v_trace_372_; lean_object* v_buildTime_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_log_369_ = lean_ctor_get(v_s_368_, 0);
v_action_370_ = lean_ctor_get_uint8(v_s_368_, sizeof(void*)*3);
v_wantsRebuild_371_ = lean_ctor_get_uint8(v_s_368_, sizeof(void*)*3 + 1);
v_trace_372_ = lean_ctor_get(v_s_368_, 1);
v_buildTime_373_ = lean_ctor_get(v_s_368_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v_s_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v_s_368_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_buildTime_373_);
lean_inc(v_trace_372_);
lean_inc(v_log_369_);
lean_dec(v_s_368_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_array_push(v_log_369_, v_e_367_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_trace_372_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_buildTime_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_380_, sizeof(void*)*3, v_action_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_380_, sizeof(void*)*3 + 1, v_wantsRebuild_371_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object* v_log_382_, lean_object* v_self_383_){
_start:
{
if (lean_obj_tag(v_self_383_) == 0)
{
lean_object* v_a_384_; lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_405_; 
v_a_384_ = lean_ctor_get(v_self_383_, 1);
v_a_385_ = lean_ctor_get(v_self_383_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_self_383_);
if (v_isSharedCheck_405_ == 0)
{
v___x_387_ = v_self_383_;
v_isShared_388_ = v_isSharedCheck_405_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_384_);
lean_inc(v_a_385_);
lean_dec(v_self_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_405_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_log_389_; uint8_t v_action_390_; uint8_t v_wantsRebuild_391_; lean_object* v_trace_392_; lean_object* v_buildTime_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_404_; 
v_log_389_ = lean_ctor_get(v_a_384_, 0);
v_action_390_ = lean_ctor_get_uint8(v_a_384_, sizeof(void*)*3);
v_wantsRebuild_391_ = lean_ctor_get_uint8(v_a_384_, sizeof(void*)*3 + 1);
v_trace_392_ = lean_ctor_get(v_a_384_, 1);
v_buildTime_393_ = lean_ctor_get(v_a_384_, 2);
v_isSharedCheck_404_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_404_ == 0)
{
v___x_395_ = v_a_384_;
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_buildTime_393_);
lean_inc(v_trace_392_);
lean_inc(v_log_389_);
lean_dec(v_a_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = l_Array_append___redArg(v_log_382_, v_log_389_);
lean_dec_ref(v_log_389_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_trace_392_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_buildTime_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*3, v_action_390_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*3 + 1, v_wantsRebuild_391_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_399_);
v___x_401_ = v___x_387_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_385_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_429_; 
v_a_406_ = lean_ctor_get(v_self_383_, 1);
v_a_407_ = lean_ctor_get(v_self_383_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_self_383_);
if (v_isSharedCheck_429_ == 0)
{
v___x_409_ = v_self_383_;
v_isShared_410_ = v_isSharedCheck_429_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_406_);
lean_inc(v_a_407_);
lean_dec(v_self_383_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_429_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_log_411_; uint8_t v_action_412_; uint8_t v_wantsRebuild_413_; lean_object* v_trace_414_; lean_object* v_buildTime_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_428_; 
v_log_411_ = lean_ctor_get(v_a_406_, 0);
v_action_412_ = lean_ctor_get_uint8(v_a_406_, sizeof(void*)*3);
v_wantsRebuild_413_ = lean_ctor_get_uint8(v_a_406_, sizeof(void*)*3 + 1);
v_trace_414_ = lean_ctor_get(v_a_406_, 1);
v_buildTime_415_ = lean_ctor_get(v_a_406_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_428_ == 0)
{
v___x_417_ = v_a_406_;
v_isShared_418_ = v_isSharedCheck_428_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_buildTime_415_);
lean_inc(v_trace_414_);
lean_inc(v_log_411_);
lean_dec(v_a_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_428_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_419_ = lean_array_get_size(v_log_382_);
v___x_420_ = lean_nat_add(v___x_419_, v_a_407_);
lean_dec(v_a_407_);
v___x_421_ = l_Array_append___redArg(v_log_382_, v_log_411_);
lean_dec_ref(v_log_411_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_421_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_trace_414_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_buildTime_415_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3, v_action_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 1, v_wantsRebuild_413_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_423_);
lean_ctor_set(v___x_409_, 0, v___x_420_);
v___x_425_ = v___x_409_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object* v_00_u03b1_430_, lean_object* v_log_431_, lean_object* v_self_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lake_JobResult_prependLog___redArg(v_log_431_, v_self_432_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___closed__0(void){
_start:
{
uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_436_ = 0;
v___x_437_ = l_Lake_LogLevel_ctorIdx(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0(lean_object* v_as_438_, size_t v_i_439_, size_t v_stop_440_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_eq(v_i_439_, v_stop_440_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v_level_447_; lean_object* v_message_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_446_ = lean_array_uget_borrowed(v_as_438_, v_i_439_);
v_level_447_ = lean_ctor_get_uint8(v___x_446_, sizeof(void*)*1);
v_message_448_ = lean_ctor_get(v___x_446_, 0);
v___x_449_ = l_Lake_LogLevel_ctorIdx(v_level_447_);
v___x_450_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___closed__0);
v___x_451_ = lean_nat_dec_eq(v___x_449_, v___x_450_);
lean_dec(v___x_449_);
if (v___x_451_ == 0)
{
goto v___jp_441_;
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lake_cancelMessage___closed__0));
v___x_453_ = lean_string_dec_eq(v_message_448_, v___x_452_);
if (v___x_453_ == 0)
{
goto v___jp_441_;
}
else
{
return v___x_453_;
}
}
}
else
{
uint8_t v___x_454_; 
v___x_454_ = 0;
return v___x_454_;
}
v___jp_441_:
{
size_t v___x_442_; size_t v___x_443_; 
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_439_, v___x_442_);
v_i_439_ = v___x_443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0___boxed(lean_object* v_as_455_, lean_object* v_i_456_, lean_object* v_stop_457_){
_start:
{
size_t v_i_boxed_458_; size_t v_stop_boxed_459_; uint8_t v_res_460_; lean_object* v_r_461_; 
v_i_boxed_458_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_stop_boxed_459_ = lean_unbox_usize(v_stop_457_);
lean_dec(v_stop_457_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0(v_as_455_, v_i_boxed_458_, v_stop_boxed_459_);
lean_dec_ref(v_as_455_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobResult_isCanceled___redArg(lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
uint8_t v___x_463_; 
v___x_463_ = 0;
return v___x_463_;
}
else
{
lean_object* v_a_464_; lean_object* v_log_465_; uint8_t v___x_466_; uint8_t v___x_467_; uint8_t v___x_468_; 
v_a_464_ = lean_ctor_get(v_x_462_, 1);
v_log_465_ = lean_ctor_get(v_a_464_, 0);
v___x_466_ = l_Lake_Log_maxLv(v_log_465_);
v___x_467_ = 3;
v___x_468_ = l_Lake_instOrdLogLevel_ord(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_get_size(v_log_465_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_470_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_JobResult_isCanceled_spec__0(v_log_465_, v___x_472_, v___x_473_);
return v___x_474_;
}
}
}
else
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___redArg___boxed(lean_object* v_x_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Lake_JobResult_isCanceled___redArg(v_x_476_);
lean_dec_ref(v_x_476_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobResult_isCanceled(lean_object* v_00_u03b1_479_, lean_object* v_x_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = l_Lake_JobResult_isCanceled___redArg(v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___boxed(lean_object* v_00_u03b1_482_, lean_object* v_x_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Lake_JobResult_isCanceled(v_00_u03b1_482_, v_x_483_);
lean_dec_ref(v_x_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__0(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = l_Lake_instInhabitedJobState_default;
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__1(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__0, &l_Lake_instInhabitedJob___redArg___closed__0_once, _init_l_Lake_instInhabitedJob___redArg___closed__0);
v___x_490_ = lean_task_pure(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__3(void){
_start:
{
uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_492_ = 0;
v___x_493_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_494_ = lean_box(0);
v___x_495_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__1, &l_Lake_instInhabitedJob___redArg___closed__1_once, _init_l_Lake_instInhabitedJob___redArg___closed__1);
v___x_496_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_493_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*3, v___x_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob___redArg(){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__3, &l_Lake_instInhabitedJob___redArg___closed__3_once, _init_l_Lake_instInhabitedJob___redArg___closed__3);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob___redArg___boxed(lean_object* v___dummy_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lake_instInhabitedJob___redArg();
return v_res_500_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lake_instInhabitedJob___redArg();
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_504_){
_start:
{
lean_inc_ref(v_self_504_);
return v_self_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lake_Job_cast___redArg(v_self_505_);
lean_dec_ref(v_self_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_507_, lean_object* v_self_508_, lean_object* v_h_509_){
_start:
{
lean_inc_ref(v_self_508_);
return v_self_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_510_, lean_object* v_self_511_, lean_object* v_h_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_Job_cast(v_00_u03b1_510_, v_self_511_, v_h_512_);
lean_dec_ref(v_self_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_514_, lean_object* v_task_515_, lean_object* v_caption_516_){
_start:
{
uint8_t v___x_517_; lean_object* v___x_518_; 
v___x_517_ = 0;
v___x_518_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_518_, 0, v_task_515_);
lean_ctor_set(v___x_518_, 1, v_inst_514_);
lean_ctor_set(v___x_518_, 2, v_caption_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*3, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_519_, lean_object* v_inst_520_, lean_object* v_task_521_, lean_object* v_caption_522_){
_start:
{
uint8_t v___x_523_; lean_object* v___x_524_; 
v___x_523_ = 0;
v___x_524_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_524_, 0, v_task_521_);
lean_ctor_set(v___x_524_, 1, v_inst_520_);
lean_ctor_set(v___x_524_, 2, v_caption_522_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*3, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_525_, lean_object* v_log_526_, lean_object* v_caption_527_){
_start:
{
lean_object* v___x_528_; uint8_t v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = 0;
v___x_530_ = 0;
v___x_531_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_532_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_532_, 0, v_log_526_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
lean_ctor_set(v___x_532_, 2, v___x_528_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*3, v___x_529_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*3 + 1, v___x_530_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_528_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_task_pure(v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v_inst_525_);
lean_ctor_set(v___x_535_, 2, v_caption_527_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*3, v___x_530_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_536_, lean_object* v_inst_537_, lean_object* v_log_538_, lean_object* v_caption_539_){
_start:
{
lean_object* v___x_540_; uint8_t v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = 0;
v___x_542_ = 0;
v___x_543_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_544_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_544_, 0, v_log_538_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
lean_ctor_set(v___x_544_, 2, v___x_540_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*3, v___x_541_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*3 + 1, v___x_542_);
v___x_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_540_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_task_pure(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v_inst_537_);
lean_ctor_set(v___x_547_, 2, v_caption_539_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*3, v___x_542_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_548_, lean_object* v_a_549_, lean_object* v_log_550_, lean_object* v_caption_551_){
_start:
{
uint8_t v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_552_ = 0;
v___x_553_ = 0;
v___x_554_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_556_, 0, v_log_550_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*3, v___x_552_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*3 + 1, v___x_553_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v_a_549_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_task_pure(v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_kind_548_);
lean_ctor_set(v___x_559_, 2, v_caption_551_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*3, v___x_553_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_560_, lean_object* v_kind_561_, lean_object* v_a_562_, lean_object* v_log_563_, lean_object* v_caption_564_){
_start:
{
uint8_t v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_565_ = 0;
v___x_566_ = 0;
v___x_567_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_569_, 0, v_log_563_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_568_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*3, v___x_565_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*3 + 1, v___x_566_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_a_562_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_task_pure(v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_kind_561_);
lean_ctor_set(v___x_572_, 2, v_caption_564_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*3, v___x_566_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_575_ = lean_box(0);
v___x_576_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_577_ = 0;
v___x_578_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_574_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_task_pure(v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_575_);
lean_ctor_set(v___x_581_, 2, v___x_576_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*3, v___x_577_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_584_, lean_object* v_caption_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_586_ = lean_box(0);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_589_ = 0;
v___x_590_ = 0;
v___x_591_ = l_Lake_BuildTrace_nil(v_caption_585_);
v___x_592_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_592_, 0, v___x_588_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
lean_ctor_set(v___x_592_, 2, v___x_587_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3, v___x_589_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3 + 1, v___x_590_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_a_584_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_task_pure(v___x_593_);
v___x_595_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_596_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_586_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*3, v___x_590_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_597_, lean_object* v_a_598_, lean_object* v_caption_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_603_ = 0;
v___x_604_ = 0;
v___x_605_ = l_Lake_BuildTrace_nil(v_caption_599_);
v___x_606_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_606_, 0, v___x_602_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
lean_ctor_set(v___x_606_, 2, v___x_601_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*3, v___x_603_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*3 + 1, v___x_604_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v_a_598_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_task_pure(v___x_607_);
v___x_609_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_610_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_600_);
lean_ctor_set(v___x_610_, 2, v___x_609_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*3, v___x_604_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_611_, lean_object* v_caption_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_613_ = l_Lake_instDataKindUnit;
v___x_614_ = lean_box(0);
v___x_615_ = 0;
v___x_616_ = 0;
v___x_617_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_619_, 0, v_log_611_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_618_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 1, v___x_616_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_614_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_task_pure(v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___x_613_);
lean_ctor_set(v___x_622_, 2, v_caption_612_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*3, v___x_616_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_box(0);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_628_ = 0;
v___x_629_ = 0;
v___x_630_ = l_Lake_BuildTrace_nil(v_traceCaption_623_);
v___x_631_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_631_, 0, v___x_627_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
lean_ctor_set(v___x_631_, 2, v___x_626_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3, v___x_628_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 1, v___x_629_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_624_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_task_pure(v___x_632_);
v___x_634_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_635_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_625_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*3, v___x_629_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_636_){
_start:
{
lean_object* v_task_637_; lean_object* v___x_638_; lean_object* v_a_639_; lean_object* v_trace_640_; 
v_task_637_ = lean_ctor_get(v_job_636_, 0);
lean_inc_ref(v_task_637_);
lean_dec_ref(v_job_636_);
v___x_638_ = lean_task_get_own(v_task_637_);
v_a_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v_trace_640_ = lean_ctor_get(v_a_639_, 1);
lean_inc_ref(v_trace_640_);
lean_dec(v_a_639_);
return v_trace_640_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_641_, lean_object* v_job_642_){
_start:
{
lean_object* v_task_643_; lean_object* v___x_644_; lean_object* v_a_645_; lean_object* v_trace_646_; 
v_task_643_ = lean_ctor_get(v_job_642_, 0);
lean_inc_ref(v_task_643_);
lean_dec_ref(v_job_642_);
v___x_644_ = lean_task_get_own(v_task_643_);
v_a_645_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v_trace_646_ = lean_ctor_get(v_a_645_, 1);
lean_inc_ref(v_trace_646_);
lean_dec(v_a_645_);
return v_trace_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_647_, lean_object* v_job_648_){
_start:
{
lean_object* v_task_649_; lean_object* v_kind_650_; uint8_t v_optional_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_task_649_ = lean_ctor_get(v_job_648_, 0);
v_kind_650_ = lean_ctor_get(v_job_648_, 1);
v_optional_651_ = lean_ctor_get_uint8(v_job_648_, sizeof(void*)*3);
v_isSharedCheck_658_ = !lean_is_exclusive(v_job_648_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_job_648_, 2);
lean_dec(v_unused_659_);
v___x_653_ = v_job_648_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_kind_650_);
lean_inc(v_task_649_);
lean_dec(v_job_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 2, v_caption_647_);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_task_649_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_kind_650_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_caption_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_657_, sizeof(void*)*3, v_optional_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_660_, lean_object* v_caption_661_, lean_object* v_job_662_){
_start:
{
lean_object* v_task_663_; lean_object* v_kind_664_; uint8_t v_optional_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_task_663_ = lean_ctor_get(v_job_662_, 0);
v_kind_664_ = lean_ctor_get(v_job_662_, 1);
v_optional_665_ = lean_ctor_get_uint8(v_job_662_, sizeof(void*)*3);
v_isSharedCheck_672_ = !lean_is_exclusive(v_job_662_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_job_662_, 2);
lean_dec(v_unused_673_);
v___x_667_ = v_job_662_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_kind_664_);
lean_inc(v_task_663_);
lean_dec(v_job_662_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 2, v_caption_661_);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_task_663_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_kind_664_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_caption_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_671_, sizeof(void*)*3, v_optional_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_674_, lean_object* v_job_675_){
_start:
{
lean_object* v_task_676_; lean_object* v_kind_677_; lean_object* v_caption_678_; uint8_t v_optional_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_task_676_ = lean_ctor_get(v_job_675_, 0);
v_kind_677_ = lean_ctor_get(v_job_675_, 1);
v_caption_678_ = lean_ctor_get(v_job_675_, 2);
v_optional_679_ = lean_ctor_get_uint8(v_job_675_, sizeof(void*)*3);
v___x_680_ = lean_string_utf8_byte_size(v_caption_678_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_nat_dec_eq(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_dec_ref(v_caption_674_);
return v_job_675_;
}
else
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_inc(v_kind_677_);
lean_inc_ref(v_task_676_);
v_isSharedCheck_689_ = !lean_is_exclusive(v_job_675_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; lean_object* v_unused_691_; lean_object* v_unused_692_; 
v_unused_690_ = lean_ctor_get(v_job_675_, 2);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_job_675_, 1);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_job_675_, 0);
lean_dec(v_unused_692_);
v___x_684_ = v_job_675_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_job_675_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 2, v_caption_674_);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_task_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_kind_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_caption_674_);
lean_ctor_set_uint8(v_reuseFailAlloc_688_, sizeof(void*)*3, v_optional_679_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_693_, lean_object* v_caption_694_, lean_object* v_job_695_){
_start:
{
lean_object* v_task_696_; lean_object* v_kind_697_; lean_object* v_caption_698_; uint8_t v_optional_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_task_696_ = lean_ctor_get(v_job_695_, 0);
v_kind_697_ = lean_ctor_get(v_job_695_, 1);
v_caption_698_ = lean_ctor_get(v_job_695_, 2);
v_optional_699_ = lean_ctor_get_uint8(v_job_695_, sizeof(void*)*3);
v___x_700_ = lean_string_utf8_byte_size(v_caption_698_);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_nat_dec_eq(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec_ref(v_caption_694_);
return v_job_695_;
}
else
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_inc(v_kind_697_);
lean_inc_ref(v_task_696_);
v_isSharedCheck_709_ = !lean_is_exclusive(v_job_695_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; 
v_unused_710_ = lean_ctor_get(v_job_695_, 2);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_job_695_, 1);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_job_695_, 0);
lean_dec(v_unused_712_);
v___x_704_ = v_job_695_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_job_695_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 2, v_caption_694_);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_task_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_kind_697_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_caption_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3, v_optional_699_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_713_, lean_object* v_f_714_, lean_object* v_self_715_, lean_object* v_prio_716_, uint8_t v_sync_717_){
_start:
{
lean_object* v_task_718_; lean_object* v_caption_719_; uint8_t v_optional_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
v_task_718_ = lean_ctor_get(v_self_715_, 0);
v_caption_719_ = lean_ctor_get(v_self_715_, 2);
v_optional_720_ = lean_ctor_get_uint8(v_self_715_, sizeof(void*)*3);
v_isSharedCheck_728_ = !lean_is_exclusive(v_self_715_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v_self_715_, 1);
lean_dec(v_unused_729_);
v___x_722_ = v_self_715_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_caption_719_);
lean_inc(v_task_718_);
lean_dec(v_self_715_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_task_map(v_f_714_, v_task_718_, v_prio_716_, v_sync_717_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v_inst_713_);
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_inst_713_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_caption_719_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*3, v_optional_720_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_730_, lean_object* v_f_731_, lean_object* v_self_732_, lean_object* v_prio_733_, lean_object* v_sync_734_){
_start:
{
uint8_t v_sync_boxed_735_; lean_object* v_res_736_; 
v_sync_boxed_735_ = lean_unbox(v_sync_734_);
v_res_736_ = l_Lake_Job_mapResult___redArg(v_inst_730_, v_f_731_, v_self_732_, v_prio_733_, v_sync_boxed_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_737_, lean_object* v_00_u03b1_738_, lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_self_741_, lean_object* v_prio_742_, uint8_t v_sync_743_){
_start:
{
lean_object* v_task_744_; lean_object* v_caption_745_; uint8_t v_optional_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_task_744_ = lean_ctor_get(v_self_741_, 0);
v_caption_745_ = lean_ctor_get(v_self_741_, 2);
v_optional_746_ = lean_ctor_get_uint8(v_self_741_, sizeof(void*)*3);
v_isSharedCheck_754_ = !lean_is_exclusive(v_self_741_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_self_741_, 1);
lean_dec(v_unused_755_);
v___x_748_ = v_self_741_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_caption_745_);
lean_inc(v_task_744_);
lean_dec(v_self_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_task_map(v_f_740_, v_task_744_, v_prio_742_, v_sync_743_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v_inst_739_);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_inst_739_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_caption_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*3, v_optional_746_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_756_, lean_object* v_00_u03b1_757_, lean_object* v_inst_758_, lean_object* v_f_759_, lean_object* v_self_760_, lean_object* v_prio_761_, lean_object* v_sync_762_){
_start:
{
uint8_t v_sync_boxed_763_; lean_object* v_res_764_; 
v_sync_boxed_763_ = lean_unbox(v_sync_762_);
v_res_764_ = l_Lake_Job_mapResult(v_00_u03b2_756_, v_00_u03b1_757_, v_inst_758_, v_f_759_, v_self_760_, v_prio_761_, v_sync_boxed_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v_a_768_; lean_object* v___x_769_; 
v_a_767_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_a_767_);
v_a_768_ = lean_ctor_get(v_x_766_, 1);
lean_inc(v_a_768_);
lean_dec_ref_known(v_x_766_, 2);
v___x_769_ = lean_apply_2(v_f_765_, v_a_767_, v_a_768_);
return v___x_769_;
}
else
{
lean_object* v_a_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_f_765_);
v_a_770_ = lean_ctor_get(v_x_766_, 0);
v_a_771_ = lean_ctor_get(v_x_766_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v_x_766_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_inc(v_a_770_);
lean_dec(v_x_766_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_770_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_779_, lean_object* v_f_780_, lean_object* v_self_781_, lean_object* v_prio_782_, uint8_t v_sync_783_){
_start:
{
lean_object* v_task_784_; lean_object* v_caption_785_; uint8_t v_optional_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_795_; 
v_task_784_ = lean_ctor_get(v_self_781_, 0);
v_caption_785_ = lean_ctor_get(v_self_781_, 2);
v_optional_786_ = lean_ctor_get_uint8(v_self_781_, sizeof(void*)*3);
v_isSharedCheck_795_ = !lean_is_exclusive(v_self_781_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_self_781_, 1);
lean_dec(v_unused_796_);
v___x_788_ = v_self_781_;
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_caption_785_);
lean_inc(v_task_784_);
lean_dec(v_self_781_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___f_790_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_790_, 0, v_f_780_);
v___x_791_ = lean_task_map(v___f_790_, v_task_784_, v_prio_782_, v_sync_783_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_inst_779_);
lean_ctor_set(v___x_788_, 0, v___x_791_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_inst_779_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_caption_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_794_, sizeof(void*)*3, v_optional_786_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* v_inst_797_, lean_object* v_f_798_, lean_object* v_self_799_, lean_object* v_prio_800_, lean_object* v_sync_801_){
_start:
{
uint8_t v_sync_boxed_802_; lean_object* v_res_803_; 
v_sync_boxed_802_ = lean_unbox(v_sync_801_);
v_res_803_ = l_Lake_Job_mapOk___redArg(v_inst_797_, v_f_798_, v_self_799_, v_prio_800_, v_sync_boxed_802_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_804_, lean_object* v_00_u03b1_805_, lean_object* v_inst_806_, lean_object* v_f_807_, lean_object* v_self_808_, lean_object* v_prio_809_, uint8_t v_sync_810_){
_start:
{
lean_object* v_task_811_; lean_object* v_caption_812_; uint8_t v_optional_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_task_811_ = lean_ctor_get(v_self_808_, 0);
v_caption_812_ = lean_ctor_get(v_self_808_, 2);
v_optional_813_ = lean_ctor_get_uint8(v_self_808_, sizeof(void*)*3);
v_isSharedCheck_822_ = !lean_is_exclusive(v_self_808_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_self_808_, 1);
lean_dec(v_unused_823_);
v___x_815_ = v_self_808_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_caption_812_);
lean_inc(v_task_811_);
lean_dec(v_self_808_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___f_817_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_817_, 0, v_f_807_);
v___x_818_ = lean_task_map(v___f_817_, v_task_811_, v_prio_809_, v_sync_810_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v_inst_806_);
lean_ctor_set(v___x_815_, 0, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_inst_806_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_caption_812_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, sizeof(void*)*3, v_optional_813_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_824_, lean_object* v_00_u03b1_825_, lean_object* v_inst_826_, lean_object* v_f_827_, lean_object* v_self_828_, lean_object* v_prio_829_, lean_object* v_sync_830_){
_start:
{
uint8_t v_sync_boxed_831_; lean_object* v_res_832_; 
v_sync_boxed_831_ = lean_unbox(v_sync_830_);
v_res_832_ = l_Lake_Job_mapOk(v_00_u03b2_824_, v_00_u03b1_825_, v_inst_826_, v_f_827_, v_self_828_, v_prio_829_, v_sync_boxed_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_844_; 
v_a_835_ = lean_ctor_get(v_x_834_, 0);
v_a_836_ = lean_ctor_get(v_x_834_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_834_);
if (v_isSharedCheck_844_ == 0)
{
v___x_838_ = v_x_834_;
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_inc(v_a_835_);
lean_dec(v_x_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = lean_apply_1(v_f_833_, v_a_835_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_a_836_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_f_833_);
v_a_845_ = lean_ctor_get(v_x_834_, 0);
v_a_846_ = lean_ctor_get(v_x_834_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_x_834_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v_x_834_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_inc(v_a_845_);
lean_dec(v_x_834_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_845_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_854_, lean_object* v_f_855_, lean_object* v_self_856_, lean_object* v_prio_857_, uint8_t v_sync_858_){
_start:
{
lean_object* v_task_859_; lean_object* v_caption_860_; uint8_t v_optional_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_870_; 
v_task_859_ = lean_ctor_get(v_self_856_, 0);
v_caption_860_ = lean_ctor_get(v_self_856_, 2);
v_optional_861_ = lean_ctor_get_uint8(v_self_856_, sizeof(void*)*3);
v_isSharedCheck_870_ = !lean_is_exclusive(v_self_856_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_self_856_, 1);
lean_dec(v_unused_871_);
v___x_863_ = v_self_856_;
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_caption_860_);
lean_inc(v_task_859_);
lean_dec(v_self_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___f_865_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_865_, 0, v_f_855_);
v___x_866_ = lean_task_map(v___f_865_, v_task_859_, v_prio_857_, v_sync_858_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_inst_854_);
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_inst_854_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_caption_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, sizeof(void*)*3, v_optional_861_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_872_, lean_object* v_f_873_, lean_object* v_self_874_, lean_object* v_prio_875_, lean_object* v_sync_876_){
_start:
{
uint8_t v_sync_boxed_877_; lean_object* v_res_878_; 
v_sync_boxed_877_ = lean_unbox(v_sync_876_);
v_res_878_ = l_Lake_Job_map___redArg(v_inst_872_, v_f_873_, v_self_874_, v_prio_875_, v_sync_boxed_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_879_, lean_object* v_00_u03b1_880_, lean_object* v_inst_881_, lean_object* v_f_882_, lean_object* v_self_883_, lean_object* v_prio_884_, uint8_t v_sync_885_){
_start:
{
lean_object* v_task_886_; lean_object* v_caption_887_; uint8_t v_optional_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_897_; 
v_task_886_ = lean_ctor_get(v_self_883_, 0);
v_caption_887_ = lean_ctor_get(v_self_883_, 2);
v_optional_888_ = lean_ctor_get_uint8(v_self_883_, sizeof(void*)*3);
v_isSharedCheck_897_ = !lean_is_exclusive(v_self_883_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v_self_883_, 1);
lean_dec(v_unused_898_);
v___x_890_ = v_self_883_;
v_isShared_891_ = v_isSharedCheck_897_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_caption_887_);
lean_inc(v_task_886_);
lean_dec(v_self_883_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_897_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___f_892_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_892_, 0, v_f_882_);
v___x_893_ = lean_task_map(v___f_892_, v_task_886_, v_prio_884_, v_sync_885_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_inst_881_);
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_inst_881_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_caption_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_896_, sizeof(void*)*3, v_optional_888_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_899_, lean_object* v_00_u03b1_900_, lean_object* v_inst_901_, lean_object* v_f_902_, lean_object* v_self_903_, lean_object* v_prio_904_, lean_object* v_sync_905_){
_start:
{
uint8_t v_sync_boxed_906_; lean_object* v_res_907_; 
v_sync_boxed_906_ = lean_unbox(v_sync_905_);
v_res_907_ = l_Lake_Job_map(v_00_u03b2_899_, v_00_u03b1_900_, v_inst_901_, v_f_902_, v_self_903_, v_prio_904_, v_sync_boxed_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_908_, lean_object* v_00_u03b2_909_, lean_object* v_f_910_, lean_object* v_self_911_){
_start:
{
lean_object* v_task_912_; lean_object* v_caption_913_; uint8_t v_optional_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_926_; 
v_task_912_ = lean_ctor_get(v_self_911_, 0);
v_caption_913_ = lean_ctor_get(v_self_911_, 2);
v_optional_914_ = lean_ctor_get_uint8(v_self_911_, sizeof(void*)*3);
v_isSharedCheck_926_ = !lean_is_exclusive(v_self_911_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_self_911_, 1);
lean_dec(v_unused_927_);
v___x_916_ = v_self_911_;
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_caption_913_);
lean_inc(v_task_912_);
lean_dec(v_self_911_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___f_918_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_918_, 0, v_f_910_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = 0;
v___x_922_ = lean_task_map(v___f_918_, v_task_912_, v___x_920_, v___x_921_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v___x_919_);
lean_ctor_set(v___x_916_, 0, v___x_922_);
v___x_924_ = v___x_916_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_caption_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*3, v_optional_914_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_928_, lean_object* v_00_u03b1_929_, lean_object* v_00_u03b2_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_933_, 0, lean_box(0));
lean_closure_set(v___x_933_, 1, lean_box(0));
lean_closure_set(v___x_933_, 2, v___y_931_);
v___x_934_ = lean_apply_4(v___f_928_, lean_box(0), lean_box(0), v___x_933_, v___y_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_942_){
_start:
{
lean_inc_ref(v_self_942_);
return v_self_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_943_);
lean_dec_ref(v_self_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_945_, lean_object* v_self_946_){
_start:
{
lean_inc_ref(v_self_946_);
return v_self_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_947_, lean_object* v_self_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_947_, v_self_948_);
lean_dec_ref(v_self_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg(){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0));
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___boxed(lean_object* v___dummy_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg();
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0));
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_957_){
_start:
{
lean_object* v_task_958_; lean_object* v_caption_959_; uint8_t v_optional_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_task_958_ = lean_ctor_get(v_job_957_, 0);
v_caption_959_ = lean_ctor_get(v_job_957_, 2);
v_optional_960_ = lean_ctor_get_uint8(v_job_957_, sizeof(void*)*3);
v_isSharedCheck_968_ = !lean_is_exclusive(v_job_957_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_job_957_, 1);
lean_dec(v_unused_969_);
v___x_962_ = v_job_957_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_caption_959_);
lean_inc(v_task_958_);
lean_dec(v_job_957_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_box(0);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_task_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_caption_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3, v_optional_960_);
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
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_970_, lean_object* v_job_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lake_Job_toOpaque___redArg(v_job_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg(){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0));
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg___boxed(lean_object* v___dummy_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lake_instCoeOutJobOpaqueJob___redArg();
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* v_00_u03b1_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0));
return v___x_979_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Task(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Opaque(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Trace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Job_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedJobAction_default = _init_l_Lake_instInhabitedJobAction_default();
l_Lake_instInhabitedJobAction = _init_l_Lake_instInhabitedJobAction();
l_Lake_JobAction_instLT = _init_l_Lake_JobAction_instLT();
lean_mark_persistent(l_Lake_JobAction_instLT);
l_Lake_JobAction_instLE = _init_l_Lake_JobAction_instLE();
lean_mark_persistent(l_Lake_JobAction_instLE);
l_Lake_instInhabitedJobState_default = _init_l_Lake_instInhabitedJobState_default();
lean_mark_persistent(l_Lake_instInhabitedJobState_default);
l_Lake_instInhabitedJobState = _init_l_Lake_instInhabitedJobState();
lean_mark_persistent(l_Lake_instInhabitedJobState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Job_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Util_Task(uint8_t builtin);
lean_object* initialize_Lake_Util_Opaque(uint8_t builtin);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin);
lean_object* initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Job_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
