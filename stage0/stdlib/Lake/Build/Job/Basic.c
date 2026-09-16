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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
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
static lean_once_cell_t l_Lake_instInhabitedJob___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJob___closed__0;
static lean_once_cell_t l_Lake_instInhabitedJob___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJob___closed__1;
static const lean_string_object l_Lake_instInhabitedJob___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedJob___closed__2 = (const lean_object*)&l_Lake_instInhabitedJob___closed__2_value;
static lean_once_cell_t l_Lake_instInhabitedJob___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJob___closed__3;
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
static const lean_closure_object l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0 = (const lean_object*)&l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instCoeOutJobOpaqueJob___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Job_toOpaque, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instCoeOutJobOpaqueJob___closed__0 = (const lean_object*)&l_Lake_instCoeOutJobOpaqueJob___closed__0_value;
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
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
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
static lean_object* _init_l_Lake_instInhabitedJob___closed__1(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
v___x_490_ = lean_task_pure(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__3(void){
_start:
{
uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_492_ = 0;
v___x_493_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_494_ = lean_box(0);
v___x_495_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__1, &l_Lake_instInhabitedJob___closed__1_once, _init_l_Lake_instInhabitedJob___closed__1);
v___x_496_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_493_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*3, v___x_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__3, &l_Lake_instInhabitedJob___closed__3_once, _init_l_Lake_instInhabitedJob___closed__3);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_499_){
_start:
{
lean_inc_ref(v_self_499_);
return v_self_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lake_Job_cast___redArg(v_self_500_);
lean_dec_ref(v_self_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_502_, lean_object* v_self_503_, lean_object* v_h_504_){
_start:
{
lean_inc_ref(v_self_503_);
return v_self_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_505_, lean_object* v_self_506_, lean_object* v_h_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lake_Job_cast(v_00_u03b1_505_, v_self_506_, v_h_507_);
lean_dec_ref(v_self_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_509_, lean_object* v_task_510_, lean_object* v_caption_511_){
_start:
{
uint8_t v___x_512_; lean_object* v___x_513_; 
v___x_512_ = 0;
v___x_513_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_513_, 0, v_task_510_);
lean_ctor_set(v___x_513_, 1, v_inst_509_);
lean_ctor_set(v___x_513_, 2, v_caption_511_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*3, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_514_, lean_object* v_inst_515_, lean_object* v_task_516_, lean_object* v_caption_517_){
_start:
{
uint8_t v___x_518_; lean_object* v___x_519_; 
v___x_518_ = 0;
v___x_519_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_519_, 0, v_task_516_);
lean_ctor_set(v___x_519_, 1, v_inst_515_);
lean_ctor_set(v___x_519_, 2, v_caption_517_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*3, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_520_, lean_object* v_log_521_, lean_object* v_caption_522_){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = 0;
v___x_525_ = 0;
v___x_526_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_527_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_527_, 0, v_log_521_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_ctor_set(v___x_527_, 2, v___x_523_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*3, v___x_524_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*3 + 1, v___x_525_);
v___x_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_523_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_task_pure(v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v_inst_520_);
lean_ctor_set(v___x_530_, 2, v_caption_522_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*3, v___x_525_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_531_, lean_object* v_inst_532_, lean_object* v_log_533_, lean_object* v_caption_534_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = 0;
v___x_537_ = 0;
v___x_538_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_539_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_539_, 0, v_log_533_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_ctor_set(v___x_539_, 2, v___x_535_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*3, v___x_536_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*3 + 1, v___x_537_);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_535_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_task_pure(v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_inst_532_);
lean_ctor_set(v___x_542_, 2, v_caption_534_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*3, v___x_537_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_543_, lean_object* v_a_544_, lean_object* v_log_545_, lean_object* v_caption_546_){
_start:
{
uint8_t v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_547_ = 0;
v___x_548_ = 0;
v___x_549_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_551_, 0, v_log_545_);
lean_ctor_set(v___x_551_, 1, v___x_549_);
lean_ctor_set(v___x_551_, 2, v___x_550_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*3, v___x_547_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*3 + 1, v___x_548_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_a_544_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_task_pure(v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_kind_543_);
lean_ctor_set(v___x_554_, 2, v_caption_546_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*3, v___x_548_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_555_, lean_object* v_kind_556_, lean_object* v_a_557_, lean_object* v_log_558_, lean_object* v_caption_559_){
_start:
{
uint8_t v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_560_ = 0;
v___x_561_ = 0;
v___x_562_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_564_, 0, v_log_558_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
lean_ctor_set(v___x_564_, 2, v___x_563_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3, v___x_560_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3 + 1, v___x_561_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_a_557_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_task_pure(v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_kind_556_);
lean_ctor_set(v___x_567_, 2, v_caption_559_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3, v___x_561_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_570_ = lean_box(0);
v___x_571_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_572_ = 0;
v___x_573_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_a_569_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_task_pure(v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_570_);
lean_ctor_set(v___x_576_, 2, v___x_571_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*3, v___x_572_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_579_, lean_object* v_caption_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_581_ = lean_box(0);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_584_ = 0;
v___x_585_ = 0;
v___x_586_ = l_Lake_BuildTrace_nil(v_caption_580_);
v___x_587_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_587_, 0, v___x_583_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
lean_ctor_set(v___x_587_, 2, v___x_582_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*3, v___x_584_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*3 + 1, v___x_585_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_a_579_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_task_pure(v___x_588_);
v___x_590_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_591_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_581_);
lean_ctor_set(v___x_591_, 2, v___x_590_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*3, v___x_585_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_592_, lean_object* v_a_593_, lean_object* v_caption_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_598_ = 0;
v___x_599_ = 0;
v___x_600_ = l_Lake_BuildTrace_nil(v_caption_594_);
v___x_601_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_601_, 0, v___x_597_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_ctor_set(v___x_601_, 2, v___x_596_);
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*3, v___x_598_);
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*3 + 1, v___x_599_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_a_593_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_task_pure(v___x_602_);
v___x_604_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_605_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_595_);
lean_ctor_set(v___x_605_, 2, v___x_604_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*3, v___x_599_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_606_, lean_object* v_caption_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_608_ = l_Lake_instDataKindUnit;
v___x_609_ = lean_box(0);
v___x_610_ = 0;
v___x_611_ = 0;
v___x_612_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_614_, 0, v_log_606_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_613_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*3, v___x_610_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*3 + 1, v___x_611_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_609_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_task_pure(v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_608_);
lean_ctor_set(v___x_617_, 2, v_caption_607_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3, v___x_611_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_619_ = lean_box(0);
v___x_620_ = lean_box(0);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_623_ = 0;
v___x_624_ = 0;
v___x_625_ = l_Lake_BuildTrace_nil(v_traceCaption_618_);
v___x_626_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_626_, 0, v___x_622_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
lean_ctor_set(v___x_626_, 2, v___x_621_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*3, v___x_623_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*3 + 1, v___x_624_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_619_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_task_pure(v___x_627_);
v___x_629_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_630_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_620_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*3, v___x_624_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_631_){
_start:
{
lean_object* v_task_632_; lean_object* v___x_633_; lean_object* v_a_634_; lean_object* v_trace_635_; 
v_task_632_ = lean_ctor_get(v_job_631_, 0);
lean_inc_ref(v_task_632_);
lean_dec_ref(v_job_631_);
v___x_633_ = lean_task_get_own(v_task_632_);
v_a_634_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v_trace_635_ = lean_ctor_get(v_a_634_, 1);
lean_inc_ref(v_trace_635_);
lean_dec(v_a_634_);
return v_trace_635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_636_, lean_object* v_job_637_){
_start:
{
lean_object* v_task_638_; lean_object* v___x_639_; lean_object* v_a_640_; lean_object* v_trace_641_; 
v_task_638_ = lean_ctor_get(v_job_637_, 0);
lean_inc_ref(v_task_638_);
lean_dec_ref(v_job_637_);
v___x_639_ = lean_task_get_own(v_task_638_);
v_a_640_ = lean_ctor_get(v___x_639_, 1);
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v_trace_641_ = lean_ctor_get(v_a_640_, 1);
lean_inc_ref(v_trace_641_);
lean_dec(v_a_640_);
return v_trace_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_642_, lean_object* v_job_643_){
_start:
{
lean_object* v_task_644_; lean_object* v_kind_645_; uint8_t v_optional_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
v_task_644_ = lean_ctor_get(v_job_643_, 0);
v_kind_645_ = lean_ctor_get(v_job_643_, 1);
v_optional_646_ = lean_ctor_get_uint8(v_job_643_, sizeof(void*)*3);
v_isSharedCheck_653_ = !lean_is_exclusive(v_job_643_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_job_643_, 2);
lean_dec(v_unused_654_);
v___x_648_ = v_job_643_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_kind_645_);
lean_inc(v_task_644_);
lean_dec(v_job_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v_caption_642_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_task_644_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_kind_645_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_caption_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_652_, sizeof(void*)*3, v_optional_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_655_, lean_object* v_caption_656_, lean_object* v_job_657_){
_start:
{
lean_object* v_task_658_; lean_object* v_kind_659_; uint8_t v_optional_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_task_658_ = lean_ctor_get(v_job_657_, 0);
v_kind_659_ = lean_ctor_get(v_job_657_, 1);
v_optional_660_ = lean_ctor_get_uint8(v_job_657_, sizeof(void*)*3);
v_isSharedCheck_667_ = !lean_is_exclusive(v_job_657_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_job_657_, 2);
lean_dec(v_unused_668_);
v___x_662_ = v_job_657_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_kind_659_);
lean_inc(v_task_658_);
lean_dec(v_job_657_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 2, v_caption_656_);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_task_658_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_kind_659_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_caption_656_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3, v_optional_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_669_, lean_object* v_job_670_){
_start:
{
lean_object* v_task_671_; lean_object* v_kind_672_; lean_object* v_caption_673_; uint8_t v_optional_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_task_671_ = lean_ctor_get(v_job_670_, 0);
v_kind_672_ = lean_ctor_get(v_job_670_, 1);
v_caption_673_ = lean_ctor_get(v_job_670_, 2);
v_optional_674_ = lean_ctor_get_uint8(v_job_670_, sizeof(void*)*3);
v___x_675_ = lean_string_utf8_byte_size(v_caption_673_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_nat_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v_caption_669_);
return v_job_670_;
}
else
{
lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_inc(v_kind_672_);
lean_inc_ref(v_task_671_);
v_isSharedCheck_684_ = !lean_is_exclusive(v_job_670_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; lean_object* v_unused_686_; lean_object* v_unused_687_; 
v_unused_685_ = lean_ctor_get(v_job_670_, 2);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_job_670_, 1);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_job_670_, 0);
lean_dec(v_unused_687_);
v___x_679_ = v_job_670_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_dec(v_job_670_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 2, v_caption_669_);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_task_671_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_kind_672_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_caption_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_683_, sizeof(void*)*3, v_optional_674_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_688_, lean_object* v_caption_689_, lean_object* v_job_690_){
_start:
{
lean_object* v_task_691_; lean_object* v_kind_692_; lean_object* v_caption_693_; uint8_t v_optional_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_task_691_ = lean_ctor_get(v_job_690_, 0);
v_kind_692_ = lean_ctor_get(v_job_690_, 1);
v_caption_693_ = lean_ctor_get(v_job_690_, 2);
v_optional_694_ = lean_ctor_get_uint8(v_job_690_, sizeof(void*)*3);
v___x_695_ = lean_string_utf8_byte_size(v_caption_693_);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_caption_689_);
return v_job_690_;
}
else
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_inc(v_kind_692_);
lean_inc_ref(v_task_691_);
v_isSharedCheck_704_ = !lean_is_exclusive(v_job_690_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; 
v_unused_705_ = lean_ctor_get(v_job_690_, 2);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_job_690_, 1);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_job_690_, 0);
lean_dec(v_unused_707_);
v___x_699_ = v_job_690_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_dec(v_job_690_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 2, v_caption_689_);
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_task_691_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_kind_692_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_caption_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_703_, sizeof(void*)*3, v_optional_694_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_708_, lean_object* v_f_709_, lean_object* v_self_710_, lean_object* v_prio_711_, uint8_t v_sync_712_){
_start:
{
lean_object* v_task_713_; lean_object* v_caption_714_; uint8_t v_optional_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_task_713_ = lean_ctor_get(v_self_710_, 0);
v_caption_714_ = lean_ctor_get(v_self_710_, 2);
v_optional_715_ = lean_ctor_get_uint8(v_self_710_, sizeof(void*)*3);
v_isSharedCheck_723_ = !lean_is_exclusive(v_self_710_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v_self_710_, 1);
lean_dec(v_unused_724_);
v___x_717_ = v_self_710_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_caption_714_);
lean_inc(v_task_713_);
lean_dec(v_self_710_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_task_map(v_f_709_, v_task_713_, v_prio_711_, v_sync_712_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v_inst_708_);
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_inst_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_caption_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*3, v_optional_715_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_725_, lean_object* v_f_726_, lean_object* v_self_727_, lean_object* v_prio_728_, lean_object* v_sync_729_){
_start:
{
uint8_t v_sync_boxed_730_; lean_object* v_res_731_; 
v_sync_boxed_730_ = lean_unbox(v_sync_729_);
v_res_731_ = l_Lake_Job_mapResult___redArg(v_inst_725_, v_f_726_, v_self_727_, v_prio_728_, v_sync_boxed_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_732_, lean_object* v_00_u03b1_733_, lean_object* v_inst_734_, lean_object* v_f_735_, lean_object* v_self_736_, lean_object* v_prio_737_, uint8_t v_sync_738_){
_start:
{
lean_object* v_task_739_; lean_object* v_caption_740_; uint8_t v_optional_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_task_739_ = lean_ctor_get(v_self_736_, 0);
v_caption_740_ = lean_ctor_get(v_self_736_, 2);
v_optional_741_ = lean_ctor_get_uint8(v_self_736_, sizeof(void*)*3);
v_isSharedCheck_749_ = !lean_is_exclusive(v_self_736_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_self_736_, 1);
lean_dec(v_unused_750_);
v___x_743_ = v_self_736_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_caption_740_);
lean_inc(v_task_739_);
lean_dec(v_self_736_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_task_map(v_f_735_, v_task_739_, v_prio_737_, v_sync_738_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v_inst_734_);
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_inst_734_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_caption_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_748_, sizeof(void*)*3, v_optional_741_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_751_, lean_object* v_00_u03b1_752_, lean_object* v_inst_753_, lean_object* v_f_754_, lean_object* v_self_755_, lean_object* v_prio_756_, lean_object* v_sync_757_){
_start:
{
uint8_t v_sync_boxed_758_; lean_object* v_res_759_; 
v_sync_boxed_758_ = lean_unbox(v_sync_757_);
v_res_759_ = l_Lake_Job_mapResult(v_00_u03b2_751_, v_00_u03b1_752_, v_inst_753_, v_f_754_, v_self_755_, v_prio_756_, v_sync_boxed_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v_a_763_; lean_object* v___x_764_; 
v_a_762_ = lean_ctor_get(v_x_761_, 0);
lean_inc(v_a_762_);
v_a_763_ = lean_ctor_get(v_x_761_, 1);
lean_inc(v_a_763_);
lean_dec_ref_known(v_x_761_, 2);
v___x_764_ = lean_apply_2(v_f_760_, v_a_762_, v_a_763_);
return v___x_764_;
}
else
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_f_760_);
v_a_765_ = lean_ctor_get(v_x_761_, 0);
v_a_766_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v_x_761_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v_x_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_774_, lean_object* v_f_775_, lean_object* v_self_776_, lean_object* v_prio_777_, uint8_t v_sync_778_){
_start:
{
lean_object* v_task_779_; lean_object* v_caption_780_; uint8_t v_optional_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_790_; 
v_task_779_ = lean_ctor_get(v_self_776_, 0);
v_caption_780_ = lean_ctor_get(v_self_776_, 2);
v_optional_781_ = lean_ctor_get_uint8(v_self_776_, sizeof(void*)*3);
v_isSharedCheck_790_ = !lean_is_exclusive(v_self_776_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_self_776_, 1);
lean_dec(v_unused_791_);
v___x_783_ = v_self_776_;
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_caption_780_);
lean_inc(v_task_779_);
lean_dec(v_self_776_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___f_785_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_785_, 0, v_f_775_);
v___x_786_ = lean_task_map(v___f_785_, v_task_779_, v_prio_777_, v_sync_778_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_inst_774_);
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_inst_774_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_caption_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_789_, sizeof(void*)*3, v_optional_781_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* v_inst_792_, lean_object* v_f_793_, lean_object* v_self_794_, lean_object* v_prio_795_, lean_object* v_sync_796_){
_start:
{
uint8_t v_sync_boxed_797_; lean_object* v_res_798_; 
v_sync_boxed_797_ = lean_unbox(v_sync_796_);
v_res_798_ = l_Lake_Job_mapOk___redArg(v_inst_792_, v_f_793_, v_self_794_, v_prio_795_, v_sync_boxed_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_799_, lean_object* v_00_u03b1_800_, lean_object* v_inst_801_, lean_object* v_f_802_, lean_object* v_self_803_, lean_object* v_prio_804_, uint8_t v_sync_805_){
_start:
{
lean_object* v_task_806_; lean_object* v_caption_807_; uint8_t v_optional_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_817_; 
v_task_806_ = lean_ctor_get(v_self_803_, 0);
v_caption_807_ = lean_ctor_get(v_self_803_, 2);
v_optional_808_ = lean_ctor_get_uint8(v_self_803_, sizeof(void*)*3);
v_isSharedCheck_817_ = !lean_is_exclusive(v_self_803_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_self_803_, 1);
lean_dec(v_unused_818_);
v___x_810_ = v_self_803_;
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_caption_807_);
lean_inc(v_task_806_);
lean_dec(v_self_803_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___f_812_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_812_, 0, v_f_802_);
v___x_813_ = lean_task_map(v___f_812_, v_task_806_, v_prio_804_, v_sync_805_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v_inst_801_);
lean_ctor_set(v___x_810_, 0, v___x_813_);
v___x_815_ = v___x_810_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_inst_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_caption_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*3, v_optional_808_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_819_, lean_object* v_00_u03b1_820_, lean_object* v_inst_821_, lean_object* v_f_822_, lean_object* v_self_823_, lean_object* v_prio_824_, lean_object* v_sync_825_){
_start:
{
uint8_t v_sync_boxed_826_; lean_object* v_res_827_; 
v_sync_boxed_826_ = lean_unbox(v_sync_825_);
v_res_827_ = l_Lake_Job_mapOk(v_00_u03b2_819_, v_00_u03b1_820_, v_inst_821_, v_f_822_, v_self_823_, v_prio_824_, v_sync_boxed_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_828_, lean_object* v_x_829_){
_start:
{
if (lean_obj_tag(v_x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_a_830_ = lean_ctor_get(v_x_829_, 0);
v_a_831_ = lean_ctor_get(v_x_829_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v_x_829_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_inc(v_a_830_);
lean_dec(v_x_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_apply_1(v_f_828_, v_a_830_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_a_831_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_f_828_);
v_a_840_ = lean_ctor_get(v_x_829_, 0);
v_a_841_ = lean_ctor_get(v_x_829_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v_x_829_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_inc(v_a_840_);
lean_dec(v_x_829_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_840_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_849_, lean_object* v_f_850_, lean_object* v_self_851_, lean_object* v_prio_852_, uint8_t v_sync_853_){
_start:
{
lean_object* v_task_854_; lean_object* v_caption_855_; uint8_t v_optional_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_865_; 
v_task_854_ = lean_ctor_get(v_self_851_, 0);
v_caption_855_ = lean_ctor_get(v_self_851_, 2);
v_optional_856_ = lean_ctor_get_uint8(v_self_851_, sizeof(void*)*3);
v_isSharedCheck_865_ = !lean_is_exclusive(v_self_851_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_self_851_, 1);
lean_dec(v_unused_866_);
v___x_858_ = v_self_851_;
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_caption_855_);
lean_inc(v_task_854_);
lean_dec(v_self_851_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___f_860_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_860_, 0, v_f_850_);
v___x_861_ = lean_task_map(v___f_860_, v_task_854_, v_prio_852_, v_sync_853_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_inst_849_);
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_inst_849_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_caption_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_864_, sizeof(void*)*3, v_optional_856_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_867_, lean_object* v_f_868_, lean_object* v_self_869_, lean_object* v_prio_870_, lean_object* v_sync_871_){
_start:
{
uint8_t v_sync_boxed_872_; lean_object* v_res_873_; 
v_sync_boxed_872_ = lean_unbox(v_sync_871_);
v_res_873_ = l_Lake_Job_map___redArg(v_inst_867_, v_f_868_, v_self_869_, v_prio_870_, v_sync_boxed_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_874_, lean_object* v_00_u03b1_875_, lean_object* v_inst_876_, lean_object* v_f_877_, lean_object* v_self_878_, lean_object* v_prio_879_, uint8_t v_sync_880_){
_start:
{
lean_object* v_task_881_; lean_object* v_caption_882_; uint8_t v_optional_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
v_task_881_ = lean_ctor_get(v_self_878_, 0);
v_caption_882_ = lean_ctor_get(v_self_878_, 2);
v_optional_883_ = lean_ctor_get_uint8(v_self_878_, sizeof(void*)*3);
v_isSharedCheck_892_ = !lean_is_exclusive(v_self_878_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_self_878_, 1);
lean_dec(v_unused_893_);
v___x_885_ = v_self_878_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_caption_882_);
lean_inc(v_task_881_);
lean_dec(v_self_878_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___f_887_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_887_, 0, v_f_877_);
v___x_888_ = lean_task_map(v___f_887_, v_task_881_, v_prio_879_, v_sync_880_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v_inst_876_);
lean_ctor_set(v___x_885_, 0, v___x_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_inst_876_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_caption_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3, v_optional_883_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_894_, lean_object* v_00_u03b1_895_, lean_object* v_inst_896_, lean_object* v_f_897_, lean_object* v_self_898_, lean_object* v_prio_899_, lean_object* v_sync_900_){
_start:
{
uint8_t v_sync_boxed_901_; lean_object* v_res_902_; 
v_sync_boxed_901_ = lean_unbox(v_sync_900_);
v_res_902_ = l_Lake_Job_map(v_00_u03b2_894_, v_00_u03b1_895_, v_inst_896_, v_f_897_, v_self_898_, v_prio_899_, v_sync_boxed_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_f_905_, lean_object* v_self_906_){
_start:
{
lean_object* v_task_907_; lean_object* v_caption_908_; uint8_t v_optional_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_task_907_ = lean_ctor_get(v_self_906_, 0);
v_caption_908_ = lean_ctor_get(v_self_906_, 2);
v_optional_909_ = lean_ctor_get_uint8(v_self_906_, sizeof(void*)*3);
v_isSharedCheck_921_ = !lean_is_exclusive(v_self_906_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_self_906_, 1);
lean_dec(v_unused_922_);
v___x_911_ = v_self_906_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_caption_908_);
lean_inc(v_task_907_);
lean_dec(v_self_906_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___f_913_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_913_, 0, v_f_905_);
v___x_914_ = lean_box(0);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = 0;
v___x_917_ = lean_task_map(v___f_913_, v_task_907_, v___x_915_, v___x_916_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_914_);
lean_ctor_set(v___x_911_, 0, v___x_917_);
v___x_919_ = v___x_911_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_caption_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, sizeof(void*)*3, v_optional_909_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_923_, lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_928_, 0, lean_box(0));
lean_closure_set(v___x_928_, 1, lean_box(0));
lean_closure_set(v___x_928_, 2, v___y_926_);
v___x_929_ = lean_apply_4(v___f_923_, lean_box(0), lean_box(0), v___x_928_, v___y_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_937_){
_start:
{
lean_inc_ref(v_self_937_);
return v_self_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_938_);
lean_dec_ref(v_self_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_940_, lean_object* v_self_941_){
_start:
{
lean_inc_ref(v_self_941_);
return v_self_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_942_, lean_object* v_self_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_942_, v_self_943_);
lean_dec_ref(v_self_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0));
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_948_){
_start:
{
lean_object* v_task_949_; lean_object* v_caption_950_; uint8_t v_optional_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_959_; 
v_task_949_ = lean_ctor_get(v_job_948_, 0);
v_caption_950_ = lean_ctor_get(v_job_948_, 2);
v_optional_951_ = lean_ctor_get_uint8(v_job_948_, sizeof(void*)*3);
v_isSharedCheck_959_ = !lean_is_exclusive(v_job_948_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_job_948_, 1);
lean_dec(v_unused_960_);
v___x_953_ = v_job_948_;
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_caption_950_);
lean_inc(v_task_949_);
lean_dec(v_job_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_box(0);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_task_949_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_caption_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3, v_optional_951_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_961_, lean_object* v_job_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lake_Job_toOpaque___redArg(v_job_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* v_00_u03b1_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___closed__0));
return v___x_966_;
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
