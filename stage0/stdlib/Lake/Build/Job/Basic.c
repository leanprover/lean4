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
uint8_t v_x_345__boxed_198_; lean_object* v_res_199_; 
v_x_345__boxed_198_ = lean_unbox(v_x_196_);
v_res_199_ = l_Lake_instReprJobAction_repr(v_x_345__boxed_198_, v_prec_197_);
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
uint8_t v_x_13__boxed_229_; uint8_t v_y_14__boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v_x_13__boxed_229_ = lean_unbox(v_x_227_);
v_y_14__boxed_230_ = lean_unbox(v_y_228_);
v_res_231_ = l_Lake_instDecidableEqJobAction(v_x_13__boxed_229_, v_y_14__boxed_230_);
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
uint8_t v_failed_boxed_311_; uint8_t v_x_256__boxed_312_; lean_object* v_res_313_; 
v_failed_boxed_311_ = lean_unbox(v_failed_309_);
v_x_256__boxed_312_ = lean_unbox(v_x_310_);
v_res_313_ = l_Lake_JobAction_verb(v_failed_boxed_311_, v_x_256__boxed_312_);
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
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l_Lake_instInhabitedJobState_default;
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
v___x_438_ = lean_task_pure(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__3(void){
_start:
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_440_ = 0;
v___x_441_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_442_ = lean_box(0);
v___x_443_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__1, &l_Lake_instInhabitedJob___closed__1_once, _init_l_Lake_instInhabitedJob___closed__1);
v___x_444_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*3, v___x_440_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__3, &l_Lake_instInhabitedJob___closed__3_once, _init_l_Lake_instInhabitedJob___closed__3);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_447_){
_start:
{
lean_inc_ref(v_self_447_);
return v_self_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lake_Job_cast___redArg(v_self_448_);
lean_dec_ref(v_self_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_450_, lean_object* v_self_451_, lean_object* v_h_452_){
_start:
{
lean_inc_ref(v_self_451_);
return v_self_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_453_, lean_object* v_self_454_, lean_object* v_h_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lake_Job_cast(v_00_u03b1_453_, v_self_454_, v_h_455_);
lean_dec_ref(v_self_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_457_, lean_object* v_task_458_, lean_object* v_caption_459_){
_start:
{
uint8_t v___x_460_; lean_object* v___x_461_; 
v___x_460_ = 0;
v___x_461_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_461_, 0, v_task_458_);
lean_ctor_set(v___x_461_, 1, v_inst_457_);
lean_ctor_set(v___x_461_, 2, v_caption_459_);
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*3, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_462_, lean_object* v_inst_463_, lean_object* v_task_464_, lean_object* v_caption_465_){
_start:
{
uint8_t v___x_466_; lean_object* v___x_467_; 
v___x_466_ = 0;
v___x_467_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_467_, 0, v_task_464_);
lean_ctor_set(v___x_467_, 1, v_inst_463_);
lean_ctor_set(v___x_467_, 2, v_caption_465_);
lean_ctor_set_uint8(v___x_467_, sizeof(void*)*3, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_468_, lean_object* v_log_469_, lean_object* v_caption_470_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = 0;
v___x_473_ = 0;
v___x_474_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_475_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_475_, 0, v_log_469_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
lean_ctor_set(v___x_475_, 2, v___x_471_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*3, v___x_472_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*3 + 1, v___x_473_);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_471_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_task_pure(v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_inst_468_);
lean_ctor_set(v___x_478_, 2, v_caption_470_);
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*3, v___x_473_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_479_, lean_object* v_inst_480_, lean_object* v_log_481_, lean_object* v_caption_482_){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = 0;
v___x_485_ = 0;
v___x_486_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_487_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_487_, 0, v_log_481_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
lean_ctor_set(v___x_487_, 2, v___x_483_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*3, v___x_484_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*3 + 1, v___x_485_);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_483_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_task_pure(v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_inst_480_);
lean_ctor_set(v___x_490_, 2, v_caption_482_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*3, v___x_485_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_491_, lean_object* v_a_492_, lean_object* v_log_493_, lean_object* v_caption_494_){
_start:
{
uint8_t v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_495_ = 0;
v___x_496_ = 0;
v___x_497_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_499_, 0, v_log_493_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*3, v___x_495_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*3 + 1, v___x_496_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_a_492_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_task_pure(v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v_kind_491_);
lean_ctor_set(v___x_502_, 2, v_caption_494_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3, v___x_496_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_503_, lean_object* v_kind_504_, lean_object* v_a_505_, lean_object* v_log_506_, lean_object* v_caption_507_){
_start:
{
uint8_t v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_508_ = 0;
v___x_509_ = 0;
v___x_510_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_512_, 0, v_log_506_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
lean_ctor_set(v___x_512_, 2, v___x_511_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*3, v___x_508_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*3 + 1, v___x_509_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_a_505_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_task_pure(v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_kind_504_);
lean_ctor_set(v___x_515_, 2, v_caption_507_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*3, v___x_509_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_518_ = lean_box(0);
v___x_519_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_520_ = 0;
v___x_521_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_a_517_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = lean_task_pure(v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v___x_518_);
lean_ctor_set(v___x_524_, 2, v___x_519_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*3, v___x_520_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_527_, lean_object* v_caption_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_529_ = lean_box(0);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_532_ = 0;
v___x_533_ = 0;
v___x_534_ = l_Lake_BuildTrace_nil(v_caption_528_);
v___x_535_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_535_, 0, v___x_531_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_ctor_set(v___x_535_, 2, v___x_530_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*3, v___x_532_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*3 + 1, v___x_533_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_527_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_task_pure(v___x_536_);
v___x_538_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_539_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_529_);
lean_ctor_set(v___x_539_, 2, v___x_538_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*3, v___x_533_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_540_, lean_object* v_a_541_, lean_object* v_caption_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_546_ = 0;
v___x_547_ = 0;
v___x_548_ = l_Lake_BuildTrace_nil(v_caption_542_);
v___x_549_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_549_, 0, v___x_545_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_ctor_set(v___x_549_, 2, v___x_544_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*3, v___x_546_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*3 + 1, v___x_547_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_541_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_task_pure(v___x_550_);
v___x_552_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_553_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_543_);
lean_ctor_set(v___x_553_, 2, v___x_552_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*3, v___x_547_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_554_, lean_object* v_caption_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_556_ = l_Lake_instDataKindUnit;
v___x_557_ = lean_box(0);
v___x_558_ = 0;
v___x_559_ = 0;
v___x_560_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_562_, 0, v_log_554_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_561_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*3, v___x_558_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*3 + 1, v___x_559_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_557_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_task_pure(v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_556_);
lean_ctor_set(v___x_565_, 2, v_caption_555_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*3, v___x_559_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_567_ = lean_box(0);
v___x_568_ = lean_box(0);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_571_ = 0;
v___x_572_ = 0;
v___x_573_ = l_Lake_BuildTrace_nil(v_traceCaption_566_);
v___x_574_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_574_, 0, v___x_570_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_ctor_set(v___x_574_, 2, v___x_569_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*3, v___x_571_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*3 + 1, v___x_572_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_567_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_task_pure(v___x_575_);
v___x_577_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_578_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_568_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
lean_ctor_set_uint8(v___x_578_, sizeof(void*)*3, v___x_572_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_579_){
_start:
{
lean_object* v_task_580_; lean_object* v___x_581_; lean_object* v_a_582_; lean_object* v_trace_583_; 
v_task_580_ = lean_ctor_get(v_job_579_, 0);
lean_inc_ref(v_task_580_);
lean_dec_ref(v_job_579_);
v___x_581_ = lean_task_get_own(v_task_580_);
v_a_582_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v_trace_583_ = lean_ctor_get(v_a_582_, 1);
lean_inc_ref(v_trace_583_);
lean_dec(v_a_582_);
return v_trace_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_584_, lean_object* v_job_585_){
_start:
{
lean_object* v_task_586_; lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v_trace_589_; 
v_task_586_ = lean_ctor_get(v_job_585_, 0);
lean_inc_ref(v_task_586_);
lean_dec_ref(v_job_585_);
v___x_587_ = lean_task_get_own(v_task_586_);
v_a_588_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v_trace_589_ = lean_ctor_get(v_a_588_, 1);
lean_inc_ref(v_trace_589_);
lean_dec(v_a_588_);
return v_trace_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_590_, lean_object* v_job_591_){
_start:
{
lean_object* v_task_592_; lean_object* v_kind_593_; uint8_t v_optional_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_task_592_ = lean_ctor_get(v_job_591_, 0);
v_kind_593_ = lean_ctor_get(v_job_591_, 1);
v_optional_594_ = lean_ctor_get_uint8(v_job_591_, sizeof(void*)*3);
v_isSharedCheck_601_ = !lean_is_exclusive(v_job_591_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_job_591_, 2);
lean_dec(v_unused_602_);
v___x_596_ = v_job_591_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_kind_593_);
lean_inc(v_task_592_);
lean_dec(v_job_591_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 2, v_caption_590_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_task_592_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_kind_593_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_caption_590_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*3, v_optional_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_603_, lean_object* v_caption_604_, lean_object* v_job_605_){
_start:
{
lean_object* v_task_606_; lean_object* v_kind_607_; uint8_t v_optional_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_task_606_ = lean_ctor_get(v_job_605_, 0);
v_kind_607_ = lean_ctor_get(v_job_605_, 1);
v_optional_608_ = lean_ctor_get_uint8(v_job_605_, sizeof(void*)*3);
v_isSharedCheck_615_ = !lean_is_exclusive(v_job_605_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_job_605_, 2);
lean_dec(v_unused_616_);
v___x_610_ = v_job_605_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_kind_607_);
lean_inc(v_task_606_);
lean_dec(v_job_605_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 2, v_caption_604_);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_task_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_kind_607_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_caption_604_);
lean_ctor_set_uint8(v_reuseFailAlloc_614_, sizeof(void*)*3, v_optional_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_617_, lean_object* v_job_618_){
_start:
{
lean_object* v_task_619_; lean_object* v_kind_620_; lean_object* v_caption_621_; uint8_t v_optional_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_task_619_ = lean_ctor_get(v_job_618_, 0);
v_kind_620_ = lean_ctor_get(v_job_618_, 1);
v_caption_621_ = lean_ctor_get(v_job_618_, 2);
v_optional_622_ = lean_ctor_get_uint8(v_job_618_, sizeof(void*)*3);
v___x_623_ = lean_string_utf8_byte_size(v_caption_621_);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_nat_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec_ref(v_caption_617_);
return v_job_618_;
}
else
{
lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_inc(v_kind_620_);
lean_inc_ref(v_task_619_);
v_isSharedCheck_632_ = !lean_is_exclusive(v_job_618_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; lean_object* v_unused_634_; lean_object* v_unused_635_; 
v_unused_633_ = lean_ctor_get(v_job_618_, 2);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_job_618_, 1);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_job_618_, 0);
lean_dec(v_unused_635_);
v___x_627_ = v_job_618_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_dec(v_job_618_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 2, v_caption_617_);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_task_619_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_kind_620_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_caption_617_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*3, v_optional_622_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_636_, lean_object* v_caption_637_, lean_object* v_job_638_){
_start:
{
lean_object* v_task_639_; lean_object* v_kind_640_; lean_object* v_caption_641_; uint8_t v_optional_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_task_639_ = lean_ctor_get(v_job_638_, 0);
v_kind_640_ = lean_ctor_get(v_job_638_, 1);
v_caption_641_ = lean_ctor_get(v_job_638_, 2);
v_optional_642_ = lean_ctor_get_uint8(v_job_638_, sizeof(void*)*3);
v___x_643_ = lean_string_utf8_byte_size(v_caption_641_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_nat_dec_eq(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec_ref(v_caption_637_);
return v_job_638_;
}
else
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_inc(v_kind_640_);
lean_inc_ref(v_task_639_);
v_isSharedCheck_652_ = !lean_is_exclusive(v_job_638_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; 
v_unused_653_ = lean_ctor_get(v_job_638_, 2);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_job_638_, 1);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_job_638_, 0);
lean_dec(v_unused_655_);
v___x_647_ = v_job_638_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_dec(v_job_638_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 2, v_caption_637_);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_task_639_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_kind_640_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_caption_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_651_, sizeof(void*)*3, v_optional_642_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_656_, lean_object* v_f_657_, lean_object* v_self_658_, lean_object* v_prio_659_, uint8_t v_sync_660_){
_start:
{
lean_object* v_task_661_; lean_object* v_caption_662_; uint8_t v_optional_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_task_661_ = lean_ctor_get(v_self_658_, 0);
v_caption_662_ = lean_ctor_get(v_self_658_, 2);
v_optional_663_ = lean_ctor_get_uint8(v_self_658_, sizeof(void*)*3);
v_isSharedCheck_671_ = !lean_is_exclusive(v_self_658_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_self_658_, 1);
lean_dec(v_unused_672_);
v___x_665_ = v_self_658_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_caption_662_);
lean_inc(v_task_661_);
lean_dec(v_self_658_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_task_map(v_f_657_, v_task_661_, v_prio_659_, v_sync_660_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_inst_656_);
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_inst_656_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_caption_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*3, v_optional_663_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_673_, lean_object* v_f_674_, lean_object* v_self_675_, lean_object* v_prio_676_, lean_object* v_sync_677_){
_start:
{
uint8_t v_sync_boxed_678_; lean_object* v_res_679_; 
v_sync_boxed_678_ = lean_unbox(v_sync_677_);
v_res_679_ = l_Lake_Job_mapResult___redArg(v_inst_673_, v_f_674_, v_self_675_, v_prio_676_, v_sync_boxed_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_680_, lean_object* v_00_u03b1_681_, lean_object* v_inst_682_, lean_object* v_f_683_, lean_object* v_self_684_, lean_object* v_prio_685_, uint8_t v_sync_686_){
_start:
{
lean_object* v_task_687_; lean_object* v_caption_688_; uint8_t v_optional_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_697_; 
v_task_687_ = lean_ctor_get(v_self_684_, 0);
v_caption_688_ = lean_ctor_get(v_self_684_, 2);
v_optional_689_ = lean_ctor_get_uint8(v_self_684_, sizeof(void*)*3);
v_isSharedCheck_697_ = !lean_is_exclusive(v_self_684_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_self_684_, 1);
lean_dec(v_unused_698_);
v___x_691_ = v_self_684_;
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_caption_688_);
lean_inc(v_task_687_);
lean_dec(v_self_684_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = lean_task_map(v_f_683_, v_task_687_, v_prio_685_, v_sync_686_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_inst_682_);
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_inst_682_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_caption_688_);
lean_ctor_set_uint8(v_reuseFailAlloc_696_, sizeof(void*)*3, v_optional_689_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_699_, lean_object* v_00_u03b1_700_, lean_object* v_inst_701_, lean_object* v_f_702_, lean_object* v_self_703_, lean_object* v_prio_704_, lean_object* v_sync_705_){
_start:
{
uint8_t v_sync_boxed_706_; lean_object* v_res_707_; 
v_sync_boxed_706_ = lean_unbox(v_sync_705_);
v_res_707_ = l_Lake_Job_mapResult(v_00_u03b2_699_, v_00_u03b1_700_, v_inst_701_, v_f_702_, v_self_703_, v_prio_704_, v_sync_boxed_706_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v_a_711_; lean_object* v___x_712_; 
v_a_710_ = lean_ctor_get(v_x_709_, 0);
lean_inc(v_a_710_);
v_a_711_ = lean_ctor_get(v_x_709_, 1);
lean_inc(v_a_711_);
lean_dec_ref_known(v_x_709_, 2);
v___x_712_ = lean_apply_2(v_f_708_, v_a_710_, v_a_711_);
return v___x_712_;
}
else
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_f_708_);
v_a_713_ = lean_ctor_get(v_x_709_, 0);
v_a_714_ = lean_ctor_get(v_x_709_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v_x_709_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_inc(v_a_713_);
lean_dec(v_x_709_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_713_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_722_, lean_object* v_f_723_, lean_object* v_self_724_, lean_object* v_prio_725_, uint8_t v_sync_726_){
_start:
{
lean_object* v_task_727_; lean_object* v_caption_728_; uint8_t v_optional_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_738_; 
v_task_727_ = lean_ctor_get(v_self_724_, 0);
v_caption_728_ = lean_ctor_get(v_self_724_, 2);
v_optional_729_ = lean_ctor_get_uint8(v_self_724_, sizeof(void*)*3);
v_isSharedCheck_738_ = !lean_is_exclusive(v_self_724_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_self_724_, 1);
lean_dec(v_unused_739_);
v___x_731_ = v_self_724_;
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_caption_728_);
lean_inc(v_task_727_);
lean_dec(v_self_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___f_733_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_733_, 0, v_f_723_);
v___x_734_ = lean_task_map(v___f_733_, v_task_727_, v_prio_725_, v_sync_726_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_inst_722_);
lean_ctor_set(v___x_731_, 0, v___x_734_);
v___x_736_ = v___x_731_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_inst_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_caption_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*3, v_optional_729_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* v_inst_740_, lean_object* v_f_741_, lean_object* v_self_742_, lean_object* v_prio_743_, lean_object* v_sync_744_){
_start:
{
uint8_t v_sync_boxed_745_; lean_object* v_res_746_; 
v_sync_boxed_745_ = lean_unbox(v_sync_744_);
v_res_746_ = l_Lake_Job_mapOk___redArg(v_inst_740_, v_f_741_, v_self_742_, v_prio_743_, v_sync_boxed_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_747_, lean_object* v_00_u03b1_748_, lean_object* v_inst_749_, lean_object* v_f_750_, lean_object* v_self_751_, lean_object* v_prio_752_, uint8_t v_sync_753_){
_start:
{
lean_object* v_task_754_; lean_object* v_caption_755_; uint8_t v_optional_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_765_; 
v_task_754_ = lean_ctor_get(v_self_751_, 0);
v_caption_755_ = lean_ctor_get(v_self_751_, 2);
v_optional_756_ = lean_ctor_get_uint8(v_self_751_, sizeof(void*)*3);
v_isSharedCheck_765_ = !lean_is_exclusive(v_self_751_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_self_751_, 1);
lean_dec(v_unused_766_);
v___x_758_ = v_self_751_;
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_caption_755_);
lean_inc(v_task_754_);
lean_dec(v_self_751_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___f_760_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_760_, 0, v_f_750_);
v___x_761_ = lean_task_map(v___f_760_, v_task_754_, v_prio_752_, v_sync_753_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_inst_749_);
lean_ctor_set(v___x_758_, 0, v___x_761_);
v___x_763_ = v___x_758_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_inst_749_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_caption_755_);
lean_ctor_set_uint8(v_reuseFailAlloc_764_, sizeof(void*)*3, v_optional_756_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_767_, lean_object* v_00_u03b1_768_, lean_object* v_inst_769_, lean_object* v_f_770_, lean_object* v_self_771_, lean_object* v_prio_772_, lean_object* v_sync_773_){
_start:
{
uint8_t v_sync_boxed_774_; lean_object* v_res_775_; 
v_sync_boxed_774_ = lean_unbox(v_sync_773_);
v_res_775_ = l_Lake_Job_mapOk(v_00_u03b2_767_, v_00_u03b1_768_, v_inst_769_, v_f_770_, v_self_771_, v_prio_772_, v_sync_boxed_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_a_778_ = lean_ctor_get(v_x_777_, 0);
v_a_779_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_787_ == 0)
{
v___x_781_ = v_x_777_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_inc(v_a_778_);
lean_dec(v_x_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_apply_1(v_f_776_, v_a_778_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_a_779_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_f_776_);
v_a_788_ = lean_ctor_get(v_x_777_, 0);
v_a_789_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v_x_777_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_inc(v_a_788_);
lean_dec(v_x_777_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_788_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_797_, lean_object* v_f_798_, lean_object* v_self_799_, lean_object* v_prio_800_, uint8_t v_sync_801_){
_start:
{
lean_object* v_task_802_; lean_object* v_caption_803_; uint8_t v_optional_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_813_; 
v_task_802_ = lean_ctor_get(v_self_799_, 0);
v_caption_803_ = lean_ctor_get(v_self_799_, 2);
v_optional_804_ = lean_ctor_get_uint8(v_self_799_, sizeof(void*)*3);
v_isSharedCheck_813_ = !lean_is_exclusive(v_self_799_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_self_799_, 1);
lean_dec(v_unused_814_);
v___x_806_ = v_self_799_;
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_caption_803_);
lean_inc(v_task_802_);
lean_dec(v_self_799_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___f_808_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_808_, 0, v_f_798_);
v___x_809_ = lean_task_map(v___f_808_, v_task_802_, v_prio_800_, v_sync_801_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v_inst_797_);
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_inst_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_caption_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*3, v_optional_804_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_815_, lean_object* v_f_816_, lean_object* v_self_817_, lean_object* v_prio_818_, lean_object* v_sync_819_){
_start:
{
uint8_t v_sync_boxed_820_; lean_object* v_res_821_; 
v_sync_boxed_820_ = lean_unbox(v_sync_819_);
v_res_821_ = l_Lake_Job_map___redArg(v_inst_815_, v_f_816_, v_self_817_, v_prio_818_, v_sync_boxed_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_822_, lean_object* v_00_u03b1_823_, lean_object* v_inst_824_, lean_object* v_f_825_, lean_object* v_self_826_, lean_object* v_prio_827_, uint8_t v_sync_828_){
_start:
{
lean_object* v_task_829_; lean_object* v_caption_830_; uint8_t v_optional_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_840_; 
v_task_829_ = lean_ctor_get(v_self_826_, 0);
v_caption_830_ = lean_ctor_get(v_self_826_, 2);
v_optional_831_ = lean_ctor_get_uint8(v_self_826_, sizeof(void*)*3);
v_isSharedCheck_840_ = !lean_is_exclusive(v_self_826_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_self_826_, 1);
lean_dec(v_unused_841_);
v___x_833_ = v_self_826_;
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_caption_830_);
lean_inc(v_task_829_);
lean_dec(v_self_826_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___f_835_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_835_, 0, v_f_825_);
v___x_836_ = lean_task_map(v___f_835_, v_task_829_, v_prio_827_, v_sync_828_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_inst_824_);
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_inst_824_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_caption_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_839_, sizeof(void*)*3, v_optional_831_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_842_, lean_object* v_00_u03b1_843_, lean_object* v_inst_844_, lean_object* v_f_845_, lean_object* v_self_846_, lean_object* v_prio_847_, lean_object* v_sync_848_){
_start:
{
uint8_t v_sync_boxed_849_; lean_object* v_res_850_; 
v_sync_boxed_849_ = lean_unbox(v_sync_848_);
v_res_850_ = l_Lake_Job_map(v_00_u03b2_842_, v_00_u03b1_843_, v_inst_844_, v_f_845_, v_self_846_, v_prio_847_, v_sync_boxed_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_f_853_, lean_object* v_self_854_){
_start:
{
lean_object* v_task_855_; lean_object* v_caption_856_; uint8_t v_optional_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_869_; 
v_task_855_ = lean_ctor_get(v_self_854_, 0);
v_caption_856_ = lean_ctor_get(v_self_854_, 2);
v_optional_857_ = lean_ctor_get_uint8(v_self_854_, sizeof(void*)*3);
v_isSharedCheck_869_ = !lean_is_exclusive(v_self_854_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_self_854_, 1);
lean_dec(v_unused_870_);
v___x_859_ = v_self_854_;
v_isShared_860_ = v_isSharedCheck_869_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_caption_856_);
lean_inc(v_task_855_);
lean_dec(v_self_854_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_869_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___f_861_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_861_, 0, v_f_853_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = 0;
v___x_865_ = lean_task_map(v___f_861_, v_task_855_, v___x_863_, v___x_864_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_862_);
lean_ctor_set(v___x_859_, 0, v___x_865_);
v___x_867_ = v___x_859_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_caption_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, sizeof(void*)*3, v_optional_857_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_871_, lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_876_, 0, lean_box(0));
lean_closure_set(v___x_876_, 1, lean_box(0));
lean_closure_set(v___x_876_, 2, v___y_874_);
v___x_877_ = lean_apply_4(v___f_871_, lean_box(0), lean_box(0), v___x_876_, v___y_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_885_){
_start:
{
lean_inc_ref(v_self_885_);
return v_self_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_886_);
lean_dec_ref(v_self_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_888_, lean_object* v_self_889_){
_start:
{
lean_inc_ref(v_self_889_);
return v_self_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_890_, lean_object* v_self_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_890_, v_self_891_);
lean_dec_ref(v_self_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0));
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_896_){
_start:
{
lean_object* v_task_897_; lean_object* v_caption_898_; uint8_t v_optional_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_907_; 
v_task_897_ = lean_ctor_get(v_job_896_, 0);
v_caption_898_ = lean_ctor_get(v_job_896_, 2);
v_optional_899_ = lean_ctor_get_uint8(v_job_896_, sizeof(void*)*3);
v_isSharedCheck_907_ = !lean_is_exclusive(v_job_896_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_job_896_, 1);
lean_dec(v_unused_908_);
v___x_901_ = v_job_896_;
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_caption_898_);
lean_inc(v_task_897_);
lean_dec(v_job_896_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_task_897_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_caption_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*3, v_optional_899_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_909_, lean_object* v_job_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lake_Job_toOpaque___redArg(v_job_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* v_00_u03b1_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___closed__0));
return v___x_914_;
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
