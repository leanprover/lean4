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
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx(uint8_t v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lake_JobAction_ctorIdx(v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_x_4__boxed_14_; lean_object* v_res_15_; 
v_x_4__boxed_14_ = lean_unbox(v_x_13_);
v_res_15_ = l_Lake_JobAction_toCtorIdx(v_x_4__boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg(lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg___boxed(lean_object* v_k_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lake_JobAction_ctorElim___redArg(v_k_17_);
lean_dec(v_k_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, uint8_t v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_inc(v_k_23_);
return v_k_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
uint8_t v_t_boxed_29_; lean_object* v_res_30_; 
v_t_boxed_29_ = lean_unbox(v_t_26_);
v_res_30_ = l_Lake_JobAction_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_boxed_29_, v_h_27_, v_k_28_);
lean_dec(v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg(lean_object* v_unknown_31_){
_start:
{
lean_inc(v_unknown_31_);
return v_unknown_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg___boxed(lean_object* v_unknown_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lake_JobAction_unknown_elim___redArg(v_unknown_32_);
lean_dec(v_unknown_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim(lean_object* v_motive_34_, uint8_t v_t_35_, lean_object* v_h_36_, lean_object* v_unknown_37_){
_start:
{
lean_inc(v_unknown_37_);
return v_unknown_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___boxed(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_unknown_41_){
_start:
{
uint8_t v_t_boxed_42_; lean_object* v_res_43_; 
v_t_boxed_42_ = lean_unbox(v_t_39_);
v_res_43_ = l_Lake_JobAction_unknown_elim(v_motive_38_, v_t_boxed_42_, v_h_40_, v_unknown_41_);
lean_dec(v_unknown_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg(lean_object* v_reuse_44_){
_start:
{
lean_inc(v_reuse_44_);
return v_reuse_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg___boxed(lean_object* v_reuse_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lake_JobAction_reuse_elim___redArg(v_reuse_45_);
lean_dec(v_reuse_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim(lean_object* v_motive_47_, uint8_t v_t_48_, lean_object* v_h_49_, lean_object* v_reuse_50_){
_start:
{
lean_inc(v_reuse_50_);
return v_reuse_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___boxed(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_reuse_54_){
_start:
{
uint8_t v_t_boxed_55_; lean_object* v_res_56_; 
v_t_boxed_55_ = lean_unbox(v_t_52_);
v_res_56_ = l_Lake_JobAction_reuse_elim(v_motive_51_, v_t_boxed_55_, v_h_53_, v_reuse_54_);
lean_dec(v_reuse_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg(lean_object* v_replay_57_){
_start:
{
lean_inc(v_replay_57_);
return v_replay_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg___boxed(lean_object* v_replay_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_JobAction_replay_elim___redArg(v_replay_58_);
lean_dec(v_replay_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim(lean_object* v_motive_60_, uint8_t v_t_61_, lean_object* v_h_62_, lean_object* v_replay_63_){
_start:
{
lean_inc(v_replay_63_);
return v_replay_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___boxed(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_replay_67_){
_start:
{
uint8_t v_t_boxed_68_; lean_object* v_res_69_; 
v_t_boxed_68_ = lean_unbox(v_t_65_);
v_res_69_ = l_Lake_JobAction_replay_elim(v_motive_64_, v_t_boxed_68_, v_h_66_, v_replay_67_);
lean_dec(v_replay_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg(lean_object* v_unpack_70_){
_start:
{
lean_inc(v_unpack_70_);
return v_unpack_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg___boxed(lean_object* v_unpack_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lake_JobAction_unpack_elim___redArg(v_unpack_71_);
lean_dec(v_unpack_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim(lean_object* v_motive_73_, uint8_t v_t_74_, lean_object* v_h_75_, lean_object* v_unpack_76_){
_start:
{
lean_inc(v_unpack_76_);
return v_unpack_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___boxed(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_unpack_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l_Lake_JobAction_unpack_elim(v_motive_77_, v_t_boxed_81_, v_h_79_, v_unpack_80_);
lean_dec(v_unpack_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg(lean_object* v_fetch_83_){
_start:
{
lean_inc(v_fetch_83_);
return v_fetch_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg___boxed(lean_object* v_fetch_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lake_JobAction_fetch_elim___redArg(v_fetch_84_);
lean_dec(v_fetch_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim(lean_object* v_motive_86_, uint8_t v_t_87_, lean_object* v_h_88_, lean_object* v_fetch_89_){
_start:
{
lean_inc(v_fetch_89_);
return v_fetch_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___boxed(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_fetch_93_){
_start:
{
uint8_t v_t_boxed_94_; lean_object* v_res_95_; 
v_t_boxed_94_ = lean_unbox(v_t_91_);
v_res_95_ = l_Lake_JobAction_fetch_elim(v_motive_90_, v_t_boxed_94_, v_h_92_, v_fetch_93_);
lean_dec(v_fetch_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg(lean_object* v_build_96_){
_start:
{
lean_inc(v_build_96_);
return v_build_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg___boxed(lean_object* v_build_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lake_JobAction_build_elim___redArg(v_build_97_);
lean_dec(v_build_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim(lean_object* v_motive_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_build_102_){
_start:
{
lean_inc(v_build_102_);
return v_build_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___boxed(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_build_106_){
_start:
{
uint8_t v_t_boxed_107_; lean_object* v_res_108_; 
v_t_boxed_107_ = lean_unbox(v_t_104_);
v_res_108_ = l_Lake_JobAction_build_elim(v_motive_103_, v_t_boxed_107_, v_h_105_, v_build_106_);
lean_dec(v_build_106_);
return v_res_108_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction_default(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction(void){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__12(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(2u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__13(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr(uint8_t v_x_133_, lean_object* v_prec_134_){
_start:
{
lean_object* v___y_136_; lean_object* v___y_143_; lean_object* v___y_150_; lean_object* v___y_157_; lean_object* v___y_164_; lean_object* v___y_171_; 
switch(v_x_133_)
{
case 0:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1024u);
v___x_178_ = lean_nat_dec_le(v___x_177_, v_prec_134_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_136_ = v___x_179_;
goto v___jp_135_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_136_ = v___x_180_;
goto v___jp_135_;
}
}
case 1:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1024u);
v___x_182_ = lean_nat_dec_le(v___x_181_, v_prec_134_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_143_ = v___x_183_;
goto v___jp_142_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_143_ = v___x_184_;
goto v___jp_142_;
}
}
case 2:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(1024u);
v___x_186_ = lean_nat_dec_le(v___x_185_, v_prec_134_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_150_ = v___x_187_;
goto v___jp_149_;
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_150_ = v___x_188_;
goto v___jp_149_;
}
}
case 3:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(1024u);
v___x_190_ = lean_nat_dec_le(v___x_189_, v_prec_134_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_157_ = v___x_191_;
goto v___jp_156_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_157_ = v___x_192_;
goto v___jp_156_;
}
}
case 4:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1024u);
v___x_194_ = lean_nat_dec_le(v___x_193_, v_prec_134_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_164_ = v___x_195_;
goto v___jp_163_;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_164_ = v___x_196_;
goto v___jp_163_;
}
}
default: 
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(1024u);
v___x_198_ = lean_nat_dec_le(v___x_197_, v_prec_134_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_171_ = v___x_199_;
goto v___jp_170_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_171_ = v___x_200_;
goto v___jp_170_;
}
}
}
v___jp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__1));
lean_inc(v___y_136_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___y_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = l_Repr_addAppParen(v___x_140_, v_prec_134_);
return v___x_141_;
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__3));
lean_inc(v___y_143_);
v___x_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_145_, 0, v___y_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = 0;
v___x_147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_146_);
v___x_148_ = l_Repr_addAppParen(v___x_147_, v_prec_134_);
return v___x_148_;
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__5));
lean_inc(v___y_150_);
v___x_152_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_152_, 0, v___y_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_153_);
v___x_155_ = l_Repr_addAppParen(v___x_154_, v_prec_134_);
return v___x_155_;
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__7));
lean_inc(v___y_157_);
v___x_159_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_159_, 0, v___y_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = 0;
v___x_161_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v___x_160_);
v___x_162_ = l_Repr_addAppParen(v___x_161_, v_prec_134_);
return v___x_162_;
}
v___jp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__9));
lean_inc(v___y_164_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___y_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v_prec_134_);
return v___x_169_;
}
v___jp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_172_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__11));
lean_inc(v___y_171_);
v___x_173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_173_, 0, v___y_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = 0;
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_174_);
v___x_176_ = l_Repr_addAppParen(v___x_175_, v_prec_134_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr___boxed(lean_object* v_x_201_, lean_object* v_prec_202_){
_start:
{
uint8_t v_x_345__boxed_203_; lean_object* v_res_204_; 
v_x_345__boxed_203_ = lean_unbox(v_x_201_);
v_res_204_ = l_Lake_instReprJobAction_repr(v_x_345__boxed_203_, v_prec_202_);
lean_dec(v_prec_202_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_ofNat(lean_object* v_n_207_){
_start:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = lean_nat_dec_le(v_n_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(3u);
v___x_211_ = lean_nat_dec_le(v_n_207_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(4u);
v___x_213_ = lean_nat_dec_le(v_n_207_, v___x_212_);
if (v___x_213_ == 0)
{
uint8_t v___x_214_; 
v___x_214_ = 5;
return v___x_214_;
}
else
{
uint8_t v___x_215_; 
v___x_215_ = 4;
return v___x_215_;
}
}
else
{
uint8_t v___x_216_; 
v___x_216_ = 3;
return v___x_216_;
}
}
else
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_dec_le(v_n_207_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_dec_le(v_n_207_, v___x_219_);
if (v___x_220_ == 0)
{
uint8_t v___x_221_; 
v___x_221_ = 2;
return v___x_221_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = 1;
return v___x_222_;
}
}
else
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ofNat___boxed(lean_object* v_n_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Lake_JobAction_ofNat(v_n_224_);
lean_dec(v_n_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqJobAction(uint8_t v_x_227_, uint8_t v_y_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_229_ = l_Lake_JobAction_ctorIdx(v_x_227_);
v___x_230_ = l_Lake_JobAction_ctorIdx(v_y_228_);
v___x_231_ = lean_nat_dec_eq(v___x_229_, v___x_230_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqJobAction___boxed(lean_object* v_x_232_, lean_object* v_y_233_){
_start:
{
uint8_t v_x_13__boxed_234_; uint8_t v_y_14__boxed_235_; uint8_t v_res_236_; lean_object* v_r_237_; 
v_x_13__boxed_234_ = lean_unbox(v_x_232_);
v_y_14__boxed_235_ = lean_unbox(v_y_233_);
v_res_236_ = l_Lake_instDecidableEqJobAction(v_x_13__boxed_234_, v_y_14__boxed_235_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdJobAction_ord(uint8_t v_x_238_, uint8_t v_y_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = l_Lake_JobAction_ctorIdx(v_x_238_);
v___x_241_ = l_Lake_JobAction_ctorIdx(v_y_239_);
v___x_242_ = lean_nat_dec_lt(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
v___x_243_ = lean_nat_dec_eq(v___x_240_, v___x_241_);
lean_dec(v___x_241_);
lean_dec(v___x_240_);
if (v___x_243_ == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 2;
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 1;
return v___x_245_;
}
}
else
{
uint8_t v___x_246_; 
lean_dec(v___x_241_);
lean_dec(v___x_240_);
v___x_246_ = 0;
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdJobAction_ord___boxed(lean_object* v_x_247_, lean_object* v_y_248_){
_start:
{
uint8_t v_x_30__boxed_249_; uint8_t v_y_31__boxed_250_; uint8_t v_res_251_; lean_object* v_r_252_; 
v_x_30__boxed_249_ = lean_unbox(v_x_247_);
v_y_31__boxed_250_ = lean_unbox(v_y_248_);
v_res_251_ = l_Lake_instOrdJobAction_ord(v_x_30__boxed_249_, v_y_31__boxed_250_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
static lean_object* _init_l_Lake_JobAction_instLT(void){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_box(0);
return v___x_255_;
}
}
static lean_object* _init_l_Lake_JobAction_instLE(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_box(0);
return v___x_256_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_instMin___lam__0(uint8_t v_x_257_, uint8_t v_y_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_Lake_instOrdJobAction_ord(v_x_257_, v_y_258_);
if (v___x_259_ == 2)
{
return v_y_258_;
}
else
{
return v_x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMin___lam__0___boxed(lean_object* v_x_260_, lean_object* v_y_261_){
_start:
{
uint8_t v_x_boxed_262_; uint8_t v_y_boxed_263_; uint8_t v_res_264_; lean_object* v_r_265_; 
v_x_boxed_262_ = lean_unbox(v_x_260_);
v_y_boxed_263_ = lean_unbox(v_y_261_);
v_res_264_ = l_Lake_JobAction_instMin___lam__0(v_x_boxed_262_, v_y_boxed_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_instMax___lam__0(uint8_t v_x_268_, uint8_t v_y_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_Lake_instOrdJobAction_ord(v_x_268_, v_y_269_);
if (v___x_270_ == 2)
{
return v_x_268_;
}
else
{
return v_y_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMax___lam__0___boxed(lean_object* v_x_271_, lean_object* v_y_272_){
_start:
{
uint8_t v_x_boxed_273_; uint8_t v_y_boxed_274_; uint8_t v_res_275_; lean_object* v_r_276_; 
v_x_boxed_273_ = lean_unbox(v_x_271_);
v_y_boxed_274_ = lean_unbox(v_y_272_);
v_res_275_ = l_Lake_JobAction_instMax___lam__0(v_x_boxed_273_, v_y_boxed_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_merge(uint8_t v_a_279_, uint8_t v_b_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_Lake_instOrdJobAction_ord(v_a_279_, v_b_280_);
if (v___x_281_ == 2)
{
return v_a_279_;
}
else
{
return v_b_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_merge___boxed(lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
uint8_t v_a_boxed_284_; uint8_t v_b_boxed_285_; uint8_t v_res_286_; lean_object* v_r_287_; 
v_a_boxed_284_ = lean_unbox(v_a_282_);
v_b_boxed_285_ = lean_unbox(v_b_283_);
v_res_286_ = l_Lake_JobAction_merge(v_a_boxed_284_, v_b_boxed_285_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb(uint8_t v_failed_300_, uint8_t v_x_301_){
_start:
{
switch(v_x_301_)
{
case 0:
{
if (v_failed_300_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = ((lean_object*)(l_Lake_JobAction_verb___closed__0));
return v___x_302_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = ((lean_object*)(l_Lake_JobAction_verb___closed__1));
return v___x_303_;
}
}
case 1:
{
if (v_failed_300_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l_Lake_JobAction_verb___closed__2));
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = ((lean_object*)(l_Lake_JobAction_verb___closed__3));
return v___x_305_;
}
}
case 2:
{
if (v_failed_300_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l_Lake_JobAction_verb___closed__4));
return v___x_306_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Lake_JobAction_verb___closed__5));
return v___x_307_;
}
}
case 3:
{
if (v_failed_300_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = ((lean_object*)(l_Lake_JobAction_verb___closed__6));
return v___x_308_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = ((lean_object*)(l_Lake_JobAction_verb___closed__7));
return v___x_309_;
}
}
case 4:
{
if (v_failed_300_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = ((lean_object*)(l_Lake_JobAction_verb___closed__8));
return v___x_310_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = ((lean_object*)(l_Lake_JobAction_verb___closed__9));
return v___x_311_;
}
}
default: 
{
if (v_failed_300_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = ((lean_object*)(l_Lake_JobAction_verb___closed__10));
return v___x_312_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = ((lean_object*)(l_Lake_JobAction_verb___closed__11));
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object* v_failed_314_, lean_object* v_x_315_){
_start:
{
uint8_t v_failed_boxed_316_; uint8_t v_x_256__boxed_317_; lean_object* v_res_318_; 
v_failed_boxed_316_ = lean_unbox(v_failed_314_);
v_x_256__boxed_317_ = lean_unbox(v_x_315_);
v_res_318_ = l_Lake_JobAction_verb(v_failed_boxed_316_, v_x_256__boxed_317_);
return v_res_318_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__2(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__1));
v___x_323_ = l_Lake_BuildTrace_nil(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__3(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_326_ = 0;
v___x_327_ = 0;
v___x_328_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_329_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_325_);
lean_ctor_set(v___x_329_, 2, v___x_324_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*3, v___x_327_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*3 + 1, v___x_326_);
return v___x_329_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
return v___x_330_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lake_instInhabitedJobState_default;
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
lean_object* v_log_334_; uint8_t v_action_335_; uint8_t v_wantsRebuild_336_; lean_object* v_trace_337_; lean_object* v_buildTime_338_; lean_object* v_log_339_; uint8_t v_action_340_; uint8_t v_wantsRebuild_341_; lean_object* v_trace_342_; lean_object* v_buildTime_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_356_; 
v_log_334_ = lean_ctor_get(v_a_332_, 0);
lean_inc_ref(v_log_334_);
v_action_335_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*3);
v_wantsRebuild_336_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*3 + 1);
v_trace_337_ = lean_ctor_get(v_a_332_, 1);
lean_inc_ref(v_trace_337_);
v_buildTime_338_ = lean_ctor_get(v_a_332_, 2);
lean_inc(v_buildTime_338_);
lean_dec_ref(v_a_332_);
v_log_339_ = lean_ctor_get(v_b_333_, 0);
v_action_340_ = lean_ctor_get_uint8(v_b_333_, sizeof(void*)*3);
v_wantsRebuild_341_ = lean_ctor_get_uint8(v_b_333_, sizeof(void*)*3 + 1);
v_trace_342_ = lean_ctor_get(v_b_333_, 1);
v_buildTime_343_ = lean_ctor_get(v_b_333_, 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_b_333_);
if (v_isSharedCheck_356_ == 0)
{
v___x_345_ = v_b_333_;
v_isShared_346_ = v_isSharedCheck_356_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_buildTime_343_);
lean_inc(v_trace_342_);
lean_inc(v_log_339_);
lean_dec(v_b_333_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_356_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; uint8_t v___x_348_; uint8_t v___y_350_; 
v___x_347_ = l_Array_append___redArg(v_log_334_, v_log_339_);
lean_dec_ref(v_log_339_);
v___x_348_ = l_Lake_JobAction_merge(v_action_335_, v_action_340_);
if (v_wantsRebuild_336_ == 0)
{
v___y_350_ = v_wantsRebuild_341_;
goto v___jp_349_;
}
else
{
v___y_350_ = v_wantsRebuild_336_;
goto v___jp_349_;
}
v___jp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = l_Lake_BuildTrace_mix(v_trace_337_, v_trace_342_);
v___x_352_ = lean_nat_add(v_buildTime_338_, v_buildTime_343_);
lean_dec(v_buildTime_343_);
lean_dec(v_buildTime_338_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 2, v___x_352_);
lean_ctor_set(v___x_345_, 1, v___x_351_);
lean_ctor_set(v___x_345_, 0, v___x_347_);
v___x_354_ = v___x_345_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*3, v___x_348_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*3 + 1, v___y_350_);
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object* v_f_357_, lean_object* v_s_358_){
_start:
{
lean_object* v_log_359_; uint8_t v_action_360_; uint8_t v_wantsRebuild_361_; lean_object* v_trace_362_; lean_object* v_buildTime_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_371_; 
v_log_359_ = lean_ctor_get(v_s_358_, 0);
v_action_360_ = lean_ctor_get_uint8(v_s_358_, sizeof(void*)*3);
v_wantsRebuild_361_ = lean_ctor_get_uint8(v_s_358_, sizeof(void*)*3 + 1);
v_trace_362_ = lean_ctor_get(v_s_358_, 1);
v_buildTime_363_ = lean_ctor_get(v_s_358_, 2);
v_isSharedCheck_371_ = !lean_is_exclusive(v_s_358_);
if (v_isSharedCheck_371_ == 0)
{
v___x_365_ = v_s_358_;
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_buildTime_363_);
lean_inc(v_trace_362_);
lean_inc(v_log_359_);
lean_dec(v_s_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_apply_1(v_f_357_, v_log_359_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_trace_362_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_buildTime_363_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3, v_action_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3 + 1, v_wantsRebuild_361_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object* v_e_372_, lean_object* v_s_373_){
_start:
{
lean_object* v_log_374_; uint8_t v_action_375_; uint8_t v_wantsRebuild_376_; lean_object* v_trace_377_; lean_object* v_buildTime_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_log_374_ = lean_ctor_get(v_s_373_, 0);
v_action_375_ = lean_ctor_get_uint8(v_s_373_, sizeof(void*)*3);
v_wantsRebuild_376_ = lean_ctor_get_uint8(v_s_373_, sizeof(void*)*3 + 1);
v_trace_377_ = lean_ctor_get(v_s_373_, 1);
v_buildTime_378_ = lean_ctor_get(v_s_373_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_s_373_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v_s_373_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_buildTime_378_);
lean_inc(v_trace_377_);
lean_inc(v_log_374_);
lean_dec(v_s_373_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_array_push(v_log_374_, v_e_372_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_trace_377_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_buildTime_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_385_, sizeof(void*)*3, v_action_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_385_, sizeof(void*)*3 + 1, v_wantsRebuild_376_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object* v_log_387_, lean_object* v_self_388_){
_start:
{
if (lean_obj_tag(v_self_388_) == 0)
{
lean_object* v_a_389_; lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_410_; 
v_a_389_ = lean_ctor_get(v_self_388_, 1);
v_a_390_ = lean_ctor_get(v_self_388_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_self_388_);
if (v_isSharedCheck_410_ == 0)
{
v___x_392_ = v_self_388_;
v_isShared_393_ = v_isSharedCheck_410_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_389_);
lean_inc(v_a_390_);
lean_dec(v_self_388_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_410_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_log_394_; uint8_t v_action_395_; uint8_t v_wantsRebuild_396_; lean_object* v_trace_397_; lean_object* v_buildTime_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_409_; 
v_log_394_ = lean_ctor_get(v_a_389_, 0);
v_action_395_ = lean_ctor_get_uint8(v_a_389_, sizeof(void*)*3);
v_wantsRebuild_396_ = lean_ctor_get_uint8(v_a_389_, sizeof(void*)*3 + 1);
v_trace_397_ = lean_ctor_get(v_a_389_, 1);
v_buildTime_398_ = lean_ctor_get(v_a_389_, 2);
v_isSharedCheck_409_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_409_ == 0)
{
v___x_400_ = v_a_389_;
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_buildTime_398_);
lean_inc(v_trace_397_);
lean_inc(v_log_394_);
lean_dec(v_a_389_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = l_Array_append___redArg(v_log_387_, v_log_394_);
lean_dec_ref(v_log_394_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_trace_397_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_buildTime_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*3, v_action_395_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*3 + 1, v_wantsRebuild_396_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_404_);
v___x_406_ = v___x_392_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_390_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_434_; 
v_a_411_ = lean_ctor_get(v_self_388_, 1);
v_a_412_ = lean_ctor_get(v_self_388_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_self_388_);
if (v_isSharedCheck_434_ == 0)
{
v___x_414_ = v_self_388_;
v_isShared_415_ = v_isSharedCheck_434_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_411_);
lean_inc(v_a_412_);
lean_dec(v_self_388_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_434_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_log_416_; uint8_t v_action_417_; uint8_t v_wantsRebuild_418_; lean_object* v_trace_419_; lean_object* v_buildTime_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_433_; 
v_log_416_ = lean_ctor_get(v_a_411_, 0);
v_action_417_ = lean_ctor_get_uint8(v_a_411_, sizeof(void*)*3);
v_wantsRebuild_418_ = lean_ctor_get_uint8(v_a_411_, sizeof(void*)*3 + 1);
v_trace_419_ = lean_ctor_get(v_a_411_, 1);
v_buildTime_420_ = lean_ctor_get(v_a_411_, 2);
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_411_);
if (v_isSharedCheck_433_ == 0)
{
v___x_422_ = v_a_411_;
v_isShared_423_ = v_isSharedCheck_433_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_buildTime_420_);
lean_inc(v_trace_419_);
lean_inc(v_log_416_);
lean_dec(v_a_411_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_433_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_424_ = lean_array_get_size(v_log_387_);
v___x_425_ = lean_nat_add(v___x_424_, v_a_412_);
lean_dec(v_a_412_);
v___x_426_ = l_Array_append___redArg(v_log_387_, v_log_416_);
lean_dec_ref(v_log_416_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_426_);
v___x_428_ = v___x_422_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_trace_419_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_buildTime_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3, v_action_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3 + 1, v_wantsRebuild_418_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_428_);
lean_ctor_set(v___x_414_, 0, v___x_425_);
v___x_430_ = v___x_414_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object* v_00_u03b1_435_, lean_object* v_log_436_, lean_object* v_self_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lake_JobResult_prependLog___redArg(v_log_436_, v_self_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = l_Lake_instInhabitedJobState_default;
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__1(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
v___x_443_ = lean_task_pure(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__3(void){
_start:
{
uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_445_ = 0;
v___x_446_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_447_ = lean_box(0);
v___x_448_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__1, &l_Lake_instInhabitedJob___closed__1_once, _init_l_Lake_instInhabitedJob___closed__1);
v___x_449_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_446_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*3, v___x_445_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__3, &l_Lake_instInhabitedJob___closed__3_once, _init_l_Lake_instInhabitedJob___closed__3);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_452_){
_start:
{
lean_inc_ref(v_self_452_);
return v_self_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lake_Job_cast___redArg(v_self_453_);
lean_dec_ref(v_self_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_455_, lean_object* v_self_456_, lean_object* v_h_457_){
_start:
{
lean_inc_ref(v_self_456_);
return v_self_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_458_, lean_object* v_self_459_, lean_object* v_h_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lake_Job_cast(v_00_u03b1_458_, v_self_459_, v_h_460_);
lean_dec_ref(v_self_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_462_, lean_object* v_task_463_, lean_object* v_caption_464_){
_start:
{
uint8_t v___x_465_; lean_object* v___x_466_; 
v___x_465_ = 0;
v___x_466_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_466_, 0, v_task_463_);
lean_ctor_set(v___x_466_, 1, v_inst_462_);
lean_ctor_set(v___x_466_, 2, v_caption_464_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*3, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_467_, lean_object* v_inst_468_, lean_object* v_task_469_, lean_object* v_caption_470_){
_start:
{
uint8_t v___x_471_; lean_object* v___x_472_; 
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_472_, 0, v_task_469_);
lean_ctor_set(v___x_472_, 1, v_inst_468_);
lean_ctor_set(v___x_472_, 2, v_caption_470_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*3, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_473_, lean_object* v_log_474_, lean_object* v_caption_475_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = 0;
v___x_478_ = 0;
v___x_479_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_480_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_480_, 0, v_log_474_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
lean_ctor_set(v___x_480_, 2, v___x_476_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*3, v___x_477_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*3 + 1, v___x_478_);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_476_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_task_pure(v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_inst_473_);
lean_ctor_set(v___x_483_, 2, v_caption_475_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*3, v___x_478_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_484_, lean_object* v_inst_485_, lean_object* v_log_486_, lean_object* v_caption_487_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = 0;
v___x_490_ = 0;
v___x_491_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_492_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_492_, 0, v_log_486_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_ctor_set(v___x_492_, 2, v___x_488_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*3, v___x_489_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*3 + 1, v___x_490_);
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_488_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_task_pure(v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_inst_485_);
lean_ctor_set(v___x_495_, 2, v_caption_487_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*3, v___x_490_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_496_, lean_object* v_a_497_, lean_object* v_log_498_, lean_object* v_caption_499_){
_start:
{
uint8_t v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_500_ = 0;
v___x_501_ = 0;
v___x_502_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_504_, 0, v_log_498_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
lean_ctor_set(v___x_504_, 2, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3, v___x_500_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3 + 1, v___x_501_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v_a_497_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = lean_task_pure(v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_kind_496_);
lean_ctor_set(v___x_507_, 2, v_caption_499_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3, v___x_501_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_508_, lean_object* v_kind_509_, lean_object* v_a_510_, lean_object* v_log_511_, lean_object* v_caption_512_){
_start:
{
uint8_t v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_513_ = 0;
v___x_514_ = 0;
v___x_515_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_517_, 0, v_log_511_);
lean_ctor_set(v___x_517_, 1, v___x_515_);
lean_ctor_set(v___x_517_, 2, v___x_516_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3, v___x_513_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3 + 1, v___x_514_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_510_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_task_pure(v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_kind_509_);
lean_ctor_set(v___x_520_, 2, v_caption_512_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*3, v___x_514_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_523_ = lean_box(0);
v___x_524_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_525_ = 0;
v___x_526_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_522_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_task_pure(v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_523_);
lean_ctor_set(v___x_529_, 2, v___x_524_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3, v___x_525_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_532_, lean_object* v_caption_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_534_ = lean_box(0);
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_537_ = 0;
v___x_538_ = 0;
v___x_539_ = l_Lake_BuildTrace_nil(v_caption_533_);
v___x_540_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_540_, 0, v___x_536_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
lean_ctor_set(v___x_540_, 2, v___x_535_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*3, v___x_537_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*3 + 1, v___x_538_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_a_532_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_task_pure(v___x_541_);
v___x_543_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_544_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_534_);
lean_ctor_set(v___x_544_, 2, v___x_543_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*3, v___x_538_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_545_, lean_object* v_a_546_, lean_object* v_caption_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_548_ = lean_box(0);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_551_ = 0;
v___x_552_ = 0;
v___x_553_ = l_Lake_BuildTrace_nil(v_caption_547_);
v___x_554_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_554_, 0, v___x_550_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
lean_ctor_set(v___x_554_, 2, v___x_549_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*3, v___x_551_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*3 + 1, v___x_552_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_a_546_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_task_pure(v___x_555_);
v___x_557_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_558_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_548_);
lean_ctor_set(v___x_558_, 2, v___x_557_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*3, v___x_552_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_559_, lean_object* v_caption_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_561_ = l_Lake_instDataKindUnit;
v___x_562_ = lean_box(0);
v___x_563_ = 0;
v___x_564_ = 0;
v___x_565_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_567_, 0, v_log_559_);
lean_ctor_set(v___x_567_, 1, v___x_565_);
lean_ctor_set(v___x_567_, 2, v___x_566_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3, v___x_563_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3 + 1, v___x_564_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_562_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_task_pure(v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_561_);
lean_ctor_set(v___x_570_, 2, v_caption_560_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*3, v___x_564_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_box(0);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_576_ = 0;
v___x_577_ = 0;
v___x_578_ = l_Lake_BuildTrace_nil(v_traceCaption_571_);
v___x_579_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_579_, 0, v___x_575_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
lean_ctor_set(v___x_579_, 2, v___x_574_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*3, v___x_576_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*3 + 1, v___x_577_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_572_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_task_pure(v___x_580_);
v___x_582_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_583_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_573_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*3, v___x_577_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_584_){
_start:
{
lean_object* v_task_585_; lean_object* v___x_586_; lean_object* v_a_587_; lean_object* v_trace_588_; 
v_task_585_ = lean_ctor_get(v_job_584_, 0);
lean_inc_ref(v_task_585_);
lean_dec_ref(v_job_584_);
v___x_586_ = lean_task_get_own(v_task_585_);
v_a_587_ = lean_ctor_get(v___x_586_, 1);
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v_trace_588_ = lean_ctor_get(v_a_587_, 1);
lean_inc_ref(v_trace_588_);
lean_dec(v_a_587_);
return v_trace_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_589_, lean_object* v_job_590_){
_start:
{
lean_object* v_task_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v_trace_594_; 
v_task_591_ = lean_ctor_get(v_job_590_, 0);
lean_inc_ref(v_task_591_);
lean_dec_ref(v_job_590_);
v___x_592_ = lean_task_get_own(v_task_591_);
v_a_593_ = lean_ctor_get(v___x_592_, 1);
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v_trace_594_ = lean_ctor_get(v_a_593_, 1);
lean_inc_ref(v_trace_594_);
lean_dec(v_a_593_);
return v_trace_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_595_, lean_object* v_job_596_){
_start:
{
lean_object* v_task_597_; lean_object* v_kind_598_; uint8_t v_optional_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_task_597_ = lean_ctor_get(v_job_596_, 0);
v_kind_598_ = lean_ctor_get(v_job_596_, 1);
v_optional_599_ = lean_ctor_get_uint8(v_job_596_, sizeof(void*)*3);
v_isSharedCheck_606_ = !lean_is_exclusive(v_job_596_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_job_596_, 2);
lean_dec(v_unused_607_);
v___x_601_ = v_job_596_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_kind_598_);
lean_inc(v_task_597_);
lean_dec(v_job_596_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 2, v_caption_595_);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_task_597_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_kind_598_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_caption_595_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*3, v_optional_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_608_, lean_object* v_caption_609_, lean_object* v_job_610_){
_start:
{
lean_object* v_task_611_; lean_object* v_kind_612_; uint8_t v_optional_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_task_611_ = lean_ctor_get(v_job_610_, 0);
v_kind_612_ = lean_ctor_get(v_job_610_, 1);
v_optional_613_ = lean_ctor_get_uint8(v_job_610_, sizeof(void*)*3);
v_isSharedCheck_620_ = !lean_is_exclusive(v_job_610_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_job_610_, 2);
lean_dec(v_unused_621_);
v___x_615_ = v_job_610_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_kind_612_);
lean_inc(v_task_611_);
lean_dec(v_job_610_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 2, v_caption_609_);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_task_611_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_kind_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_caption_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_619_, sizeof(void*)*3, v_optional_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_622_, lean_object* v_job_623_){
_start:
{
lean_object* v_task_624_; lean_object* v_kind_625_; lean_object* v_caption_626_; uint8_t v_optional_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_task_624_ = lean_ctor_get(v_job_623_, 0);
v_kind_625_ = lean_ctor_get(v_job_623_, 1);
v_caption_626_ = lean_ctor_get(v_job_623_, 2);
v_optional_627_ = lean_ctor_get_uint8(v_job_623_, sizeof(void*)*3);
v___x_628_ = lean_string_utf8_byte_size(v_caption_626_);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_nat_dec_eq(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec_ref(v_caption_622_);
return v_job_623_;
}
else
{
lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_inc(v_kind_625_);
lean_inc_ref(v_task_624_);
v_isSharedCheck_637_ = !lean_is_exclusive(v_job_623_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_638_ = lean_ctor_get(v_job_623_, 2);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_job_623_, 1);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_job_623_, 0);
lean_dec(v_unused_640_);
v___x_632_ = v_job_623_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_dec(v_job_623_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v_caption_622_);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_task_624_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_kind_625_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_caption_622_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*3, v_optional_627_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_641_, lean_object* v_caption_642_, lean_object* v_job_643_){
_start:
{
lean_object* v_task_644_; lean_object* v_kind_645_; lean_object* v_caption_646_; uint8_t v_optional_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_task_644_ = lean_ctor_get(v_job_643_, 0);
v_kind_645_ = lean_ctor_get(v_job_643_, 1);
v_caption_646_ = lean_ctor_get(v_job_643_, 2);
v_optional_647_ = lean_ctor_get_uint8(v_job_643_, sizeof(void*)*3);
v___x_648_ = lean_string_utf8_byte_size(v_caption_646_);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_nat_dec_eq(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
lean_dec_ref(v_caption_642_);
return v_job_643_;
}
else
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_inc(v_kind_645_);
lean_inc_ref(v_task_644_);
v_isSharedCheck_657_ = !lean_is_exclusive(v_job_643_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; lean_object* v_unused_660_; 
v_unused_658_ = lean_ctor_get(v_job_643_, 2);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_job_643_, 1);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_job_643_, 0);
lean_dec(v_unused_660_);
v___x_652_ = v_job_643_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_dec(v_job_643_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 2, v_caption_642_);
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_task_644_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_kind_645_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_caption_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_656_, sizeof(void*)*3, v_optional_647_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_661_, lean_object* v_f_662_, lean_object* v_self_663_, lean_object* v_prio_664_, uint8_t v_sync_665_){
_start:
{
lean_object* v_task_666_; lean_object* v_caption_667_; uint8_t v_optional_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
v_task_666_ = lean_ctor_get(v_self_663_, 0);
v_caption_667_ = lean_ctor_get(v_self_663_, 2);
v_optional_668_ = lean_ctor_get_uint8(v_self_663_, sizeof(void*)*3);
v_isSharedCheck_676_ = !lean_is_exclusive(v_self_663_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v_self_663_, 1);
lean_dec(v_unused_677_);
v___x_670_ = v_self_663_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_caption_667_);
lean_inc(v_task_666_);
lean_dec(v_self_663_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_task_map(v_f_662_, v_task_666_, v_prio_664_, v_sync_665_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_inst_661_);
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_inst_661_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_caption_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_675_, sizeof(void*)*3, v_optional_668_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_678_, lean_object* v_f_679_, lean_object* v_self_680_, lean_object* v_prio_681_, lean_object* v_sync_682_){
_start:
{
uint8_t v_sync_boxed_683_; lean_object* v_res_684_; 
v_sync_boxed_683_ = lean_unbox(v_sync_682_);
v_res_684_ = l_Lake_Job_mapResult___redArg(v_inst_678_, v_f_679_, v_self_680_, v_prio_681_, v_sync_boxed_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_685_, lean_object* v_00_u03b1_686_, lean_object* v_inst_687_, lean_object* v_f_688_, lean_object* v_self_689_, lean_object* v_prio_690_, uint8_t v_sync_691_){
_start:
{
lean_object* v_task_692_; lean_object* v_caption_693_; uint8_t v_optional_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_task_692_ = lean_ctor_get(v_self_689_, 0);
v_caption_693_ = lean_ctor_get(v_self_689_, 2);
v_optional_694_ = lean_ctor_get_uint8(v_self_689_, sizeof(void*)*3);
v_isSharedCheck_702_ = !lean_is_exclusive(v_self_689_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_self_689_, 1);
lean_dec(v_unused_703_);
v___x_696_ = v_self_689_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_caption_693_);
lean_inc(v_task_692_);
lean_dec(v_self_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_task_map(v_f_688_, v_task_692_, v_prio_690_, v_sync_691_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_inst_687_);
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_inst_687_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_caption_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*3, v_optional_694_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_704_, lean_object* v_00_u03b1_705_, lean_object* v_inst_706_, lean_object* v_f_707_, lean_object* v_self_708_, lean_object* v_prio_709_, lean_object* v_sync_710_){
_start:
{
uint8_t v_sync_boxed_711_; lean_object* v_res_712_; 
v_sync_boxed_711_ = lean_unbox(v_sync_710_);
v_res_712_ = l_Lake_Job_mapResult(v_00_u03b2_704_, v_00_u03b1_705_, v_inst_706_, v_f_707_, v_self_708_, v_prio_709_, v_sync_boxed_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_713_, lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_715_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_a_715_);
v_a_716_ = lean_ctor_get(v_x_714_, 1);
lean_inc(v_a_716_);
lean_dec_ref(v_x_714_);
v___x_717_ = lean_apply_2(v_f_713_, v_a_715_, v_a_716_);
return v___x_717_;
}
else
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v_f_713_);
v_a_718_ = lean_ctor_get(v_x_714_, 0);
v_a_719_ = lean_ctor_get(v_x_714_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_714_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v_x_714_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_inc(v_a_718_);
lean_dec(v_x_714_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_718_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_727_, lean_object* v_f_728_, lean_object* v_self_729_, lean_object* v_prio_730_, uint8_t v_sync_731_){
_start:
{
lean_object* v_task_732_; lean_object* v_caption_733_; uint8_t v_optional_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_743_; 
v_task_732_ = lean_ctor_get(v_self_729_, 0);
v_caption_733_ = lean_ctor_get(v_self_729_, 2);
v_optional_734_ = lean_ctor_get_uint8(v_self_729_, sizeof(void*)*3);
v_isSharedCheck_743_ = !lean_is_exclusive(v_self_729_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_self_729_, 1);
lean_dec(v_unused_744_);
v___x_736_ = v_self_729_;
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_caption_733_);
lean_inc(v_task_732_);
lean_dec(v_self_729_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___f_738_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_738_, 0, v_f_728_);
v___x_739_ = lean_task_map(v___f_738_, v_task_732_, v_prio_730_, v_sync_731_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_inst_727_);
lean_ctor_set(v___x_736_, 0, v___x_739_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_inst_727_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_caption_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*3, v_optional_734_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* v_inst_745_, lean_object* v_f_746_, lean_object* v_self_747_, lean_object* v_prio_748_, lean_object* v_sync_749_){
_start:
{
uint8_t v_sync_boxed_750_; lean_object* v_res_751_; 
v_sync_boxed_750_ = lean_unbox(v_sync_749_);
v_res_751_ = l_Lake_Job_mapOk___redArg(v_inst_745_, v_f_746_, v_self_747_, v_prio_748_, v_sync_boxed_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_752_, lean_object* v_00_u03b1_753_, lean_object* v_inst_754_, lean_object* v_f_755_, lean_object* v_self_756_, lean_object* v_prio_757_, uint8_t v_sync_758_){
_start:
{
lean_object* v_task_759_; lean_object* v_caption_760_; uint8_t v_optional_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_770_; 
v_task_759_ = lean_ctor_get(v_self_756_, 0);
v_caption_760_ = lean_ctor_get(v_self_756_, 2);
v_optional_761_ = lean_ctor_get_uint8(v_self_756_, sizeof(void*)*3);
v_isSharedCheck_770_ = !lean_is_exclusive(v_self_756_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v_self_756_, 1);
lean_dec(v_unused_771_);
v___x_763_ = v_self_756_;
v_isShared_764_ = v_isSharedCheck_770_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_caption_760_);
lean_inc(v_task_759_);
lean_dec(v_self_756_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_770_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___f_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___f_765_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_765_, 0, v_f_755_);
v___x_766_ = lean_task_map(v___f_765_, v_task_759_, v_prio_757_, v_sync_758_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v_inst_754_);
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_inst_754_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_caption_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*3, v_optional_761_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_772_, lean_object* v_00_u03b1_773_, lean_object* v_inst_774_, lean_object* v_f_775_, lean_object* v_self_776_, lean_object* v_prio_777_, lean_object* v_sync_778_){
_start:
{
uint8_t v_sync_boxed_779_; lean_object* v_res_780_; 
v_sync_boxed_779_ = lean_unbox(v_sync_778_);
v_res_780_ = l_Lake_Job_mapOk(v_00_u03b2_772_, v_00_u03b1_773_, v_inst_774_, v_f_775_, v_self_776_, v_prio_777_, v_sync_boxed_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_792_; 
v_a_783_ = lean_ctor_get(v_x_782_, 0);
v_a_784_ = lean_ctor_get(v_x_782_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_792_ == 0)
{
v___x_786_ = v_x_782_;
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_inc(v_a_783_);
lean_dec(v_x_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_apply_1(v_f_781_, v_a_783_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_a_784_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_f_781_);
v_a_793_ = lean_ctor_get(v_x_782_, 0);
v_a_794_ = lean_ctor_get(v_x_782_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v_x_782_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_inc(v_a_793_);
lean_dec(v_x_782_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_793_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_802_, lean_object* v_f_803_, lean_object* v_self_804_, lean_object* v_prio_805_, uint8_t v_sync_806_){
_start:
{
lean_object* v_task_807_; lean_object* v_caption_808_; uint8_t v_optional_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_task_807_ = lean_ctor_get(v_self_804_, 0);
v_caption_808_ = lean_ctor_get(v_self_804_, 2);
v_optional_809_ = lean_ctor_get_uint8(v_self_804_, sizeof(void*)*3);
v_isSharedCheck_818_ = !lean_is_exclusive(v_self_804_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_self_804_, 1);
lean_dec(v_unused_819_);
v___x_811_ = v_self_804_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_caption_808_);
lean_inc(v_task_807_);
lean_dec(v_self_804_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___f_813_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_813_, 0, v_f_803_);
v___x_814_ = lean_task_map(v___f_813_, v_task_807_, v_prio_805_, v_sync_806_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v_inst_802_);
lean_ctor_set(v___x_811_, 0, v___x_814_);
v___x_816_ = v___x_811_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_inst_802_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_caption_808_);
lean_ctor_set_uint8(v_reuseFailAlloc_817_, sizeof(void*)*3, v_optional_809_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_820_, lean_object* v_f_821_, lean_object* v_self_822_, lean_object* v_prio_823_, lean_object* v_sync_824_){
_start:
{
uint8_t v_sync_boxed_825_; lean_object* v_res_826_; 
v_sync_boxed_825_ = lean_unbox(v_sync_824_);
v_res_826_ = l_Lake_Job_map___redArg(v_inst_820_, v_f_821_, v_self_822_, v_prio_823_, v_sync_boxed_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_827_, lean_object* v_00_u03b1_828_, lean_object* v_inst_829_, lean_object* v_f_830_, lean_object* v_self_831_, lean_object* v_prio_832_, uint8_t v_sync_833_){
_start:
{
lean_object* v_task_834_; lean_object* v_caption_835_; uint8_t v_optional_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_845_; 
v_task_834_ = lean_ctor_get(v_self_831_, 0);
v_caption_835_ = lean_ctor_get(v_self_831_, 2);
v_optional_836_ = lean_ctor_get_uint8(v_self_831_, sizeof(void*)*3);
v_isSharedCheck_845_ = !lean_is_exclusive(v_self_831_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_self_831_, 1);
lean_dec(v_unused_846_);
v___x_838_ = v_self_831_;
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_caption_835_);
lean_inc(v_task_834_);
lean_dec(v_self_831_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___f_840_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_840_, 0, v_f_830_);
v___x_841_ = lean_task_map(v___f_840_, v_task_834_, v_prio_832_, v_sync_833_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_inst_829_);
lean_ctor_set(v___x_838_, 0, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_inst_829_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_caption_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*3, v_optional_836_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_847_, lean_object* v_00_u03b1_848_, lean_object* v_inst_849_, lean_object* v_f_850_, lean_object* v_self_851_, lean_object* v_prio_852_, lean_object* v_sync_853_){
_start:
{
uint8_t v_sync_boxed_854_; lean_object* v_res_855_; 
v_sync_boxed_854_ = lean_unbox(v_sync_853_);
v_res_855_ = l_Lake_Job_map(v_00_u03b2_847_, v_00_u03b1_848_, v_inst_849_, v_f_850_, v_self_851_, v_prio_852_, v_sync_boxed_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_f_858_, lean_object* v_self_859_){
_start:
{
lean_object* v_task_860_; lean_object* v_caption_861_; uint8_t v_optional_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_874_; 
v_task_860_ = lean_ctor_get(v_self_859_, 0);
v_caption_861_ = lean_ctor_get(v_self_859_, 2);
v_optional_862_ = lean_ctor_get_uint8(v_self_859_, sizeof(void*)*3);
v_isSharedCheck_874_ = !lean_is_exclusive(v_self_859_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v_self_859_, 1);
lean_dec(v_unused_875_);
v___x_864_ = v_self_859_;
v_isShared_865_ = v_isSharedCheck_874_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_caption_861_);
lean_inc(v_task_860_);
lean_dec(v_self_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_874_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___f_866_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_866_, 0, v_f_858_);
v___x_867_ = lean_box(0);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = 0;
v___x_870_ = lean_task_map(v___f_866_, v_task_860_, v___x_868_, v___x_869_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_867_);
lean_ctor_set(v___x_864_, 0, v___x_870_);
v___x_872_ = v___x_864_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_caption_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_873_, sizeof(void*)*3, v_optional_862_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_876_, lean_object* v_00_u03b1_877_, lean_object* v_00_u03b2_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_881_, 0, lean_box(0));
lean_closure_set(v___x_881_, 1, lean_box(0));
lean_closure_set(v___x_881_, 2, v___y_879_);
v___x_882_ = lean_apply_4(v___f_876_, lean_box(0), lean_box(0), v___x_881_, v___y_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_890_){
_start:
{
lean_inc_ref(v_self_890_);
return v_self_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_891_);
lean_dec_ref(v_self_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_893_, lean_object* v_self_894_){
_start:
{
lean_inc_ref(v_self_894_);
return v_self_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_895_, lean_object* v_self_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_895_, v_self_896_);
lean_dec_ref(v_self_896_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0));
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_901_){
_start:
{
lean_object* v_task_902_; lean_object* v_caption_903_; uint8_t v_optional_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_912_; 
v_task_902_ = lean_ctor_get(v_job_901_, 0);
v_caption_903_ = lean_ctor_get(v_job_901_, 2);
v_optional_904_ = lean_ctor_get_uint8(v_job_901_, sizeof(void*)*3);
v_isSharedCheck_912_ = !lean_is_exclusive(v_job_901_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v_job_901_, 1);
lean_dec(v_unused_913_);
v___x_906_ = v_job_901_;
v_isShared_907_ = v_isSharedCheck_912_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_caption_903_);
lean_inc(v_task_902_);
lean_dec(v_job_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_912_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_box(0);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_908_);
v___x_910_ = v___x_906_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_task_902_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_caption_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, sizeof(void*)*3, v_optional_904_);
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
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_914_, lean_object* v_job_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lake_Job_toOpaque___redArg(v_job_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* v_00_u03b1_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___closed__0));
return v___x_919_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Task(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Opaque(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Trace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Job_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
