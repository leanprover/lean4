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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
extern lean_object* l_Lake_instInhabitedLog_default;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
extern lean_object* l_Lake_Log_instInhabitedPos_default;
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
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_instReprJobAction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.JobAction.replay"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__2 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__3 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__3_value;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.JobAction.fetch"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__4 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__5 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__5_value;
static const lean_string_object l_Lake_instReprJobAction_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.JobAction.build"};
static const lean_object* l_Lake_instReprJobAction_repr___closed__6 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprJobAction_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprJobAction_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprJobAction_repr___closed__7 = (const lean_object*)&l_Lake_instReprJobAction_repr___closed__7_value;
static lean_once_cell_t l_Lake_instReprJobAction_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprJobAction_repr___closed__8;
static lean_once_cell_t l_Lake_instReprJobAction_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprJobAction_repr___closed__9;
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
static const lean_string_object l_Lake_JobAction_verb___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Replayed"};
static const lean_object* l_Lake_JobAction_verb___closed__2 = (const lean_object*)&l_Lake_JobAction_verb___closed__2_value;
static const lean_string_object l_Lake_JobAction_verb___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Replaying"};
static const lean_object* l_Lake_JobAction_verb___closed__3 = (const lean_object*)&l_Lake_JobAction_verb___closed__3_value;
static const lean_string_object l_Lake_JobAction_verb___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Fetched"};
static const lean_object* l_Lake_JobAction_verb___closed__4 = (const lean_object*)&l_Lake_JobAction_verb___closed__4_value;
static const lean_string_object l_Lake_JobAction_verb___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Fetching"};
static const lean_object* l_Lake_JobAction_verb___closed__5 = (const lean_object*)&l_Lake_JobAction_verb___closed__5_value;
static const lean_string_object l_Lake_JobAction_verb___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Built"};
static const lean_object* l_Lake_JobAction_verb___closed__6 = (const lean_object*)&l_Lake_JobAction_verb___closed__6_value;
static const lean_string_object l_Lake_JobAction_verb___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Building"};
static const lean_object* l_Lake_JobAction_verb___closed__7 = (const lean_object*)&l_Lake_JobAction_verb___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedJobState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_instInhabitedJobState_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedJobState_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedJobState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJobState_default___closed__1;
static lean_once_cell_t l_Lake_instInhabitedJobState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedJobState_default___closed__2;
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
static const lean_array_object l_Lake_Job_instPure___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Job_instPure___lam__0___closed__0 = (const lean_object*)&l_Lake_Job_instPure___lam__0___closed__0_value;
static lean_once_cell_t l_Lake_Job_instPure___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Job_instPure___lam__0___closed__1;
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
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lake_JobAction_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lake_JobAction_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Lake_JobAction_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lake_JobAction_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Lake_JobAction_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg(lean_object* v_unknown_29_){
_start:
{
lean_inc(v_unknown_29_);
return v_unknown_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg___boxed(lean_object* v_unknown_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lake_JobAction_unknown_elim___redArg(v_unknown_30_);
lean_dec(v_unknown_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_unknown_35_){
_start:
{
lean_inc(v_unknown_35_);
return v_unknown_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_unknown_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Lake_JobAction_unknown_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_unknown_39_);
lean_dec(v_unknown_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg(lean_object* v_replay_42_){
_start:
{
lean_inc(v_replay_42_);
return v_replay_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___redArg___boxed(lean_object* v_replay_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lake_JobAction_replay_elim___redArg(v_replay_43_);
lean_dec(v_replay_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_replay_48_){
_start:
{
lean_inc(v_replay_48_);
return v_replay_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_replay_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lake_JobAction_replay_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_replay_52_);
lean_dec(v_replay_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg(lean_object* v_fetch_55_){
_start:
{
lean_inc(v_fetch_55_);
return v_fetch_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg___boxed(lean_object* v_fetch_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lake_JobAction_fetch_elim___redArg(v_fetch_56_);
lean_dec(v_fetch_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_fetch_61_){
_start:
{
lean_inc(v_fetch_61_);
return v_fetch_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_fetch_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Lake_JobAction_fetch_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_fetch_65_);
lean_dec(v_fetch_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg(lean_object* v_build_68_){
_start:
{
lean_inc(v_build_68_);
return v_build_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg___boxed(lean_object* v_build_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lake_JobAction_build_elim___redArg(v_build_69_);
lean_dec(v_build_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_build_74_){
_start:
{
lean_inc(v_build_74_);
return v_build_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_build_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Lake_JobAction_build_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_build_78_);
lean_dec(v_build_78_);
return v_res_80_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction_default(void){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction(void){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__8(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(2u);
v___x_96_ = lean_nat_to_int(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__9(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_to_int(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr(uint8_t v_x_99_, lean_object* v_prec_100_){
_start:
{
lean_object* v___y_102_; lean_object* v___y_109_; lean_object* v___y_116_; lean_object* v___y_123_; 
switch(v_x_99_)
{
case 0:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1024u);
v___x_130_ = lean_nat_dec_le(v___x_129_, v_prec_100_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__8, &l_Lake_instReprJobAction_repr___closed__8_once, _init_l_Lake_instReprJobAction_repr___closed__8);
v___y_102_ = v___x_131_;
goto v___jp_101_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__9, &l_Lake_instReprJobAction_repr___closed__9_once, _init_l_Lake_instReprJobAction_repr___closed__9);
v___y_102_ = v___x_132_;
goto v___jp_101_;
}
}
case 1:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1024u);
v___x_134_ = lean_nat_dec_le(v___x_133_, v_prec_100_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__8, &l_Lake_instReprJobAction_repr___closed__8_once, _init_l_Lake_instReprJobAction_repr___closed__8);
v___y_109_ = v___x_135_;
goto v___jp_108_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__9, &l_Lake_instReprJobAction_repr___closed__9_once, _init_l_Lake_instReprJobAction_repr___closed__9);
v___y_109_ = v___x_136_;
goto v___jp_108_;
}
}
case 2:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1024u);
v___x_138_ = lean_nat_dec_le(v___x_137_, v_prec_100_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__8, &l_Lake_instReprJobAction_repr___closed__8_once, _init_l_Lake_instReprJobAction_repr___closed__8);
v___y_116_ = v___x_139_;
goto v___jp_115_;
}
else
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__9, &l_Lake_instReprJobAction_repr___closed__9_once, _init_l_Lake_instReprJobAction_repr___closed__9);
v___y_116_ = v___x_140_;
goto v___jp_115_;
}
}
default: 
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = lean_nat_dec_le(v___x_141_, v_prec_100_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__8, &l_Lake_instReprJobAction_repr___closed__8_once, _init_l_Lake_instReprJobAction_repr___closed__8);
v___y_123_ = v___x_143_;
goto v___jp_122_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__9, &l_Lake_instReprJobAction_repr___closed__9_once, _init_l_Lake_instReprJobAction_repr___closed__9);
v___y_123_ = v___x_144_;
goto v___jp_122_;
}
}
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_103_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__1));
v___x_104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = 0;
v___x_106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_105_);
v___x_107_ = l_Repr_addAppParen(v___x_106_, v_prec_100_);
return v___x_107_;
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__3));
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___y_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = l_Repr_addAppParen(v___x_113_, v_prec_100_);
return v___x_114_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_117_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__5));
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___y_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = 0;
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
v___x_121_ = l_Repr_addAppParen(v___x_120_, v_prec_100_);
return v___x_121_;
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__7));
v___x_125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_125_, 0, v___y_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = 0;
v___x_127_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*1, v___x_126_);
v___x_128_ = l_Repr_addAppParen(v___x_127_, v_prec_100_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr___boxed(lean_object* v_x_145_, lean_object* v_prec_146_){
_start:
{
uint8_t v_x_233__boxed_147_; lean_object* v_res_148_; 
v_x_233__boxed_147_ = lean_unbox(v_x_145_);
v_res_148_ = l_Lake_instReprJobAction_repr(v_x_233__boxed_147_, v_prec_146_);
lean_dec(v_prec_146_);
return v_res_148_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_ofNat(lean_object* v_n_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_dec_le(v_n_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(2u);
v___x_155_ = lean_nat_dec_le(v_n_151_, v___x_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = 3;
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 2;
return v___x_157_;
}
}
else
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_le(v_n_151_, v___x_158_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = 1;
return v___x_160_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ofNat___boxed(lean_object* v_n_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Lake_JobAction_ofNat(v_n_162_);
lean_dec(v_n_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqJobAction(uint8_t v_x_165_, uint8_t v_y_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_167_ = l_Lake_JobAction_ctorIdx(v_x_165_);
v___x_168_ = l_Lake_JobAction_ctorIdx(v_y_166_);
v___x_169_ = lean_nat_dec_eq(v___x_167_, v___x_168_);
lean_dec(v___x_168_);
lean_dec(v___x_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqJobAction___boxed(lean_object* v_x_170_, lean_object* v_y_171_){
_start:
{
uint8_t v_x_13__boxed_172_; uint8_t v_y_14__boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_x_13__boxed_172_ = lean_unbox(v_x_170_);
v_y_14__boxed_173_ = lean_unbox(v_y_171_);
v_res_174_ = l_Lake_instDecidableEqJobAction(v_x_13__boxed_172_, v_y_14__boxed_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdJobAction_ord(uint8_t v_x_176_, uint8_t v_y_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = l_Lake_JobAction_ctorIdx(v_x_176_);
v___x_179_ = l_Lake_JobAction_ctorIdx(v_y_177_);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_eq(v___x_178_, v___x_179_);
lean_dec(v___x_179_);
lean_dec(v___x_178_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; 
v___x_182_ = 2;
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = 1;
return v___x_183_;
}
}
else
{
uint8_t v___x_184_; 
lean_dec(v___x_179_);
lean_dec(v___x_178_);
v___x_184_ = 0;
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdJobAction_ord___boxed(lean_object* v_x_185_, lean_object* v_y_186_){
_start:
{
uint8_t v_x_30__boxed_187_; uint8_t v_y_31__boxed_188_; uint8_t v_res_189_; lean_object* v_r_190_; 
v_x_30__boxed_187_ = lean_unbox(v_x_185_);
v_y_31__boxed_188_ = lean_unbox(v_y_186_);
v_res_189_ = l_Lake_instOrdJobAction_ord(v_x_30__boxed_187_, v_y_31__boxed_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
static lean_object* _init_l_Lake_JobAction_instLT(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
static lean_object* _init_l_Lake_JobAction_instLE(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_instMin___lam__0(uint8_t v_x_195_, uint8_t v_y_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Lake_instOrdJobAction_ord(v_x_195_, v_y_196_);
if (v___x_197_ == 2)
{
return v_y_196_;
}
else
{
return v_x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMin___lam__0___boxed(lean_object* v_x_198_, lean_object* v_y_199_){
_start:
{
uint8_t v_x_boxed_200_; uint8_t v_y_boxed_201_; uint8_t v_res_202_; lean_object* v_r_203_; 
v_x_boxed_200_ = lean_unbox(v_x_198_);
v_y_boxed_201_ = lean_unbox(v_y_199_);
v_res_202_ = l_Lake_JobAction_instMin___lam__0(v_x_boxed_200_, v_y_boxed_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_instMax___lam__0(uint8_t v_x_206_, uint8_t v_y_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Lake_instOrdJobAction_ord(v_x_206_, v_y_207_);
if (v___x_208_ == 2)
{
return v_x_206_;
}
else
{
return v_y_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMax___lam__0___boxed(lean_object* v_x_209_, lean_object* v_y_210_){
_start:
{
uint8_t v_x_boxed_211_; uint8_t v_y_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_x_boxed_211_ = lean_unbox(v_x_209_);
v_y_boxed_212_ = lean_unbox(v_y_210_);
v_res_213_ = l_Lake_JobAction_instMax___lam__0(v_x_boxed_211_, v_y_boxed_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_merge(uint8_t v_a_217_, uint8_t v_b_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Lake_instOrdJobAction_ord(v_a_217_, v_b_218_);
if (v___x_219_ == 2)
{
return v_a_217_;
}
else
{
return v_b_218_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_merge___boxed(lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
uint8_t v_a_boxed_222_; uint8_t v_b_boxed_223_; uint8_t v_res_224_; lean_object* v_r_225_; 
v_a_boxed_222_ = lean_unbox(v_a_220_);
v_b_boxed_223_ = lean_unbox(v_b_221_);
v_res_224_ = l_Lake_JobAction_merge(v_a_boxed_222_, v_b_boxed_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb(uint8_t v_failed_234_, uint8_t v_x_235_){
_start:
{
switch(v_x_235_)
{
case 0:
{
if (v_failed_234_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = ((lean_object*)(l_Lake_JobAction_verb___closed__0));
return v___x_236_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = ((lean_object*)(l_Lake_JobAction_verb___closed__1));
return v___x_237_;
}
}
case 1:
{
if (v_failed_234_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = ((lean_object*)(l_Lake_JobAction_verb___closed__2));
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = ((lean_object*)(l_Lake_JobAction_verb___closed__3));
return v___x_239_;
}
}
case 2:
{
if (v_failed_234_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = ((lean_object*)(l_Lake_JobAction_verb___closed__4));
return v___x_240_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = ((lean_object*)(l_Lake_JobAction_verb___closed__5));
return v___x_241_;
}
}
default: 
{
if (v_failed_234_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = ((lean_object*)(l_Lake_JobAction_verb___closed__6));
return v___x_242_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l_Lake_JobAction_verb___closed__7));
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object* v_failed_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_failed_boxed_246_; uint8_t v_x_172__boxed_247_; lean_object* v_res_248_; 
v_failed_boxed_246_ = lean_unbox(v_failed_244_);
v_x_172__boxed_247_ = lean_unbox(v_x_245_);
v_res_248_ = l_Lake_JobAction_verb(v_failed_boxed_246_, v_x_172__boxed_247_);
return v_res_248_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_251_ = l_Lake_BuildTrace_nil(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__1, &l_Lake_instInhabitedJobState_default___closed__1_once, _init_l_Lake_instInhabitedJobState_default___closed__1);
v___x_254_ = 0;
v___x_255_ = 0;
v___x_256_ = l_Lake_instInhabitedLog_default;
v___x_257_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_253_);
lean_ctor_set(v___x_257_, 2, v___x_252_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*3, v___x_255_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*3 + 1, v___x_254_);
return v___x_257_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
return v___x_258_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState(void){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lake_instInhabitedJobState_default;
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object* v_a_260_, lean_object* v_b_261_){
_start:
{
lean_object* v_log_262_; uint8_t v_action_263_; uint8_t v_wantsRebuild_264_; lean_object* v_trace_265_; lean_object* v_buildTime_266_; lean_object* v_log_267_; uint8_t v_action_268_; uint8_t v_wantsRebuild_269_; lean_object* v_trace_270_; lean_object* v_buildTime_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_284_; 
v_log_262_ = lean_ctor_get(v_a_260_, 0);
lean_inc_ref(v_log_262_);
v_action_263_ = lean_ctor_get_uint8(v_a_260_, sizeof(void*)*3);
v_wantsRebuild_264_ = lean_ctor_get_uint8(v_a_260_, sizeof(void*)*3 + 1);
v_trace_265_ = lean_ctor_get(v_a_260_, 1);
lean_inc_ref(v_trace_265_);
v_buildTime_266_ = lean_ctor_get(v_a_260_, 2);
lean_inc(v_buildTime_266_);
lean_dec_ref(v_a_260_);
v_log_267_ = lean_ctor_get(v_b_261_, 0);
v_action_268_ = lean_ctor_get_uint8(v_b_261_, sizeof(void*)*3);
v_wantsRebuild_269_ = lean_ctor_get_uint8(v_b_261_, sizeof(void*)*3 + 1);
v_trace_270_ = lean_ctor_get(v_b_261_, 1);
v_buildTime_271_ = lean_ctor_get(v_b_261_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_b_261_);
if (v_isSharedCheck_284_ == 0)
{
v___x_273_ = v_b_261_;
v_isShared_274_ = v_isSharedCheck_284_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_buildTime_271_);
lean_inc(v_trace_270_);
lean_inc(v_log_267_);
lean_dec(v_b_261_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_284_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; uint8_t v___x_276_; uint8_t v___y_278_; 
v___x_275_ = l_Array_append___redArg(v_log_262_, v_log_267_);
lean_dec_ref(v_log_267_);
v___x_276_ = l_Lake_JobAction_merge(v_action_263_, v_action_268_);
if (v_wantsRebuild_264_ == 0)
{
v___y_278_ = v_wantsRebuild_269_;
goto v___jp_277_;
}
else
{
v___y_278_ = v_wantsRebuild_264_;
goto v___jp_277_;
}
v___jp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = l_Lake_BuildTrace_mix(v_trace_265_, v_trace_270_);
v___x_280_ = lean_nat_add(v_buildTime_266_, v_buildTime_271_);
lean_dec(v_buildTime_271_);
lean_dec(v_buildTime_266_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 2, v___x_280_);
lean_ctor_set(v___x_273_, 1, v___x_279_);
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_282_ = v___x_273_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*3, v___x_276_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*3 + 1, v___y_278_);
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object* v_f_285_, lean_object* v_s_286_){
_start:
{
lean_object* v_log_287_; uint8_t v_action_288_; uint8_t v_wantsRebuild_289_; lean_object* v_trace_290_; lean_object* v_buildTime_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_log_287_ = lean_ctor_get(v_s_286_, 0);
v_action_288_ = lean_ctor_get_uint8(v_s_286_, sizeof(void*)*3);
v_wantsRebuild_289_ = lean_ctor_get_uint8(v_s_286_, sizeof(void*)*3 + 1);
v_trace_290_ = lean_ctor_get(v_s_286_, 1);
v_buildTime_291_ = lean_ctor_get(v_s_286_, 2);
v_isSharedCheck_299_ = !lean_is_exclusive(v_s_286_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v_s_286_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_buildTime_291_);
lean_inc(v_trace_290_);
lean_inc(v_log_287_);
lean_dec(v_s_286_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_apply_1(v_f_285_, v_log_287_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_trace_290_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_buildTime_291_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*3, v_action_288_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*3 + 1, v_wantsRebuild_289_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object* v_e_300_, lean_object* v_s_301_){
_start:
{
lean_object* v_log_302_; uint8_t v_action_303_; uint8_t v_wantsRebuild_304_; lean_object* v_trace_305_; lean_object* v_buildTime_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_log_302_ = lean_ctor_get(v_s_301_, 0);
v_action_303_ = lean_ctor_get_uint8(v_s_301_, sizeof(void*)*3);
v_wantsRebuild_304_ = lean_ctor_get_uint8(v_s_301_, sizeof(void*)*3 + 1);
v_trace_305_ = lean_ctor_get(v_s_301_, 1);
v_buildTime_306_ = lean_ctor_get(v_s_301_, 2);
v_isSharedCheck_314_ = !lean_is_exclusive(v_s_301_);
if (v_isSharedCheck_314_ == 0)
{
v___x_308_ = v_s_301_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_buildTime_306_);
lean_inc(v_trace_305_);
lean_inc(v_log_302_);
lean_dec(v_s_301_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_array_push(v_log_302_, v_e_300_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_trace_305_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_buildTime_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*3, v_action_303_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*3 + 1, v_wantsRebuild_304_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object* v_log_315_, lean_object* v_self_316_){
_start:
{
if (lean_obj_tag(v_self_316_) == 0)
{
lean_object* v_a_317_; lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_338_; 
v_a_317_ = lean_ctor_get(v_self_316_, 1);
v_a_318_ = lean_ctor_get(v_self_316_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_self_316_);
if (v_isSharedCheck_338_ == 0)
{
v___x_320_ = v_self_316_;
v_isShared_321_ = v_isSharedCheck_338_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_317_);
lean_inc(v_a_318_);
lean_dec(v_self_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_338_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_log_322_; uint8_t v_action_323_; uint8_t v_wantsRebuild_324_; lean_object* v_trace_325_; lean_object* v_buildTime_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_337_; 
v_log_322_ = lean_ctor_get(v_a_317_, 0);
v_action_323_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*3);
v_wantsRebuild_324_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*3 + 1);
v_trace_325_ = lean_ctor_get(v_a_317_, 1);
v_buildTime_326_ = lean_ctor_get(v_a_317_, 2);
v_isSharedCheck_337_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_337_ == 0)
{
v___x_328_ = v_a_317_;
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_buildTime_326_);
lean_inc(v_trace_325_);
lean_inc(v_log_322_);
lean_dec(v_a_317_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = l_Array_append___redArg(v_log_315_, v_log_322_);
lean_dec_ref(v_log_322_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_trace_325_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_buildTime_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*3, v_action_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*3 + 1, v_wantsRebuild_324_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_332_);
v___x_334_ = v___x_320_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_318_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_362_; 
v_a_339_ = lean_ctor_get(v_self_316_, 1);
v_a_340_ = lean_ctor_get(v_self_316_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_self_316_);
if (v_isSharedCheck_362_ == 0)
{
v___x_342_ = v_self_316_;
v_isShared_343_ = v_isSharedCheck_362_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_339_);
lean_inc(v_a_340_);
lean_dec(v_self_316_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_362_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_log_344_; uint8_t v_action_345_; uint8_t v_wantsRebuild_346_; lean_object* v_trace_347_; lean_object* v_buildTime_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_361_; 
v_log_344_ = lean_ctor_get(v_a_339_, 0);
v_action_345_ = lean_ctor_get_uint8(v_a_339_, sizeof(void*)*3);
v_wantsRebuild_346_ = lean_ctor_get_uint8(v_a_339_, sizeof(void*)*3 + 1);
v_trace_347_ = lean_ctor_get(v_a_339_, 1);
v_buildTime_348_ = lean_ctor_get(v_a_339_, 2);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_339_);
if (v_isSharedCheck_361_ == 0)
{
v___x_350_ = v_a_339_;
v_isShared_351_ = v_isSharedCheck_361_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_buildTime_348_);
lean_inc(v_trace_347_);
lean_inc(v_log_344_);
lean_dec(v_a_339_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_361_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_352_ = lean_array_get_size(v_log_315_);
v___x_353_ = lean_nat_add(v___x_352_, v_a_340_);
lean_dec(v_a_340_);
v___x_354_ = l_Array_append___redArg(v_log_315_, v_log_344_);
lean_dec_ref(v_log_344_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_354_);
v___x_356_ = v___x_350_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_trace_347_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_buildTime_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*3, v_action_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*3 + 1, v_wantsRebuild_346_);
v___x_356_ = v_reuseFailAlloc_360_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_358_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_356_);
lean_ctor_set(v___x_342_, 0, v___x_353_);
v___x_358_ = v___x_342_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_353_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object* v_00_u03b1_363_, lean_object* v_log_364_, lean_object* v_self_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lake_JobResult_prependLog___redArg(v_log_364_, v_self_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = l_Lake_instInhabitedJobState_default;
v___x_368_ = l_Lake_Log_instInhabitedPos_default;
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
v___x_371_ = lean_task_pure(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__3(void){
_start:
{
uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_373_ = 0;
v___x_374_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_375_ = lean_box(0);
v___x_376_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__1, &l_Lake_instInhabitedJob___closed__1_once, _init_l_Lake_instInhabitedJob___closed__1);
v___x_377_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
lean_ctor_set(v___x_377_, 2, v___x_374_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*3, v___x_373_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__3, &l_Lake_instInhabitedJob___closed__3_once, _init_l_Lake_instInhabitedJob___closed__3);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_380_){
_start:
{
lean_inc_ref(v_self_380_);
return v_self_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_Job_cast___redArg(v_self_381_);
lean_dec_ref(v_self_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_383_, lean_object* v_self_384_, lean_object* v_h_385_){
_start:
{
lean_inc_ref(v_self_384_);
return v_self_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_386_, lean_object* v_self_387_, lean_object* v_h_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lake_Job_cast(v_00_u03b1_386_, v_self_387_, v_h_388_);
lean_dec_ref(v_self_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_390_, lean_object* v_task_391_, lean_object* v_caption_392_){
_start:
{
uint8_t v___x_393_; lean_object* v___x_394_; 
v___x_393_ = 0;
v___x_394_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_394_, 0, v_task_391_);
lean_ctor_set(v___x_394_, 1, v_inst_390_);
lean_ctor_set(v___x_394_, 2, v_caption_392_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*3, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_395_, lean_object* v_inst_396_, lean_object* v_task_397_, lean_object* v_caption_398_){
_start:
{
uint8_t v___x_399_; lean_object* v___x_400_; 
v___x_399_ = 0;
v___x_400_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_400_, 0, v_task_397_);
lean_ctor_set(v___x_400_, 1, v_inst_396_);
lean_ctor_set(v___x_400_, 2, v_caption_398_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*3, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_401_, lean_object* v_log_402_, lean_object* v_caption_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = 0;
v___x_406_ = 0;
v___x_407_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__1, &l_Lake_instInhabitedJobState_default___closed__1_once, _init_l_Lake_instInhabitedJobState_default___closed__1);
v___x_408_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_408_, 0, v_log_402_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set(v___x_408_, 2, v___x_404_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3, v___x_405_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3 + 1, v___x_406_);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_404_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_task_pure(v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_inst_401_);
lean_ctor_set(v___x_411_, 2, v_caption_403_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*3, v___x_406_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_412_, lean_object* v_inst_413_, lean_object* v_log_414_, lean_object* v_caption_415_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = 0;
v___x_418_ = 0;
v___x_419_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__1, &l_Lake_instInhabitedJobState_default___closed__1_once, _init_l_Lake_instInhabitedJobState_default___closed__1);
v___x_420_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_420_, 0, v_log_414_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
lean_ctor_set(v___x_420_, 2, v___x_416_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3, v___x_417_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3 + 1, v___x_418_);
v___x_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_416_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_task_pure(v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_inst_413_);
lean_ctor_set(v___x_423_, 2, v_caption_415_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*3, v___x_418_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_424_, lean_object* v_a_425_, lean_object* v_log_426_, lean_object* v_caption_427_){
_start:
{
uint8_t v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_428_ = 0;
v___x_429_ = 0;
v___x_430_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__1, &l_Lake_instInhabitedJobState_default___closed__1_once, _init_l_Lake_instInhabitedJobState_default___closed__1);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_432_, 0, v_log_426_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*3, v___x_428_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*3 + 1, v___x_429_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_a_425_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_task_pure(v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_kind_424_);
lean_ctor_set(v___x_435_, 2, v_caption_427_);
lean_ctor_set_uint8(v___x_435_, sizeof(void*)*3, v___x_429_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_436_, lean_object* v_kind_437_, lean_object* v_a_438_, lean_object* v_log_439_, lean_object* v_caption_440_){
_start:
{
uint8_t v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_441_ = 0;
v___x_442_ = 0;
v___x_443_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__1, &l_Lake_instInhabitedJobState_default___closed__1_once, _init_l_Lake_instInhabitedJobState_default___closed__1);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_445_, 0, v_log_439_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*3, v___x_441_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*3 + 1, v___x_442_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_a_438_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_task_pure(v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_kind_437_);
lean_ctor_set(v___x_448_, 2, v_caption_440_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*3, v___x_442_);
return v___x_448_;
}
}
static lean_object* _init_l_Lake_Job_instPure___lam__0___closed__1(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__1, &l_Lake_instInhabitedJobState_default___closed__1_once, _init_l_Lake_instInhabitedJobState_default___closed__1);
v___x_453_ = 0;
v___x_454_ = 0;
v___x_455_ = ((lean_object*)(l_Lake_Job_instPure___lam__0___closed__0));
v___x_456_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_452_);
lean_ctor_set(v___x_456_, 2, v___x_451_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*3, v___x_454_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*3 + 1, v___x_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_459_ = lean_box(0);
v___x_460_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_461_ = 0;
v___x_462_ = lean_obj_once(&l_Lake_Job_instPure___lam__0___closed__1, &l_Lake_Job_instPure___lam__0___closed__1_once, _init_l_Lake_Job_instPure___lam__0___closed__1);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_a_458_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_task_pure(v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_459_);
lean_ctor_set(v___x_465_, 2, v___x_460_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*3, v___x_461_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_468_, lean_object* v_caption_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_470_ = lean_box(0);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = ((lean_object*)(l_Lake_Job_instPure___lam__0___closed__0));
v___x_473_ = 0;
v___x_474_ = 0;
v___x_475_ = l_Lake_BuildTrace_nil(v_caption_469_);
v___x_476_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_476_, 0, v___x_472_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
lean_ctor_set(v___x_476_, 2, v___x_471_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*3, v___x_473_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*3 + 1, v___x_474_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_a_468_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_task_pure(v___x_477_);
v___x_479_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_480_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_470_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*3, v___x_474_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_481_, lean_object* v_a_482_, lean_object* v_caption_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_484_ = lean_box(0);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = ((lean_object*)(l_Lake_Job_instPure___lam__0___closed__0));
v___x_487_ = 0;
v___x_488_ = 0;
v___x_489_ = l_Lake_BuildTrace_nil(v_caption_483_);
v___x_490_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_490_, 0, v___x_486_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
lean_ctor_set(v___x_490_, 2, v___x_485_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*3, v___x_487_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*3 + 1, v___x_488_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_a_482_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_task_pure(v___x_491_);
v___x_493_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_494_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_484_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*3, v___x_488_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_495_, lean_object* v_caption_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_497_ = l_Lake_instDataKindUnit;
v___x_498_ = lean_box(0);
v___x_499_ = 0;
v___x_500_ = 0;
v___x_501_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__1, &l_Lake_instInhabitedJobState_default___closed__1_once, _init_l_Lake_instInhabitedJobState_default___closed__1);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_503_, 0, v_log_495_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*3, v___x_499_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*3 + 1, v___x_500_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_498_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_task_pure(v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_497_);
lean_ctor_set(v___x_506_, 2, v_caption_496_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*3, v___x_500_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_508_ = lean_box(0);
v___x_509_ = lean_box(0);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = ((lean_object*)(l_Lake_Job_instPure___lam__0___closed__0));
v___x_512_ = 0;
v___x_513_ = 0;
v___x_514_ = l_Lake_BuildTrace_nil(v_traceCaption_507_);
v___x_515_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_515_, 0, v___x_511_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
lean_ctor_set(v___x_515_, 2, v___x_510_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*3, v___x_512_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*3 + 1, v___x_513_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_508_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_task_pure(v___x_516_);
v___x_518_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_519_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_509_);
lean_ctor_set(v___x_519_, 2, v___x_518_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*3, v___x_513_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_520_){
_start:
{
lean_object* v_task_521_; lean_object* v___x_522_; lean_object* v_a_523_; lean_object* v_trace_524_; 
v_task_521_ = lean_ctor_get(v_job_520_, 0);
lean_inc_ref(v_task_521_);
lean_dec_ref(v_job_520_);
v___x_522_ = lean_task_get_own(v_task_521_);
v_a_523_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v_trace_524_ = lean_ctor_get(v_a_523_, 1);
lean_inc_ref(v_trace_524_);
lean_dec(v_a_523_);
return v_trace_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_525_, lean_object* v_job_526_){
_start:
{
lean_object* v_task_527_; lean_object* v___x_528_; lean_object* v_a_529_; lean_object* v_trace_530_; 
v_task_527_ = lean_ctor_get(v_job_526_, 0);
lean_inc_ref(v_task_527_);
lean_dec_ref(v_job_526_);
v___x_528_ = lean_task_get_own(v_task_527_);
v_a_529_ = lean_ctor_get(v___x_528_, 1);
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v_trace_530_ = lean_ctor_get(v_a_529_, 1);
lean_inc_ref(v_trace_530_);
lean_dec(v_a_529_);
return v_trace_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_531_, lean_object* v_job_532_){
_start:
{
lean_object* v_task_533_; lean_object* v_kind_534_; uint8_t v_optional_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_task_533_ = lean_ctor_get(v_job_532_, 0);
v_kind_534_ = lean_ctor_get(v_job_532_, 1);
v_optional_535_ = lean_ctor_get_uint8(v_job_532_, sizeof(void*)*3);
v_isSharedCheck_542_ = !lean_is_exclusive(v_job_532_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_job_532_, 2);
lean_dec(v_unused_543_);
v___x_537_ = v_job_532_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_kind_534_);
lean_inc(v_task_533_);
lean_dec(v_job_532_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 2, v_caption_531_);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_task_533_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_kind_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_caption_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_541_, sizeof(void*)*3, v_optional_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_544_, lean_object* v_caption_545_, lean_object* v_job_546_){
_start:
{
lean_object* v_task_547_; lean_object* v_kind_548_; uint8_t v_optional_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_task_547_ = lean_ctor_get(v_job_546_, 0);
v_kind_548_ = lean_ctor_get(v_job_546_, 1);
v_optional_549_ = lean_ctor_get_uint8(v_job_546_, sizeof(void*)*3);
v_isSharedCheck_556_ = !lean_is_exclusive(v_job_546_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_job_546_, 2);
lean_dec(v_unused_557_);
v___x_551_ = v_job_546_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_kind_548_);
lean_inc(v_task_547_);
lean_dec(v_job_546_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 2, v_caption_545_);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_task_547_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_kind_548_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_caption_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*3, v_optional_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_558_, lean_object* v_job_559_){
_start:
{
lean_object* v_task_560_; lean_object* v_kind_561_; lean_object* v_caption_562_; uint8_t v_optional_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_task_560_ = lean_ctor_get(v_job_559_, 0);
v_kind_561_ = lean_ctor_get(v_job_559_, 1);
v_caption_562_ = lean_ctor_get(v_job_559_, 2);
v_optional_563_ = lean_ctor_get_uint8(v_job_559_, sizeof(void*)*3);
v___x_564_ = lean_string_utf8_byte_size(v_caption_562_);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_nat_dec_eq(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_dec_ref(v_caption_558_);
return v_job_559_;
}
else
{
lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_inc(v_kind_561_);
lean_inc_ref(v_task_560_);
v_isSharedCheck_573_ = !lean_is_exclusive(v_job_559_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; lean_object* v_unused_576_; 
v_unused_574_ = lean_ctor_get(v_job_559_, 2);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_job_559_, 1);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_job_559_, 0);
lean_dec(v_unused_576_);
v___x_568_ = v_job_559_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_dec(v_job_559_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 2, v_caption_558_);
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_task_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_kind_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_caption_558_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*3, v_optional_563_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_577_, lean_object* v_caption_578_, lean_object* v_job_579_){
_start:
{
lean_object* v_task_580_; lean_object* v_kind_581_; lean_object* v_caption_582_; uint8_t v_optional_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_task_580_ = lean_ctor_get(v_job_579_, 0);
v_kind_581_ = lean_ctor_get(v_job_579_, 1);
v_caption_582_ = lean_ctor_get(v_job_579_, 2);
v_optional_583_ = lean_ctor_get_uint8(v_job_579_, sizeof(void*)*3);
v___x_584_ = lean_string_utf8_byte_size(v_caption_582_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_nat_dec_eq(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_dec_ref(v_caption_578_);
return v_job_579_;
}
else
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_inc(v_kind_581_);
lean_inc_ref(v_task_580_);
v_isSharedCheck_593_ = !lean_is_exclusive(v_job_579_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; lean_object* v_unused_595_; lean_object* v_unused_596_; 
v_unused_594_ = lean_ctor_get(v_job_579_, 2);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_job_579_, 1);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_job_579_, 0);
lean_dec(v_unused_596_);
v___x_588_ = v_job_579_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_dec(v_job_579_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 2, v_caption_578_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_task_580_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_kind_581_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_caption_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_592_, sizeof(void*)*3, v_optional_583_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_597_, lean_object* v_f_598_, lean_object* v_self_599_, lean_object* v_prio_600_, uint8_t v_sync_601_){
_start:
{
lean_object* v_task_602_; lean_object* v_caption_603_; uint8_t v_optional_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_task_602_ = lean_ctor_get(v_self_599_, 0);
v_caption_603_ = lean_ctor_get(v_self_599_, 2);
v_optional_604_ = lean_ctor_get_uint8(v_self_599_, sizeof(void*)*3);
v_isSharedCheck_612_ = !lean_is_exclusive(v_self_599_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v_self_599_, 1);
lean_dec(v_unused_613_);
v___x_606_ = v_self_599_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_caption_603_);
lean_inc(v_task_602_);
lean_dec(v_self_599_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_task_map(v_f_598_, v_task_602_, v_prio_600_, v_sync_601_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_inst_597_);
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_inst_597_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_caption_603_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*3, v_optional_604_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_614_, lean_object* v_f_615_, lean_object* v_self_616_, lean_object* v_prio_617_, lean_object* v_sync_618_){
_start:
{
uint8_t v_sync_boxed_619_; lean_object* v_res_620_; 
v_sync_boxed_619_ = lean_unbox(v_sync_618_);
v_res_620_ = l_Lake_Job_mapResult___redArg(v_inst_614_, v_f_615_, v_self_616_, v_prio_617_, v_sync_boxed_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_621_, lean_object* v_00_u03b1_622_, lean_object* v_inst_623_, lean_object* v_f_624_, lean_object* v_self_625_, lean_object* v_prio_626_, uint8_t v_sync_627_){
_start:
{
lean_object* v_task_628_; lean_object* v_caption_629_; uint8_t v_optional_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_task_628_ = lean_ctor_get(v_self_625_, 0);
v_caption_629_ = lean_ctor_get(v_self_625_, 2);
v_optional_630_ = lean_ctor_get_uint8(v_self_625_, sizeof(void*)*3);
v_isSharedCheck_638_ = !lean_is_exclusive(v_self_625_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v_self_625_, 1);
lean_dec(v_unused_639_);
v___x_632_ = v_self_625_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_caption_629_);
lean_inc(v_task_628_);
lean_dec(v_self_625_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_task_map(v_f_624_, v_task_628_, v_prio_626_, v_sync_627_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v_inst_623_);
lean_ctor_set(v___x_632_, 0, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_inst_623_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_caption_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_637_, sizeof(void*)*3, v_optional_630_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_640_, lean_object* v_00_u03b1_641_, lean_object* v_inst_642_, lean_object* v_f_643_, lean_object* v_self_644_, lean_object* v_prio_645_, lean_object* v_sync_646_){
_start:
{
uint8_t v_sync_boxed_647_; lean_object* v_res_648_; 
v_sync_boxed_647_ = lean_unbox(v_sync_646_);
v_res_648_ = l_Lake_Job_mapResult(v_00_u03b2_640_, v_00_u03b1_641_, v_inst_642_, v_f_643_, v_self_644_, v_prio_645_, v_sync_boxed_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_651_ = lean_ctor_get(v_x_650_, 0);
lean_inc(v_a_651_);
v_a_652_ = lean_ctor_get(v_x_650_, 1);
lean_inc(v_a_652_);
lean_dec_ref(v_x_650_);
v___x_653_ = lean_apply_2(v_f_649_, v_a_651_, v_a_652_);
return v___x_653_;
}
else
{
lean_object* v_a_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_f_649_);
v_a_654_ = lean_ctor_get(v_x_650_, 0);
v_a_655_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v_x_650_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_inc(v_a_654_);
lean_dec(v_x_650_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_654_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_663_, lean_object* v_f_664_, lean_object* v_self_665_, lean_object* v_prio_666_, uint8_t v_sync_667_){
_start:
{
lean_object* v_task_668_; lean_object* v_caption_669_; uint8_t v_optional_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
v_task_668_ = lean_ctor_get(v_self_665_, 0);
v_caption_669_ = lean_ctor_get(v_self_665_, 2);
v_optional_670_ = lean_ctor_get_uint8(v_self_665_, sizeof(void*)*3);
v_isSharedCheck_679_ = !lean_is_exclusive(v_self_665_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v_self_665_, 1);
lean_dec(v_unused_680_);
v___x_672_ = v_self_665_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_caption_669_);
lean_inc(v_task_668_);
lean_dec(v_self_665_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___f_674_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_674_, 0, v_f_664_);
v___x_675_ = lean_task_map(v___f_674_, v_task_668_, v_prio_666_, v_sync_667_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v_inst_663_);
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_inst_663_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_caption_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_678_, sizeof(void*)*3, v_optional_670_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* v_inst_681_, lean_object* v_f_682_, lean_object* v_self_683_, lean_object* v_prio_684_, lean_object* v_sync_685_){
_start:
{
uint8_t v_sync_boxed_686_; lean_object* v_res_687_; 
v_sync_boxed_686_ = lean_unbox(v_sync_685_);
v_res_687_ = l_Lake_Job_mapOk___redArg(v_inst_681_, v_f_682_, v_self_683_, v_prio_684_, v_sync_boxed_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_688_, lean_object* v_00_u03b1_689_, lean_object* v_inst_690_, lean_object* v_f_691_, lean_object* v_self_692_, lean_object* v_prio_693_, uint8_t v_sync_694_){
_start:
{
lean_object* v_task_695_; lean_object* v_caption_696_; uint8_t v_optional_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_706_; 
v_task_695_ = lean_ctor_get(v_self_692_, 0);
v_caption_696_ = lean_ctor_get(v_self_692_, 2);
v_optional_697_ = lean_ctor_get_uint8(v_self_692_, sizeof(void*)*3);
v_isSharedCheck_706_ = !lean_is_exclusive(v_self_692_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_self_692_, 1);
lean_dec(v_unused_707_);
v___x_699_ = v_self_692_;
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_caption_696_);
lean_inc(v_task_695_);
lean_dec(v_self_692_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___f_701_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_701_, 0, v_f_691_);
v___x_702_ = lean_task_map(v___f_701_, v_task_695_, v_prio_693_, v_sync_694_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_inst_690_);
lean_ctor_set(v___x_699_, 0, v___x_702_);
v___x_704_ = v___x_699_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_inst_690_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_caption_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_705_, sizeof(void*)*3, v_optional_697_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_708_, lean_object* v_00_u03b1_709_, lean_object* v_inst_710_, lean_object* v_f_711_, lean_object* v_self_712_, lean_object* v_prio_713_, lean_object* v_sync_714_){
_start:
{
uint8_t v_sync_boxed_715_; lean_object* v_res_716_; 
v_sync_boxed_715_ = lean_unbox(v_sync_714_);
v_res_716_ = l_Lake_Job_mapOk(v_00_u03b2_708_, v_00_u03b1_709_, v_inst_710_, v_f_711_, v_self_712_, v_prio_713_, v_sync_boxed_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
v_a_719_ = lean_ctor_get(v_x_718_, 0);
v_a_720_ = lean_ctor_get(v_x_718_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v_x_718_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_inc(v_a_719_);
lean_dec(v_x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_apply_1(v_f_717_, v_a_719_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_a_720_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_f_717_);
v_a_729_ = lean_ctor_get(v_x_718_, 0);
v_a_730_ = lean_ctor_get(v_x_718_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v_x_718_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_inc(v_a_729_);
lean_dec(v_x_718_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_729_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_738_, lean_object* v_f_739_, lean_object* v_self_740_, lean_object* v_prio_741_, uint8_t v_sync_742_){
_start:
{
lean_object* v_task_743_; lean_object* v_caption_744_; uint8_t v_optional_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_754_; 
v_task_743_ = lean_ctor_get(v_self_740_, 0);
v_caption_744_ = lean_ctor_get(v_self_740_, 2);
v_optional_745_ = lean_ctor_get_uint8(v_self_740_, sizeof(void*)*3);
v_isSharedCheck_754_ = !lean_is_exclusive(v_self_740_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_self_740_, 1);
lean_dec(v_unused_755_);
v___x_747_ = v_self_740_;
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_caption_744_);
lean_inc(v_task_743_);
lean_dec(v_self_740_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___f_749_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_749_, 0, v_f_739_);
v___x_750_ = lean_task_map(v___f_749_, v_task_743_, v_prio_741_, v_sync_742_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_inst_738_);
lean_ctor_set(v___x_747_, 0, v___x_750_);
v___x_752_ = v___x_747_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_inst_738_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_caption_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*3, v_optional_745_);
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
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_756_, lean_object* v_f_757_, lean_object* v_self_758_, lean_object* v_prio_759_, lean_object* v_sync_760_){
_start:
{
uint8_t v_sync_boxed_761_; lean_object* v_res_762_; 
v_sync_boxed_761_ = lean_unbox(v_sync_760_);
v_res_762_ = l_Lake_Job_map___redArg(v_inst_756_, v_f_757_, v_self_758_, v_prio_759_, v_sync_boxed_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_763_, lean_object* v_00_u03b1_764_, lean_object* v_inst_765_, lean_object* v_f_766_, lean_object* v_self_767_, lean_object* v_prio_768_, uint8_t v_sync_769_){
_start:
{
lean_object* v_task_770_; lean_object* v_caption_771_; uint8_t v_optional_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_781_; 
v_task_770_ = lean_ctor_get(v_self_767_, 0);
v_caption_771_ = lean_ctor_get(v_self_767_, 2);
v_optional_772_ = lean_ctor_get_uint8(v_self_767_, sizeof(void*)*3);
v_isSharedCheck_781_ = !lean_is_exclusive(v_self_767_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_self_767_, 1);
lean_dec(v_unused_782_);
v___x_774_ = v_self_767_;
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_caption_771_);
lean_inc(v_task_770_);
lean_dec(v_self_767_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___f_776_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_776_, 0, v_f_766_);
v___x_777_ = lean_task_map(v___f_776_, v_task_770_, v_prio_768_, v_sync_769_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_inst_765_);
lean_ctor_set(v___x_774_, 0, v___x_777_);
v___x_779_ = v___x_774_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_inst_765_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_caption_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_780_, sizeof(void*)*3, v_optional_772_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_783_, lean_object* v_00_u03b1_784_, lean_object* v_inst_785_, lean_object* v_f_786_, lean_object* v_self_787_, lean_object* v_prio_788_, lean_object* v_sync_789_){
_start:
{
uint8_t v_sync_boxed_790_; lean_object* v_res_791_; 
v_sync_boxed_790_ = lean_unbox(v_sync_789_);
v_res_791_ = l_Lake_Job_map(v_00_u03b2_783_, v_00_u03b1_784_, v_inst_785_, v_f_786_, v_self_787_, v_prio_788_, v_sync_boxed_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_f_794_, lean_object* v_self_795_){
_start:
{
lean_object* v_task_796_; lean_object* v_caption_797_; uint8_t v_optional_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_810_; 
v_task_796_ = lean_ctor_get(v_self_795_, 0);
v_caption_797_ = lean_ctor_get(v_self_795_, 2);
v_optional_798_ = lean_ctor_get_uint8(v_self_795_, sizeof(void*)*3);
v_isSharedCheck_810_ = !lean_is_exclusive(v_self_795_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_self_795_, 1);
lean_dec(v_unused_811_);
v___x_800_ = v_self_795_;
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_caption_797_);
lean_inc(v_task_796_);
lean_dec(v_self_795_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___f_802_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_802_, 0, v_f_794_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = 0;
v___x_806_ = lean_task_map(v___f_802_, v_task_796_, v___x_804_, v___x_805_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_803_);
lean_ctor_set(v___x_800_, 0, v___x_806_);
v___x_808_ = v___x_800_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_caption_797_);
lean_ctor_set_uint8(v_reuseFailAlloc_809_, sizeof(void*)*3, v_optional_798_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_812_, lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_817_, 0, lean_box(0));
lean_closure_set(v___x_817_, 1, lean_box(0));
lean_closure_set(v___x_817_, 2, v___y_815_);
v___x_818_ = lean_apply_4(v___f_812_, lean_box(0), lean_box(0), v___x_817_, v___y_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_826_){
_start:
{
lean_inc_ref(v_self_826_);
return v_self_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_827_);
lean_dec_ref(v_self_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_829_, lean_object* v_self_830_){
_start:
{
lean_inc_ref(v_self_830_);
return v_self_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_831_, lean_object* v_self_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_831_, v_self_832_);
lean_dec_ref(v_self_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0));
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_837_){
_start:
{
lean_object* v_task_838_; lean_object* v_caption_839_; uint8_t v_optional_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_task_838_ = lean_ctor_get(v_job_837_, 0);
v_caption_839_ = lean_ctor_get(v_job_837_, 2);
v_optional_840_ = lean_ctor_get_uint8(v_job_837_, sizeof(void*)*3);
v_isSharedCheck_848_ = !lean_is_exclusive(v_job_837_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_job_837_, 1);
lean_dec(v_unused_849_);
v___x_842_ = v_job_837_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_caption_839_);
lean_inc(v_task_838_);
lean_dec(v_job_837_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_box(0);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_task_838_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_caption_839_);
lean_ctor_set_uint8(v_reuseFailAlloc_847_, sizeof(void*)*3, v_optional_840_);
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
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_850_, lean_object* v_job_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lake_Job_toOpaque___redArg(v_job_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* v_00_u03b1_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___closed__0));
return v___x_855_;
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
