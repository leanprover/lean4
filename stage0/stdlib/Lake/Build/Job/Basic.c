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
lean_inc(v___y_102_);
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
lean_inc(v___y_109_);
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
lean_inc(v___y_116_);
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
lean_inc(v___y_123_);
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
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__1));
v___x_253_ = l_Lake_BuildTrace_nil(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__3(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_256_ = 0;
v___x_257_ = 0;
v___x_258_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_259_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_255_);
lean_ctor_set(v___x_259_, 2, v___x_254_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*3, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*3 + 1, v___x_256_);
return v___x_259_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
return v___x_260_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lake_instInhabitedJobState_default;
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object* v_a_262_, lean_object* v_b_263_){
_start:
{
lean_object* v_log_264_; uint8_t v_action_265_; uint8_t v_wantsRebuild_266_; lean_object* v_trace_267_; lean_object* v_buildTime_268_; lean_object* v_log_269_; uint8_t v_action_270_; uint8_t v_wantsRebuild_271_; lean_object* v_trace_272_; lean_object* v_buildTime_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_286_; 
v_log_264_ = lean_ctor_get(v_a_262_, 0);
lean_inc_ref(v_log_264_);
v_action_265_ = lean_ctor_get_uint8(v_a_262_, sizeof(void*)*3);
v_wantsRebuild_266_ = lean_ctor_get_uint8(v_a_262_, sizeof(void*)*3 + 1);
v_trace_267_ = lean_ctor_get(v_a_262_, 1);
lean_inc_ref(v_trace_267_);
v_buildTime_268_ = lean_ctor_get(v_a_262_, 2);
lean_inc(v_buildTime_268_);
lean_dec_ref(v_a_262_);
v_log_269_ = lean_ctor_get(v_b_263_, 0);
v_action_270_ = lean_ctor_get_uint8(v_b_263_, sizeof(void*)*3);
v_wantsRebuild_271_ = lean_ctor_get_uint8(v_b_263_, sizeof(void*)*3 + 1);
v_trace_272_ = lean_ctor_get(v_b_263_, 1);
v_buildTime_273_ = lean_ctor_get(v_b_263_, 2);
v_isSharedCheck_286_ = !lean_is_exclusive(v_b_263_);
if (v_isSharedCheck_286_ == 0)
{
v___x_275_ = v_b_263_;
v_isShared_276_ = v_isSharedCheck_286_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_buildTime_273_);
lean_inc(v_trace_272_);
lean_inc(v_log_269_);
lean_dec(v_b_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_286_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; uint8_t v___x_278_; uint8_t v___y_280_; 
v___x_277_ = l_Array_append___redArg(v_log_264_, v_log_269_);
lean_dec_ref(v_log_269_);
v___x_278_ = l_Lake_JobAction_merge(v_action_265_, v_action_270_);
if (v_wantsRebuild_266_ == 0)
{
v___y_280_ = v_wantsRebuild_271_;
goto v___jp_279_;
}
else
{
v___y_280_ = v_wantsRebuild_266_;
goto v___jp_279_;
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_281_ = l_Lake_BuildTrace_mix(v_trace_267_, v_trace_272_);
v___x_282_ = lean_nat_add(v_buildTime_268_, v_buildTime_273_);
lean_dec(v_buildTime_273_);
lean_dec(v_buildTime_268_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 2, v___x_282_);
lean_ctor_set(v___x_275_, 1, v___x_281_);
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_284_ = v___x_275_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*3, v___x_278_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*3 + 1, v___y_280_);
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object* v_f_287_, lean_object* v_s_288_){
_start:
{
lean_object* v_log_289_; uint8_t v_action_290_; uint8_t v_wantsRebuild_291_; lean_object* v_trace_292_; lean_object* v_buildTime_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_log_289_ = lean_ctor_get(v_s_288_, 0);
v_action_290_ = lean_ctor_get_uint8(v_s_288_, sizeof(void*)*3);
v_wantsRebuild_291_ = lean_ctor_get_uint8(v_s_288_, sizeof(void*)*3 + 1);
v_trace_292_ = lean_ctor_get(v_s_288_, 1);
v_buildTime_293_ = lean_ctor_get(v_s_288_, 2);
v_isSharedCheck_301_ = !lean_is_exclusive(v_s_288_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v_s_288_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_buildTime_293_);
lean_inc(v_trace_292_);
lean_inc(v_log_289_);
lean_dec(v_s_288_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_apply_1(v_f_287_, v_log_289_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_trace_292_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_buildTime_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_300_, sizeof(void*)*3, v_action_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_300_, sizeof(void*)*3 + 1, v_wantsRebuild_291_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object* v_e_302_, lean_object* v_s_303_){
_start:
{
lean_object* v_log_304_; uint8_t v_action_305_; uint8_t v_wantsRebuild_306_; lean_object* v_trace_307_; lean_object* v_buildTime_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_log_304_ = lean_ctor_get(v_s_303_, 0);
v_action_305_ = lean_ctor_get_uint8(v_s_303_, sizeof(void*)*3);
v_wantsRebuild_306_ = lean_ctor_get_uint8(v_s_303_, sizeof(void*)*3 + 1);
v_trace_307_ = lean_ctor_get(v_s_303_, 1);
v_buildTime_308_ = lean_ctor_get(v_s_303_, 2);
v_isSharedCheck_316_ = !lean_is_exclusive(v_s_303_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v_s_303_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_buildTime_308_);
lean_inc(v_trace_307_);
lean_inc(v_log_304_);
lean_dec(v_s_303_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_array_push(v_log_304_, v_e_302_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_trace_307_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_buildTime_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*3, v_action_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*3 + 1, v_wantsRebuild_306_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object* v_log_317_, lean_object* v_self_318_){
_start:
{
if (lean_obj_tag(v_self_318_) == 0)
{
lean_object* v_a_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_340_; 
v_a_319_ = lean_ctor_get(v_self_318_, 1);
v_a_320_ = lean_ctor_get(v_self_318_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_self_318_);
if (v_isSharedCheck_340_ == 0)
{
v___x_322_ = v_self_318_;
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_319_);
lean_inc(v_a_320_);
lean_dec(v_self_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_log_324_; uint8_t v_action_325_; uint8_t v_wantsRebuild_326_; lean_object* v_trace_327_; lean_object* v_buildTime_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_339_; 
v_log_324_ = lean_ctor_get(v_a_319_, 0);
v_action_325_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*3);
v_wantsRebuild_326_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*3 + 1);
v_trace_327_ = lean_ctor_get(v_a_319_, 1);
v_buildTime_328_ = lean_ctor_get(v_a_319_, 2);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_319_);
if (v_isSharedCheck_339_ == 0)
{
v___x_330_ = v_a_319_;
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_buildTime_328_);
lean_inc(v_trace_327_);
lean_inc(v_log_324_);
lean_dec(v_a_319_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = l_Array_append___redArg(v_log_317_, v_log_324_);
lean_dec_ref(v_log_324_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_trace_327_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_buildTime_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*3, v_action_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*3 + 1, v_wantsRebuild_326_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_334_);
v___x_336_ = v___x_322_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_320_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_364_; 
v_a_341_ = lean_ctor_get(v_self_318_, 1);
v_a_342_ = lean_ctor_get(v_self_318_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_self_318_);
if (v_isSharedCheck_364_ == 0)
{
v___x_344_ = v_self_318_;
v_isShared_345_ = v_isSharedCheck_364_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_341_);
lean_inc(v_a_342_);
lean_dec(v_self_318_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_364_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_log_346_; uint8_t v_action_347_; uint8_t v_wantsRebuild_348_; lean_object* v_trace_349_; lean_object* v_buildTime_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_363_; 
v_log_346_ = lean_ctor_get(v_a_341_, 0);
v_action_347_ = lean_ctor_get_uint8(v_a_341_, sizeof(void*)*3);
v_wantsRebuild_348_ = lean_ctor_get_uint8(v_a_341_, sizeof(void*)*3 + 1);
v_trace_349_ = lean_ctor_get(v_a_341_, 1);
v_buildTime_350_ = lean_ctor_get(v_a_341_, 2);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_341_);
if (v_isSharedCheck_363_ == 0)
{
v___x_352_ = v_a_341_;
v_isShared_353_ = v_isSharedCheck_363_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_buildTime_350_);
lean_inc(v_trace_349_);
lean_inc(v_log_346_);
lean_dec(v_a_341_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_363_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_354_ = lean_array_get_size(v_log_317_);
v___x_355_ = lean_nat_add(v___x_354_, v_a_342_);
lean_dec(v_a_342_);
v___x_356_ = l_Array_append___redArg(v_log_317_, v_log_346_);
lean_dec_ref(v_log_346_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_356_);
v___x_358_ = v___x_352_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_trace_349_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_buildTime_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, sizeof(void*)*3, v_action_347_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, sizeof(void*)*3 + 1, v_wantsRebuild_348_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v___x_358_);
lean_ctor_set(v___x_344_, 0, v___x_355_);
v___x_360_ = v___x_344_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object* v_00_u03b1_365_, lean_object* v_log_366_, lean_object* v_self_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lake_JobResult_prependLog___redArg(v_log_366_, v_self_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = l_Lake_instInhabitedJobState_default;
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
v___x_373_ = lean_task_pure(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__3(void){
_start:
{
uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_375_ = 0;
v___x_376_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_377_ = lean_box(0);
v___x_378_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__1, &l_Lake_instInhabitedJob___closed__1_once, _init_l_Lake_instInhabitedJob___closed__1);
v___x_379_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_376_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3, v___x_375_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__3, &l_Lake_instInhabitedJob___closed__3_once, _init_l_Lake_instInhabitedJob___closed__3);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_382_){
_start:
{
lean_inc_ref(v_self_382_);
return v_self_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lake_Job_cast___redArg(v_self_383_);
lean_dec_ref(v_self_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_385_, lean_object* v_self_386_, lean_object* v_h_387_){
_start:
{
lean_inc_ref(v_self_386_);
return v_self_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_388_, lean_object* v_self_389_, lean_object* v_h_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lake_Job_cast(v_00_u03b1_388_, v_self_389_, v_h_390_);
lean_dec_ref(v_self_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_392_, lean_object* v_task_393_, lean_object* v_caption_394_){
_start:
{
uint8_t v___x_395_; lean_object* v___x_396_; 
v___x_395_ = 0;
v___x_396_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_396_, 0, v_task_393_);
lean_ctor_set(v___x_396_, 1, v_inst_392_);
lean_ctor_set(v___x_396_, 2, v_caption_394_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_397_, lean_object* v_inst_398_, lean_object* v_task_399_, lean_object* v_caption_400_){
_start:
{
uint8_t v___x_401_; lean_object* v___x_402_; 
v___x_401_ = 0;
v___x_402_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_402_, 0, v_task_399_);
lean_ctor_set(v___x_402_, 1, v_inst_398_);
lean_ctor_set(v___x_402_, 2, v_caption_400_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*3, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_403_, lean_object* v_log_404_, lean_object* v_caption_405_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = 0;
v___x_408_ = 0;
v___x_409_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_410_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_410_, 0, v_log_404_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
lean_ctor_set(v___x_410_, 2, v___x_406_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3, v___x_407_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3 + 1, v___x_408_);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_406_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_task_pure(v___x_411_);
v___x_413_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_inst_403_);
lean_ctor_set(v___x_413_, 2, v_caption_405_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*3, v___x_408_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_414_, lean_object* v_inst_415_, lean_object* v_log_416_, lean_object* v_caption_417_){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = 0;
v___x_420_ = 0;
v___x_421_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_422_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_422_, 0, v_log_416_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_ctor_set(v___x_422_, 2, v___x_418_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*3, v___x_419_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*3 + 1, v___x_420_);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_418_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_task_pure(v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_inst_415_);
lean_ctor_set(v___x_425_, 2, v_caption_417_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3, v___x_420_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_426_, lean_object* v_a_427_, lean_object* v_log_428_, lean_object* v_caption_429_){
_start:
{
uint8_t v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_430_ = 0;
v___x_431_ = 0;
v___x_432_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_434_, 0, v_log_428_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*3, v___x_430_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*3 + 1, v___x_431_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_a_427_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_task_pure(v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_kind_426_);
lean_ctor_set(v___x_437_, 2, v_caption_429_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*3, v___x_431_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_438_, lean_object* v_kind_439_, lean_object* v_a_440_, lean_object* v_log_441_, lean_object* v_caption_442_){
_start:
{
uint8_t v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_443_ = 0;
v___x_444_ = 0;
v___x_445_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_447_, 0, v_log_441_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3, v___x_443_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3 + 1, v___x_444_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_a_440_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_task_pure(v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_kind_439_);
lean_ctor_set(v___x_450_, 2, v_caption_442_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*3, v___x_444_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_455_ = 0;
v___x_456_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_a_452_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_task_pure(v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_453_);
lean_ctor_set(v___x_459_, 2, v___x_454_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*3, v___x_455_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_462_, lean_object* v_caption_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_464_ = lean_box(0);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_467_ = 0;
v___x_468_ = 0;
v___x_469_ = l_Lake_BuildTrace_nil(v_caption_463_);
v___x_470_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_470_, 0, v___x_466_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
lean_ctor_set(v___x_470_, 2, v___x_465_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*3, v___x_467_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*3 + 1, v___x_468_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_a_462_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_task_pure(v___x_471_);
v___x_473_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_474_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_464_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*3, v___x_468_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_475_, lean_object* v_a_476_, lean_object* v_caption_477_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_478_ = lean_box(0);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_481_ = 0;
v___x_482_ = 0;
v___x_483_ = l_Lake_BuildTrace_nil(v_caption_477_);
v___x_484_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_484_, 0, v___x_480_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
lean_ctor_set(v___x_484_, 2, v___x_479_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*3, v___x_481_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*3 + 1, v___x_482_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_a_476_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_task_pure(v___x_485_);
v___x_487_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_488_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_478_);
lean_ctor_set(v___x_488_, 2, v___x_487_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*3, v___x_482_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_489_, lean_object* v_caption_490_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_491_ = l_Lake_instDataKindUnit;
v___x_492_ = lean_box(0);
v___x_493_ = 0;
v___x_494_ = 0;
v___x_495_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_497_, 0, v_log_489_);
lean_ctor_set(v___x_497_, 1, v___x_495_);
lean_ctor_set(v___x_497_, 2, v___x_496_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*3, v___x_493_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*3 + 1, v___x_494_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_492_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_task_pure(v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___x_491_);
lean_ctor_set(v___x_500_, 2, v_caption_490_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*3, v___x_494_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_502_ = lean_box(0);
v___x_503_ = lean_box(0);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_506_ = 0;
v___x_507_ = 0;
v___x_508_ = l_Lake_BuildTrace_nil(v_traceCaption_501_);
v___x_509_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_509_, 0, v___x_505_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
lean_ctor_set(v___x_509_, 2, v___x_504_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*3, v___x_506_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*3 + 1, v___x_507_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_502_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_task_pure(v___x_510_);
v___x_512_ = ((lean_object*)(l_Lake_instInhabitedJob___closed__2));
v___x_513_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_503_);
lean_ctor_set(v___x_513_, 2, v___x_512_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*3, v___x_507_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_514_){
_start:
{
lean_object* v_task_515_; lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v_trace_518_; 
v_task_515_ = lean_ctor_get(v_job_514_, 0);
lean_inc_ref(v_task_515_);
lean_dec_ref(v_job_514_);
v___x_516_ = lean_task_get_own(v_task_515_);
v_a_517_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v_trace_518_ = lean_ctor_get(v_a_517_, 1);
lean_inc_ref(v_trace_518_);
lean_dec(v_a_517_);
return v_trace_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_519_, lean_object* v_job_520_){
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
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_525_, lean_object* v_job_526_){
_start:
{
lean_object* v_task_527_; lean_object* v_kind_528_; uint8_t v_optional_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_task_527_ = lean_ctor_get(v_job_526_, 0);
v_kind_528_ = lean_ctor_get(v_job_526_, 1);
v_optional_529_ = lean_ctor_get_uint8(v_job_526_, sizeof(void*)*3);
v_isSharedCheck_536_ = !lean_is_exclusive(v_job_526_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_job_526_, 2);
lean_dec(v_unused_537_);
v___x_531_ = v_job_526_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_kind_528_);
lean_inc(v_task_527_);
lean_dec(v_job_526_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v_caption_525_);
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_task_527_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_kind_528_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_caption_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_535_, sizeof(void*)*3, v_optional_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_538_, lean_object* v_caption_539_, lean_object* v_job_540_){
_start:
{
lean_object* v_task_541_; lean_object* v_kind_542_; uint8_t v_optional_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_task_541_ = lean_ctor_get(v_job_540_, 0);
v_kind_542_ = lean_ctor_get(v_job_540_, 1);
v_optional_543_ = lean_ctor_get_uint8(v_job_540_, sizeof(void*)*3);
v_isSharedCheck_550_ = !lean_is_exclusive(v_job_540_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_job_540_, 2);
lean_dec(v_unused_551_);
v___x_545_ = v_job_540_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_kind_542_);
lean_inc(v_task_541_);
lean_dec(v_job_540_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 2, v_caption_539_);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_task_541_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_kind_542_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_caption_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*3, v_optional_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_552_, lean_object* v_job_553_){
_start:
{
lean_object* v_task_554_; lean_object* v_kind_555_; lean_object* v_caption_556_; uint8_t v_optional_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_task_554_ = lean_ctor_get(v_job_553_, 0);
v_kind_555_ = lean_ctor_get(v_job_553_, 1);
v_caption_556_ = lean_ctor_get(v_job_553_, 2);
v_optional_557_ = lean_ctor_get_uint8(v_job_553_, sizeof(void*)*3);
v___x_558_ = lean_string_utf8_byte_size(v_caption_556_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_nat_dec_eq(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec_ref(v_caption_552_);
return v_job_553_;
}
else
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_inc(v_kind_555_);
lean_inc_ref(v_task_554_);
v_isSharedCheck_567_ = !lean_is_exclusive(v_job_553_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_568_ = lean_ctor_get(v_job_553_, 2);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_job_553_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_job_553_, 0);
lean_dec(v_unused_570_);
v___x_562_ = v_job_553_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_dec(v_job_553_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 2, v_caption_552_);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_task_554_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_kind_555_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_caption_552_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3, v_optional_557_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_571_, lean_object* v_caption_572_, lean_object* v_job_573_){
_start:
{
lean_object* v_task_574_; lean_object* v_kind_575_; lean_object* v_caption_576_; uint8_t v_optional_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_task_574_ = lean_ctor_get(v_job_573_, 0);
v_kind_575_ = lean_ctor_get(v_job_573_, 1);
v_caption_576_ = lean_ctor_get(v_job_573_, 2);
v_optional_577_ = lean_ctor_get_uint8(v_job_573_, sizeof(void*)*3);
v___x_578_ = lean_string_utf8_byte_size(v_caption_576_);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_nat_dec_eq(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec_ref(v_caption_572_);
return v_job_573_;
}
else
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_inc(v_kind_575_);
lean_inc_ref(v_task_574_);
v_isSharedCheck_587_ = !lean_is_exclusive(v_job_573_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; 
v_unused_588_ = lean_ctor_get(v_job_573_, 2);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_job_573_, 1);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_job_573_, 0);
lean_dec(v_unused_590_);
v___x_582_ = v_job_573_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_job_573_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 2, v_caption_572_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_task_574_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_kind_575_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_caption_572_);
lean_ctor_set_uint8(v_reuseFailAlloc_586_, sizeof(void*)*3, v_optional_577_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_591_, lean_object* v_f_592_, lean_object* v_self_593_, lean_object* v_prio_594_, uint8_t v_sync_595_){
_start:
{
lean_object* v_task_596_; lean_object* v_caption_597_; uint8_t v_optional_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_606_; 
v_task_596_ = lean_ctor_get(v_self_593_, 0);
v_caption_597_ = lean_ctor_get(v_self_593_, 2);
v_optional_598_ = lean_ctor_get_uint8(v_self_593_, sizeof(void*)*3);
v_isSharedCheck_606_ = !lean_is_exclusive(v_self_593_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_self_593_, 1);
lean_dec(v_unused_607_);
v___x_600_ = v_self_593_;
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_caption_597_);
lean_inc(v_task_596_);
lean_dec(v_self_593_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_task_map(v_f_592_, v_task_596_, v_prio_594_, v_sync_595_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v_inst_591_);
lean_ctor_set(v___x_600_, 0, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_inst_591_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_caption_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*3, v_optional_598_);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_608_, lean_object* v_f_609_, lean_object* v_self_610_, lean_object* v_prio_611_, lean_object* v_sync_612_){
_start:
{
uint8_t v_sync_boxed_613_; lean_object* v_res_614_; 
v_sync_boxed_613_ = lean_unbox(v_sync_612_);
v_res_614_ = l_Lake_Job_mapResult___redArg(v_inst_608_, v_f_609_, v_self_610_, v_prio_611_, v_sync_boxed_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_615_, lean_object* v_00_u03b1_616_, lean_object* v_inst_617_, lean_object* v_f_618_, lean_object* v_self_619_, lean_object* v_prio_620_, uint8_t v_sync_621_){
_start:
{
lean_object* v_task_622_; lean_object* v_caption_623_; uint8_t v_optional_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_task_622_ = lean_ctor_get(v_self_619_, 0);
v_caption_623_ = lean_ctor_get(v_self_619_, 2);
v_optional_624_ = lean_ctor_get_uint8(v_self_619_, sizeof(void*)*3);
v_isSharedCheck_632_ = !lean_is_exclusive(v_self_619_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_self_619_, 1);
lean_dec(v_unused_633_);
v___x_626_ = v_self_619_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_caption_623_);
lean_inc(v_task_622_);
lean_dec(v_self_619_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_task_map(v_f_618_, v_task_622_, v_prio_620_, v_sync_621_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v_inst_617_);
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_inst_617_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_caption_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*3, v_optional_624_);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_634_, lean_object* v_00_u03b1_635_, lean_object* v_inst_636_, lean_object* v_f_637_, lean_object* v_self_638_, lean_object* v_prio_639_, lean_object* v_sync_640_){
_start:
{
uint8_t v_sync_boxed_641_; lean_object* v_res_642_; 
v_sync_boxed_641_ = lean_unbox(v_sync_640_);
v_res_642_ = l_Lake_Job_mapResult(v_00_u03b2_634_, v_00_u03b1_635_, v_inst_636_, v_f_637_, v_self_638_, v_prio_639_, v_sync_boxed_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_643_, lean_object* v_x_644_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_645_ = lean_ctor_get(v_x_644_, 0);
lean_inc(v_a_645_);
v_a_646_ = lean_ctor_get(v_x_644_, 1);
lean_inc(v_a_646_);
lean_dec_ref(v_x_644_);
v___x_647_ = lean_apply_2(v_f_643_, v_a_645_, v_a_646_);
return v___x_647_;
}
else
{
lean_object* v_a_648_; lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_f_643_);
v_a_648_ = lean_ctor_get(v_x_644_, 0);
v_a_649_ = lean_ctor_get(v_x_644_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v_x_644_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_inc(v_a_648_);
lean_dec(v_x_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_648_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_657_, lean_object* v_f_658_, lean_object* v_self_659_, lean_object* v_prio_660_, uint8_t v_sync_661_){
_start:
{
lean_object* v_task_662_; lean_object* v_caption_663_; uint8_t v_optional_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_673_; 
v_task_662_ = lean_ctor_get(v_self_659_, 0);
v_caption_663_ = lean_ctor_get(v_self_659_, 2);
v_optional_664_ = lean_ctor_get_uint8(v_self_659_, sizeof(void*)*3);
v_isSharedCheck_673_ = !lean_is_exclusive(v_self_659_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v_self_659_, 1);
lean_dec(v_unused_674_);
v___x_666_ = v_self_659_;
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_caption_663_);
lean_inc(v_task_662_);
lean_dec(v_self_659_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___f_668_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_668_, 0, v_f_658_);
v___x_669_ = lean_task_map(v___f_668_, v_task_662_, v_prio_660_, v_sync_661_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_inst_657_);
lean_ctor_set(v___x_666_, 0, v___x_669_);
v___x_671_ = v___x_666_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_inst_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_caption_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_672_, sizeof(void*)*3, v_optional_664_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* v_inst_675_, lean_object* v_f_676_, lean_object* v_self_677_, lean_object* v_prio_678_, lean_object* v_sync_679_){
_start:
{
uint8_t v_sync_boxed_680_; lean_object* v_res_681_; 
v_sync_boxed_680_ = lean_unbox(v_sync_679_);
v_res_681_ = l_Lake_Job_mapOk___redArg(v_inst_675_, v_f_676_, v_self_677_, v_prio_678_, v_sync_boxed_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_682_, lean_object* v_00_u03b1_683_, lean_object* v_inst_684_, lean_object* v_f_685_, lean_object* v_self_686_, lean_object* v_prio_687_, uint8_t v_sync_688_){
_start:
{
lean_object* v_task_689_; lean_object* v_caption_690_; uint8_t v_optional_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_700_; 
v_task_689_ = lean_ctor_get(v_self_686_, 0);
v_caption_690_ = lean_ctor_get(v_self_686_, 2);
v_optional_691_ = lean_ctor_get_uint8(v_self_686_, sizeof(void*)*3);
v_isSharedCheck_700_ = !lean_is_exclusive(v_self_686_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_self_686_, 1);
lean_dec(v_unused_701_);
v___x_693_ = v_self_686_;
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_caption_690_);
lean_inc(v_task_689_);
lean_dec(v_self_686_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___f_695_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_695_, 0, v_f_685_);
v___x_696_ = lean_task_map(v___f_695_, v_task_689_, v_prio_687_, v_sync_688_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_inst_684_);
lean_ctor_set(v___x_693_, 0, v___x_696_);
v___x_698_ = v___x_693_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_inst_684_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_caption_690_);
lean_ctor_set_uint8(v_reuseFailAlloc_699_, sizeof(void*)*3, v_optional_691_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_702_, lean_object* v_00_u03b1_703_, lean_object* v_inst_704_, lean_object* v_f_705_, lean_object* v_self_706_, lean_object* v_prio_707_, lean_object* v_sync_708_){
_start:
{
uint8_t v_sync_boxed_709_; lean_object* v_res_710_; 
v_sync_boxed_709_ = lean_unbox(v_sync_708_);
v_res_710_ = l_Lake_Job_mapOk(v_00_u03b2_702_, v_00_u03b1_703_, v_inst_704_, v_f_705_, v_self_706_, v_prio_707_, v_sync_boxed_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_a_713_ = lean_ctor_get(v_x_712_, 0);
v_a_714_ = lean_ctor_get(v_x_712_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v_x_712_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_inc(v_a_713_);
lean_dec(v_x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_apply_1(v_f_711_, v_a_713_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_a_714_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_f_711_);
v_a_723_ = lean_ctor_get(v_x_712_, 0);
v_a_724_ = lean_ctor_get(v_x_712_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v_x_712_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_inc(v_a_723_);
lean_dec(v_x_712_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_723_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_732_, lean_object* v_f_733_, lean_object* v_self_734_, lean_object* v_prio_735_, uint8_t v_sync_736_){
_start:
{
lean_object* v_task_737_; lean_object* v_caption_738_; uint8_t v_optional_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_748_; 
v_task_737_ = lean_ctor_get(v_self_734_, 0);
v_caption_738_ = lean_ctor_get(v_self_734_, 2);
v_optional_739_ = lean_ctor_get_uint8(v_self_734_, sizeof(void*)*3);
v_isSharedCheck_748_ = !lean_is_exclusive(v_self_734_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v_self_734_, 1);
lean_dec(v_unused_749_);
v___x_741_ = v_self_734_;
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_caption_738_);
lean_inc(v_task_737_);
lean_dec(v_self_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___f_743_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_743_, 0, v_f_733_);
v___x_744_ = lean_task_map(v___f_743_, v_task_737_, v_prio_735_, v_sync_736_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v_inst_732_);
lean_ctor_set(v___x_741_, 0, v___x_744_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_inst_732_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_caption_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_747_, sizeof(void*)*3, v_optional_739_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_750_, lean_object* v_f_751_, lean_object* v_self_752_, lean_object* v_prio_753_, lean_object* v_sync_754_){
_start:
{
uint8_t v_sync_boxed_755_; lean_object* v_res_756_; 
v_sync_boxed_755_ = lean_unbox(v_sync_754_);
v_res_756_ = l_Lake_Job_map___redArg(v_inst_750_, v_f_751_, v_self_752_, v_prio_753_, v_sync_boxed_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_757_, lean_object* v_00_u03b1_758_, lean_object* v_inst_759_, lean_object* v_f_760_, lean_object* v_self_761_, lean_object* v_prio_762_, uint8_t v_sync_763_){
_start:
{
lean_object* v_task_764_; lean_object* v_caption_765_; uint8_t v_optional_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v_task_764_ = lean_ctor_get(v_self_761_, 0);
v_caption_765_ = lean_ctor_get(v_self_761_, 2);
v_optional_766_ = lean_ctor_get_uint8(v_self_761_, sizeof(void*)*3);
v_isSharedCheck_775_ = !lean_is_exclusive(v_self_761_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v_self_761_, 1);
lean_dec(v_unused_776_);
v___x_768_ = v_self_761_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_caption_765_);
lean_inc(v_task_764_);
lean_dec(v_self_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___f_770_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_770_, 0, v_f_760_);
v___x_771_ = lean_task_map(v___f_770_, v_task_764_, v_prio_762_, v_sync_763_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v_inst_759_);
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_inst_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_caption_765_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*3, v_optional_766_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_777_, lean_object* v_00_u03b1_778_, lean_object* v_inst_779_, lean_object* v_f_780_, lean_object* v_self_781_, lean_object* v_prio_782_, lean_object* v_sync_783_){
_start:
{
uint8_t v_sync_boxed_784_; lean_object* v_res_785_; 
v_sync_boxed_784_ = lean_unbox(v_sync_783_);
v_res_785_ = l_Lake_Job_map(v_00_u03b2_777_, v_00_u03b1_778_, v_inst_779_, v_f_780_, v_self_781_, v_prio_782_, v_sync_boxed_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_f_788_, lean_object* v_self_789_){
_start:
{
lean_object* v_task_790_; lean_object* v_caption_791_; uint8_t v_optional_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_804_; 
v_task_790_ = lean_ctor_get(v_self_789_, 0);
v_caption_791_ = lean_ctor_get(v_self_789_, 2);
v_optional_792_ = lean_ctor_get_uint8(v_self_789_, sizeof(void*)*3);
v_isSharedCheck_804_ = !lean_is_exclusive(v_self_789_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v_self_789_, 1);
lean_dec(v_unused_805_);
v___x_794_ = v_self_789_;
v_isShared_795_ = v_isSharedCheck_804_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_caption_791_);
lean_inc(v_task_790_);
lean_dec(v_self_789_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_804_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___f_796_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_796_, 0, v_f_788_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = 0;
v___x_800_ = lean_task_map(v___f_796_, v_task_790_, v___x_798_, v___x_799_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_797_);
lean_ctor_set(v___x_794_, 0, v___x_800_);
v___x_802_ = v___x_794_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_caption_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_803_, sizeof(void*)*3, v_optional_792_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_806_, lean_object* v_00_u03b1_807_, lean_object* v_00_u03b2_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_811_, 0, lean_box(0));
lean_closure_set(v___x_811_, 1, lean_box(0));
lean_closure_set(v___x_811_, 2, v___y_809_);
v___x_812_ = lean_apply_4(v___f_806_, lean_box(0), lean_box(0), v___x_811_, v___y_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_820_){
_start:
{
lean_inc_ref(v_self_820_);
return v_self_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_821_);
lean_dec_ref(v_self_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_823_, lean_object* v_self_824_){
_start:
{
lean_inc_ref(v_self_824_);
return v_self_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_825_, lean_object* v_self_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_825_, v_self_826_);
lean_dec_ref(v_self_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0));
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_831_){
_start:
{
lean_object* v_task_832_; lean_object* v_caption_833_; uint8_t v_optional_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_task_832_ = lean_ctor_get(v_job_831_, 0);
v_caption_833_ = lean_ctor_get(v_job_831_, 2);
v_optional_834_ = lean_ctor_get_uint8(v_job_831_, sizeof(void*)*3);
v_isSharedCheck_842_ = !lean_is_exclusive(v_job_831_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_job_831_, 1);
lean_dec(v_unused_843_);
v___x_836_ = v_job_831_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_caption_833_);
lean_inc(v_task_832_);
lean_dec(v_job_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_box(0);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_task_832_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_caption_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_841_, sizeof(void*)*3, v_optional_834_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_844_, lean_object* v_job_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lake_Job_toOpaque___redArg(v_job_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* v_00_u03b1_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___closed__0));
return v___x_849_;
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
