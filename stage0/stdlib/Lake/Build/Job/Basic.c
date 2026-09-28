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
v___x_324_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_320_);
lean_ctor_set(v___x_324_, 2, v___x_319_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*3, v___x_322_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*3 + 1, v___x_321_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*3 + 2, v___x_321_);
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
lean_object* v_log_329_; uint8_t v_action_330_; uint8_t v_wantsRebuild_331_; uint8_t v_canceled_332_; lean_object* v_trace_333_; lean_object* v_buildTime_334_; lean_object* v_log_335_; uint8_t v_action_336_; uint8_t v_wantsRebuild_337_; uint8_t v_canceled_338_; lean_object* v_trace_339_; lean_object* v_buildTime_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_356_; 
v_log_329_ = lean_ctor_get(v_a_327_, 0);
lean_inc_ref(v_log_329_);
v_action_330_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*3);
v_wantsRebuild_331_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*3 + 1);
v_canceled_332_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*3 + 2);
v_trace_333_ = lean_ctor_get(v_a_327_, 1);
lean_inc_ref(v_trace_333_);
v_buildTime_334_ = lean_ctor_get(v_a_327_, 2);
lean_inc(v_buildTime_334_);
lean_dec_ref(v_a_327_);
v_log_335_ = lean_ctor_get(v_b_328_, 0);
v_action_336_ = lean_ctor_get_uint8(v_b_328_, sizeof(void*)*3);
v_wantsRebuild_337_ = lean_ctor_get_uint8(v_b_328_, sizeof(void*)*3 + 1);
v_canceled_338_ = lean_ctor_get_uint8(v_b_328_, sizeof(void*)*3 + 2);
v_trace_339_ = lean_ctor_get(v_b_328_, 1);
v_buildTime_340_ = lean_ctor_get(v_b_328_, 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_b_328_);
if (v_isSharedCheck_356_ == 0)
{
v___x_342_ = v_b_328_;
v_isShared_343_ = v_isSharedCheck_356_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_buildTime_340_);
lean_inc(v_trace_339_);
lean_inc(v_log_335_);
lean_dec(v_b_328_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_356_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; uint8_t v___x_345_; uint8_t v___y_347_; uint8_t v___y_348_; uint8_t v___y_355_; 
v___x_344_ = l_Array_append___redArg(v_log_329_, v_log_335_);
lean_dec_ref(v_log_335_);
v___x_345_ = l_Lake_JobAction_merge(v_action_330_, v_action_336_);
if (v_wantsRebuild_331_ == 0)
{
v___y_355_ = v_wantsRebuild_337_;
goto v___jp_354_;
}
else
{
v___y_355_ = v_wantsRebuild_331_;
goto v___jp_354_;
}
v___jp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_349_ = l_Lake_BuildTrace_mix(v_trace_333_, v_trace_339_);
v___x_350_ = lean_nat_add(v_buildTime_334_, v_buildTime_340_);
lean_dec(v_buildTime_340_);
lean_dec(v_buildTime_334_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 2, v___x_350_);
lean_ctor_set(v___x_342_, 1, v___x_349_);
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_352_ = v___x_342_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*3, v___x_345_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*3 + 1, v___y_347_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*3 + 2, v___y_348_);
return v___x_352_;
}
}
v___jp_354_:
{
if (v_canceled_332_ == 0)
{
v___y_347_ = v___y_355_;
v___y_348_ = v_canceled_338_;
goto v___jp_346_;
}
else
{
v___y_347_ = v___y_355_;
v___y_348_ = v_canceled_332_;
goto v___jp_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object* v_f_357_, lean_object* v_s_358_){
_start:
{
lean_object* v_log_359_; uint8_t v_action_360_; uint8_t v_wantsRebuild_361_; uint8_t v_canceled_362_; lean_object* v_trace_363_; lean_object* v_buildTime_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
v_log_359_ = lean_ctor_get(v_s_358_, 0);
v_action_360_ = lean_ctor_get_uint8(v_s_358_, sizeof(void*)*3);
v_wantsRebuild_361_ = lean_ctor_get_uint8(v_s_358_, sizeof(void*)*3 + 1);
v_canceled_362_ = lean_ctor_get_uint8(v_s_358_, sizeof(void*)*3 + 2);
v_trace_363_ = lean_ctor_get(v_s_358_, 1);
v_buildTime_364_ = lean_ctor_get(v_s_358_, 2);
v_isSharedCheck_372_ = !lean_is_exclusive(v_s_358_);
if (v_isSharedCheck_372_ == 0)
{
v___x_366_ = v_s_358_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_buildTime_364_);
lean_inc(v_trace_363_);
lean_inc(v_log_359_);
lean_dec(v_s_358_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_apply_1(v_f_357_, v_log_359_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_trace_363_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_buildTime_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*3, v_action_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*3 + 1, v_wantsRebuild_361_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*3 + 2, v_canceled_362_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object* v_e_373_, lean_object* v_s_374_){
_start:
{
lean_object* v_log_375_; uint8_t v_action_376_; uint8_t v_wantsRebuild_377_; uint8_t v_canceled_378_; lean_object* v_trace_379_; lean_object* v_buildTime_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_388_; 
v_log_375_ = lean_ctor_get(v_s_374_, 0);
v_action_376_ = lean_ctor_get_uint8(v_s_374_, sizeof(void*)*3);
v_wantsRebuild_377_ = lean_ctor_get_uint8(v_s_374_, sizeof(void*)*3 + 1);
v_canceled_378_ = lean_ctor_get_uint8(v_s_374_, sizeof(void*)*3 + 2);
v_trace_379_ = lean_ctor_get(v_s_374_, 1);
v_buildTime_380_ = lean_ctor_get(v_s_374_, 2);
v_isSharedCheck_388_ = !lean_is_exclusive(v_s_374_);
if (v_isSharedCheck_388_ == 0)
{
v___x_382_ = v_s_374_;
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_buildTime_380_);
lean_inc(v_trace_379_);
lean_inc(v_log_375_);
lean_dec(v_s_374_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_array_push(v_log_375_, v_e_373_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_trace_379_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_buildTime_380_);
lean_ctor_set_uint8(v_reuseFailAlloc_387_, sizeof(void*)*3, v_action_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_387_, sizeof(void*)*3 + 1, v_wantsRebuild_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_387_, sizeof(void*)*3 + 2, v_canceled_378_);
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
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object* v_log_389_, lean_object* v_self_390_){
_start:
{
if (lean_obj_tag(v_self_390_) == 0)
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_413_; 
v_a_391_ = lean_ctor_get(v_self_390_, 1);
v_a_392_ = lean_ctor_get(v_self_390_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_self_390_);
if (v_isSharedCheck_413_ == 0)
{
v___x_394_ = v_self_390_;
v_isShared_395_ = v_isSharedCheck_413_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_391_);
lean_inc(v_a_392_);
lean_dec(v_self_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_413_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_log_396_; uint8_t v_action_397_; uint8_t v_wantsRebuild_398_; uint8_t v_canceled_399_; lean_object* v_trace_400_; lean_object* v_buildTime_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_412_; 
v_log_396_ = lean_ctor_get(v_a_391_, 0);
v_action_397_ = lean_ctor_get_uint8(v_a_391_, sizeof(void*)*3);
v_wantsRebuild_398_ = lean_ctor_get_uint8(v_a_391_, sizeof(void*)*3 + 1);
v_canceled_399_ = lean_ctor_get_uint8(v_a_391_, sizeof(void*)*3 + 2);
v_trace_400_ = lean_ctor_get(v_a_391_, 1);
v_buildTime_401_ = lean_ctor_get(v_a_391_, 2);
v_isSharedCheck_412_ = !lean_is_exclusive(v_a_391_);
if (v_isSharedCheck_412_ == 0)
{
v___x_403_ = v_a_391_;
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_buildTime_401_);
lean_inc(v_trace_400_);
lean_inc(v_log_396_);
lean_dec(v_a_391_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = l_Array_append___redArg(v_log_389_, v_log_396_);
lean_dec_ref(v_log_396_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_trace_400_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_buildTime_401_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, sizeof(void*)*3, v_action_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, sizeof(void*)*3 + 1, v_wantsRebuild_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, sizeof(void*)*3 + 2, v_canceled_399_);
v___x_407_ = v_reuseFailAlloc_411_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_407_);
v___x_409_ = v___x_394_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_392_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_438_; 
v_a_414_ = lean_ctor_get(v_self_390_, 1);
v_a_415_ = lean_ctor_get(v_self_390_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_self_390_);
if (v_isSharedCheck_438_ == 0)
{
v___x_417_ = v_self_390_;
v_isShared_418_ = v_isSharedCheck_438_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_414_);
lean_inc(v_a_415_);
lean_dec(v_self_390_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_438_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_log_419_; uint8_t v_action_420_; uint8_t v_wantsRebuild_421_; uint8_t v_canceled_422_; lean_object* v_trace_423_; lean_object* v_buildTime_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_437_; 
v_log_419_ = lean_ctor_get(v_a_414_, 0);
v_action_420_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*3);
v_wantsRebuild_421_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*3 + 1);
v_canceled_422_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*3 + 2);
v_trace_423_ = lean_ctor_get(v_a_414_, 1);
v_buildTime_424_ = lean_ctor_get(v_a_414_, 2);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_414_);
if (v_isSharedCheck_437_ == 0)
{
v___x_426_ = v_a_414_;
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_buildTime_424_);
lean_inc(v_trace_423_);
lean_inc(v_log_419_);
lean_dec(v_a_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_428_ = lean_array_get_size(v_log_389_);
v___x_429_ = lean_nat_add(v___x_428_, v_a_415_);
lean_dec(v_a_415_);
v___x_430_ = l_Array_append___redArg(v_log_389_, v_log_419_);
lean_dec_ref(v_log_419_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_430_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_trace_423_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_buildTime_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*3, v_action_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*3 + 1, v_wantsRebuild_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*3 + 2, v_canceled_422_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_432_);
lean_ctor_set(v___x_417_, 0, v___x_429_);
v___x_434_ = v___x_417_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object* v_00_u03b1_439_, lean_object* v_log_440_, lean_object* v_self_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lake_JobResult_prependLog___redArg(v_log_440_, v_self_441_);
return v___x_442_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobResult_isCanceled___redArg(lean_object* v_x_443_){
_start:
{
if (lean_obj_tag(v_x_443_) == 0)
{
uint8_t v___x_444_; 
v___x_444_ = 0;
return v___x_444_;
}
else
{
lean_object* v_a_445_; uint8_t v_canceled_446_; 
v_a_445_ = lean_ctor_get(v_x_443_, 1);
v_canceled_446_ = lean_ctor_get_uint8(v_a_445_, sizeof(void*)*3 + 2);
return v_canceled_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___redArg___boxed(lean_object* v_x_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Lake_JobResult_isCanceled___redArg(v_x_447_);
lean_dec_ref(v_x_447_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t l_Lake_JobResult_isCanceled(lean_object* v_00_u03b1_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
else
{
lean_object* v_a_453_; uint8_t v_canceled_454_; 
v_a_453_ = lean_ctor_get(v_x_451_, 1);
v_canceled_454_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*3 + 2);
return v_canceled_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___boxed(lean_object* v_00_u03b1_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Lake_JobResult_isCanceled(v_00_u03b1_455_, v_x_456_);
lean_dec_ref(v_x_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__0(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = l_Lake_instInhabitedJobState_default;
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__1(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__0, &l_Lake_instInhabitedJob___redArg___closed__0_once, _init_l_Lake_instInhabitedJob___redArg___closed__0);
v___x_463_ = lean_task_pure(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__3(void){
_start:
{
uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_465_ = 0;
v___x_466_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_467_ = lean_box(0);
v___x_468_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__1, &l_Lake_instInhabitedJob___redArg___closed__1_once, _init_l_Lake_instInhabitedJob___redArg___closed__1);
v___x_469_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
lean_ctor_set(v___x_469_, 2, v___x_466_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*3, v___x_465_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob___redArg(){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__3, &l_Lake_instInhabitedJob___redArg___closed__3_once, _init_l_Lake_instInhabitedJob___redArg___closed__3);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob___redArg___boxed(lean_object* v___dummy_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lake_instInhabitedJob___redArg();
return v_res_473_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lake_instInhabitedJob___redArg();
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_477_){
_start:
{
lean_inc_ref(v_self_477_);
return v_self_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lake_Job_cast___redArg(v_self_478_);
lean_dec_ref(v_self_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_480_, lean_object* v_self_481_, lean_object* v_h_482_){
_start:
{
lean_inc_ref(v_self_481_);
return v_self_481_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_483_, lean_object* v_self_484_, lean_object* v_h_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lake_Job_cast(v_00_u03b1_483_, v_self_484_, v_h_485_);
lean_dec_ref(v_self_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_487_, lean_object* v_task_488_, lean_object* v_caption_489_){
_start:
{
uint8_t v___x_490_; lean_object* v___x_491_; 
v___x_490_ = 0;
v___x_491_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_491_, 0, v_task_488_);
lean_ctor_set(v___x_491_, 1, v_inst_487_);
lean_ctor_set(v___x_491_, 2, v_caption_489_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*3, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_492_, lean_object* v_inst_493_, lean_object* v_task_494_, lean_object* v_caption_495_){
_start:
{
uint8_t v___x_496_; lean_object* v___x_497_; 
v___x_496_ = 0;
v___x_497_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_497_, 0, v_task_494_);
lean_ctor_set(v___x_497_, 1, v_inst_493_);
lean_ctor_set(v___x_497_, 2, v_caption_495_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*3, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_498_, lean_object* v_log_499_, lean_object* v_caption_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = 0;
v___x_503_ = 0;
v___x_504_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_505_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_505_, 0, v_log_499_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
lean_ctor_set(v___x_505_, 2, v___x_501_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*3, v___x_502_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*3 + 1, v___x_503_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*3 + 2, v___x_503_);
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_501_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = lean_task_pure(v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_inst_498_);
lean_ctor_set(v___x_508_, 2, v_caption_500_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*3, v___x_503_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_509_, lean_object* v_inst_510_, lean_object* v_log_511_, lean_object* v_caption_512_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = 0;
v___x_515_ = 0;
v___x_516_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_517_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_517_, 0, v_log_511_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
lean_ctor_set(v___x_517_, 2, v___x_513_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3, v___x_514_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3 + 1, v___x_515_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3 + 2, v___x_515_);
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_513_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_task_pure(v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_inst_510_);
lean_ctor_set(v___x_520_, 2, v_caption_512_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*3, v___x_515_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_521_, lean_object* v_a_522_, lean_object* v_log_523_, lean_object* v_caption_524_){
_start:
{
uint8_t v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_525_ = 0;
v___x_526_ = 0;
v___x_527_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_529_, 0, v_log_523_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3, v___x_525_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3 + 1, v___x_526_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3 + 2, v___x_526_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_522_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_task_pure(v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_kind_521_);
lean_ctor_set(v___x_532_, 2, v_caption_524_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*3, v___x_526_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_533_, lean_object* v_kind_534_, lean_object* v_a_535_, lean_object* v_log_536_, lean_object* v_caption_537_){
_start:
{
uint8_t v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_538_ = 0;
v___x_539_ = 0;
v___x_540_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_542_, 0, v_log_536_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_ctor_set(v___x_542_, 2, v___x_541_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*3, v___x_538_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*3 + 1, v___x_539_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*3 + 2, v___x_539_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_a_535_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_task_pure(v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_kind_534_);
lean_ctor_set(v___x_545_, 2, v_caption_537_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*3, v___x_539_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_548_ = lean_box(0);
v___x_549_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_550_ = 0;
v___x_551_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_a_547_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_task_pure(v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___x_548_);
lean_ctor_set(v___x_554_, 2, v___x_549_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*3, v___x_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_557_, lean_object* v_caption_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_562_ = 0;
v___x_563_ = 0;
v___x_564_ = l_Lake_BuildTrace_nil(v_caption_558_);
v___x_565_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_565_, 0, v___x_561_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
lean_ctor_set(v___x_565_, 2, v___x_560_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*3, v___x_562_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*3 + 1, v___x_563_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*3 + 2, v___x_563_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_a_557_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_task_pure(v___x_566_);
v___x_568_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_569_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_559_);
lean_ctor_set(v___x_569_, 2, v___x_568_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*3, v___x_563_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_570_, lean_object* v_a_571_, lean_object* v_caption_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_576_ = 0;
v___x_577_ = 0;
v___x_578_ = l_Lake_BuildTrace_nil(v_caption_572_);
v___x_579_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_579_, 0, v___x_575_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
lean_ctor_set(v___x_579_, 2, v___x_574_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*3, v___x_576_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*3 + 1, v___x_577_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*3 + 2, v___x_577_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_a_571_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_task_pure(v___x_580_);
v___x_582_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_583_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_573_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*3, v___x_577_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_584_, lean_object* v_caption_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_586_ = l_Lake_instDataKindUnit;
v___x_587_ = lean_box(0);
v___x_588_ = 0;
v___x_589_ = 0;
v___x_590_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_592_, 0, v_log_584_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3, v___x_588_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3 + 1, v___x_589_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3 + 2, v___x_589_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_587_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_task_pure(v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_586_);
lean_ctor_set(v___x_595_, 2, v_caption_585_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3, v___x_589_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_597_ = lean_box(0);
v___x_598_ = lean_box(0);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_601_ = 0;
v___x_602_ = 0;
v___x_603_ = l_Lake_BuildTrace_nil(v_traceCaption_596_);
v___x_604_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
lean_ctor_set(v___x_604_, 2, v___x_599_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*3, v___x_601_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*3 + 1, v___x_602_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*3 + 2, v___x_602_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_597_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_task_pure(v___x_605_);
v___x_607_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_608_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_598_);
lean_ctor_set(v___x_608_, 2, v___x_607_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*3, v___x_602_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_609_){
_start:
{
lean_object* v_task_610_; lean_object* v___x_611_; lean_object* v_a_612_; lean_object* v_trace_613_; 
v_task_610_ = lean_ctor_get(v_job_609_, 0);
lean_inc_ref(v_task_610_);
lean_dec_ref(v_job_609_);
v___x_611_ = lean_task_get_own(v_task_610_);
v_a_612_ = lean_ctor_get(v___x_611_, 1);
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v_trace_613_ = lean_ctor_get(v_a_612_, 1);
lean_inc_ref(v_trace_613_);
lean_dec(v_a_612_);
return v_trace_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_614_, lean_object* v_job_615_){
_start:
{
lean_object* v_task_616_; lean_object* v___x_617_; lean_object* v_a_618_; lean_object* v_trace_619_; 
v_task_616_ = lean_ctor_get(v_job_615_, 0);
lean_inc_ref(v_task_616_);
lean_dec_ref(v_job_615_);
v___x_617_ = lean_task_get_own(v_task_616_);
v_a_618_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v_trace_619_ = lean_ctor_get(v_a_618_, 1);
lean_inc_ref(v_trace_619_);
lean_dec(v_a_618_);
return v_trace_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_620_, lean_object* v_job_621_){
_start:
{
lean_object* v_task_622_; lean_object* v_kind_623_; uint8_t v_optional_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
v_task_622_ = lean_ctor_get(v_job_621_, 0);
v_kind_623_ = lean_ctor_get(v_job_621_, 1);
v_optional_624_ = lean_ctor_get_uint8(v_job_621_, sizeof(void*)*3);
v_isSharedCheck_631_ = !lean_is_exclusive(v_job_621_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_job_621_, 2);
lean_dec(v_unused_632_);
v___x_626_ = v_job_621_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_kind_623_);
lean_inc(v_task_622_);
lean_dec(v_job_621_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 2, v_caption_620_);
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_task_622_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_kind_623_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_caption_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, sizeof(void*)*3, v_optional_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_633_, lean_object* v_caption_634_, lean_object* v_job_635_){
_start:
{
lean_object* v_task_636_; lean_object* v_kind_637_; uint8_t v_optional_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_task_636_ = lean_ctor_get(v_job_635_, 0);
v_kind_637_ = lean_ctor_get(v_job_635_, 1);
v_optional_638_ = lean_ctor_get_uint8(v_job_635_, sizeof(void*)*3);
v_isSharedCheck_645_ = !lean_is_exclusive(v_job_635_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_job_635_, 2);
lean_dec(v_unused_646_);
v___x_640_ = v_job_635_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_kind_637_);
lean_inc(v_task_636_);
lean_dec(v_job_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v_caption_634_);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_task_636_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_kind_637_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_caption_634_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*3, v_optional_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_647_, lean_object* v_job_648_){
_start:
{
lean_object* v_task_649_; lean_object* v_kind_650_; lean_object* v_caption_651_; uint8_t v_optional_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_task_649_ = lean_ctor_get(v_job_648_, 0);
v_kind_650_ = lean_ctor_get(v_job_648_, 1);
v_caption_651_ = lean_ctor_get(v_job_648_, 2);
v_optional_652_ = lean_ctor_get_uint8(v_job_648_, sizeof(void*)*3);
v___x_653_ = lean_string_utf8_byte_size(v_caption_651_);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_nat_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_dec_ref(v_caption_647_);
return v_job_648_;
}
else
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_inc(v_kind_650_);
lean_inc_ref(v_task_649_);
v_isSharedCheck_662_ = !lean_is_exclusive(v_job_648_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; lean_object* v_unused_664_; lean_object* v_unused_665_; 
v_unused_663_ = lean_ctor_get(v_job_648_, 2);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v_job_648_, 1);
lean_dec(v_unused_664_);
v_unused_665_ = lean_ctor_get(v_job_648_, 0);
lean_dec(v_unused_665_);
v___x_657_ = v_job_648_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_job_648_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 2, v_caption_647_);
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_task_649_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_kind_650_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_caption_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*3, v_optional_652_);
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
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_666_, lean_object* v_caption_667_, lean_object* v_job_668_){
_start:
{
lean_object* v_task_669_; lean_object* v_kind_670_; lean_object* v_caption_671_; uint8_t v_optional_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_task_669_ = lean_ctor_get(v_job_668_, 0);
v_kind_670_ = lean_ctor_get(v_job_668_, 1);
v_caption_671_ = lean_ctor_get(v_job_668_, 2);
v_optional_672_ = lean_ctor_get_uint8(v_job_668_, sizeof(void*)*3);
v___x_673_ = lean_string_utf8_byte_size(v_caption_671_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_nat_dec_eq(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec_ref(v_caption_667_);
return v_job_668_;
}
else
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_inc(v_kind_670_);
lean_inc_ref(v_task_669_);
v_isSharedCheck_682_ = !lean_is_exclusive(v_job_668_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_683_ = lean_ctor_get(v_job_668_, 2);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_job_668_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_job_668_, 0);
lean_dec(v_unused_685_);
v___x_677_ = v_job_668_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_job_668_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 2, v_caption_667_);
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_task_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_kind_670_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_caption_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_681_, sizeof(void*)*3, v_optional_672_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_686_, lean_object* v_f_687_, lean_object* v_self_688_, lean_object* v_prio_689_, uint8_t v_sync_690_){
_start:
{
lean_object* v_task_691_; lean_object* v_caption_692_; uint8_t v_optional_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_task_691_ = lean_ctor_get(v_self_688_, 0);
v_caption_692_ = lean_ctor_get(v_self_688_, 2);
v_optional_693_ = lean_ctor_get_uint8(v_self_688_, sizeof(void*)*3);
v_isSharedCheck_701_ = !lean_is_exclusive(v_self_688_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v_self_688_, 1);
lean_dec(v_unused_702_);
v___x_695_ = v_self_688_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_caption_692_);
lean_inc(v_task_691_);
lean_dec(v_self_688_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_task_map(v_f_687_, v_task_691_, v_prio_689_, v_sync_690_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_inst_686_);
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_inst_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_caption_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_700_, sizeof(void*)*3, v_optional_693_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_703_, lean_object* v_f_704_, lean_object* v_self_705_, lean_object* v_prio_706_, lean_object* v_sync_707_){
_start:
{
uint8_t v_sync_boxed_708_; lean_object* v_res_709_; 
v_sync_boxed_708_ = lean_unbox(v_sync_707_);
v_res_709_ = l_Lake_Job_mapResult___redArg(v_inst_703_, v_f_704_, v_self_705_, v_prio_706_, v_sync_boxed_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_710_, lean_object* v_00_u03b1_711_, lean_object* v_inst_712_, lean_object* v_f_713_, lean_object* v_self_714_, lean_object* v_prio_715_, uint8_t v_sync_716_){
_start:
{
lean_object* v_task_717_; lean_object* v_caption_718_; uint8_t v_optional_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_task_717_ = lean_ctor_get(v_self_714_, 0);
v_caption_718_ = lean_ctor_get(v_self_714_, 2);
v_optional_719_ = lean_ctor_get_uint8(v_self_714_, sizeof(void*)*3);
v_isSharedCheck_727_ = !lean_is_exclusive(v_self_714_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_self_714_, 1);
lean_dec(v_unused_728_);
v___x_721_ = v_self_714_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_caption_718_);
lean_inc(v_task_717_);
lean_dec(v_self_714_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_task_map(v_f_713_, v_task_717_, v_prio_715_, v_sync_716_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_inst_712_);
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_inst_712_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_caption_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_726_, sizeof(void*)*3, v_optional_719_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_729_, lean_object* v_00_u03b1_730_, lean_object* v_inst_731_, lean_object* v_f_732_, lean_object* v_self_733_, lean_object* v_prio_734_, lean_object* v_sync_735_){
_start:
{
uint8_t v_sync_boxed_736_; lean_object* v_res_737_; 
v_sync_boxed_736_ = lean_unbox(v_sync_735_);
v_res_737_ = l_Lake_Job_mapResult(v_00_u03b2_729_, v_00_u03b1_730_, v_inst_731_, v_f_732_, v_self_733_, v_prio_734_, v_sync_boxed_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_738_, lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_740_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_a_740_);
v_a_741_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_a_741_);
lean_dec_ref_known(v_x_739_, 2);
v___x_742_ = lean_apply_2(v_f_738_, v_a_740_, v_a_741_);
return v___x_742_;
}
else
{
lean_object* v_a_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_f_738_);
v_a_743_ = lean_ctor_get(v_x_739_, 0);
v_a_744_ = lean_ctor_get(v_x_739_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v_x_739_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_inc(v_a_743_);
lean_dec(v_x_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_743_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_752_, lean_object* v_f_753_, lean_object* v_self_754_, lean_object* v_prio_755_, uint8_t v_sync_756_){
_start:
{
lean_object* v_task_757_; lean_object* v_caption_758_; uint8_t v_optional_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_768_; 
v_task_757_ = lean_ctor_get(v_self_754_, 0);
v_caption_758_ = lean_ctor_get(v_self_754_, 2);
v_optional_759_ = lean_ctor_get_uint8(v_self_754_, sizeof(void*)*3);
v_isSharedCheck_768_ = !lean_is_exclusive(v_self_754_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_self_754_, 1);
lean_dec(v_unused_769_);
v___x_761_ = v_self_754_;
v_isShared_762_ = v_isSharedCheck_768_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_caption_758_);
lean_inc(v_task_757_);
lean_dec(v_self_754_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_768_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___f_763_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_763_, 0, v_f_753_);
v___x_764_ = lean_task_map(v___f_763_, v_task_757_, v_prio_755_, v_sync_756_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_inst_752_);
lean_ctor_set(v___x_761_, 0, v___x_764_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_inst_752_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_caption_758_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*3, v_optional_759_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* v_inst_770_, lean_object* v_f_771_, lean_object* v_self_772_, lean_object* v_prio_773_, lean_object* v_sync_774_){
_start:
{
uint8_t v_sync_boxed_775_; lean_object* v_res_776_; 
v_sync_boxed_775_ = lean_unbox(v_sync_774_);
v_res_776_ = l_Lake_Job_mapOk___redArg(v_inst_770_, v_f_771_, v_self_772_, v_prio_773_, v_sync_boxed_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_777_, lean_object* v_00_u03b1_778_, lean_object* v_inst_779_, lean_object* v_f_780_, lean_object* v_self_781_, lean_object* v_prio_782_, uint8_t v_sync_783_){
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
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_797_, lean_object* v_00_u03b1_798_, lean_object* v_inst_799_, lean_object* v_f_800_, lean_object* v_self_801_, lean_object* v_prio_802_, lean_object* v_sync_803_){
_start:
{
uint8_t v_sync_boxed_804_; lean_object* v_res_805_; 
v_sync_boxed_804_ = lean_unbox(v_sync_803_);
v_res_805_ = l_Lake_Job_mapOk(v_00_u03b2_797_, v_00_u03b1_798_, v_inst_799_, v_f_800_, v_self_801_, v_prio_802_, v_sync_boxed_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
v_a_808_ = lean_ctor_get(v_x_807_, 0);
v_a_809_ = lean_ctor_get(v_x_807_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_817_ == 0)
{
v___x_811_ = v_x_807_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_inc(v_a_808_);
lean_dec(v_x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_apply_1(v_f_806_, v_a_808_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_a_809_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_f_806_);
v_a_818_ = lean_ctor_get(v_x_807_, 0);
v_a_819_ = lean_ctor_get(v_x_807_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v_x_807_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_inc(v_a_818_);
lean_dec(v_x_807_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_827_, lean_object* v_f_828_, lean_object* v_self_829_, lean_object* v_prio_830_, uint8_t v_sync_831_){
_start:
{
lean_object* v_task_832_; lean_object* v_caption_833_; uint8_t v_optional_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_843_; 
v_task_832_ = lean_ctor_get(v_self_829_, 0);
v_caption_833_ = lean_ctor_get(v_self_829_, 2);
v_optional_834_ = lean_ctor_get_uint8(v_self_829_, sizeof(void*)*3);
v_isSharedCheck_843_ = !lean_is_exclusive(v_self_829_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_self_829_, 1);
lean_dec(v_unused_844_);
v___x_836_ = v_self_829_;
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_caption_833_);
lean_inc(v_task_832_);
lean_dec(v_self_829_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___f_838_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_838_, 0, v_f_828_);
v___x_839_ = lean_task_map(v___f_838_, v_task_832_, v_prio_830_, v_sync_831_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_inst_827_);
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_inst_827_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_caption_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3, v_optional_834_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_845_, lean_object* v_f_846_, lean_object* v_self_847_, lean_object* v_prio_848_, lean_object* v_sync_849_){
_start:
{
uint8_t v_sync_boxed_850_; lean_object* v_res_851_; 
v_sync_boxed_850_ = lean_unbox(v_sync_849_);
v_res_851_ = l_Lake_Job_map___redArg(v_inst_845_, v_f_846_, v_self_847_, v_prio_848_, v_sync_boxed_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_852_, lean_object* v_00_u03b1_853_, lean_object* v_inst_854_, lean_object* v_f_855_, lean_object* v_self_856_, lean_object* v_prio_857_, uint8_t v_sync_858_){
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
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_872_, lean_object* v_00_u03b1_873_, lean_object* v_inst_874_, lean_object* v_f_875_, lean_object* v_self_876_, lean_object* v_prio_877_, lean_object* v_sync_878_){
_start:
{
uint8_t v_sync_boxed_879_; lean_object* v_res_880_; 
v_sync_boxed_879_ = lean_unbox(v_sync_878_);
v_res_880_ = l_Lake_Job_map(v_00_u03b2_872_, v_00_u03b1_873_, v_inst_874_, v_f_875_, v_self_876_, v_prio_877_, v_sync_boxed_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_f_883_, lean_object* v_self_884_){
_start:
{
lean_object* v_task_885_; lean_object* v_caption_886_; uint8_t v_optional_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_899_; 
v_task_885_ = lean_ctor_get(v_self_884_, 0);
v_caption_886_ = lean_ctor_get(v_self_884_, 2);
v_optional_887_ = lean_ctor_get_uint8(v_self_884_, sizeof(void*)*3);
v_isSharedCheck_899_ = !lean_is_exclusive(v_self_884_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_self_884_, 1);
lean_dec(v_unused_900_);
v___x_889_ = v_self_884_;
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_caption_886_);
lean_inc(v_task_885_);
lean_dec(v_self_884_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___f_891_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_891_, 0, v_f_883_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = 0;
v___x_895_ = lean_task_map(v___f_891_, v_task_885_, v___x_893_, v___x_894_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_892_);
lean_ctor_set(v___x_889_, 0, v___x_895_);
v___x_897_ = v___x_889_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_caption_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*3, v_optional_887_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_901_, lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_906_, 0, lean_box(0));
lean_closure_set(v___x_906_, 1, lean_box(0));
lean_closure_set(v___x_906_, 2, v___y_904_);
v___x_907_ = lean_apply_4(v___f_901_, lean_box(0), lean_box(0), v___x_906_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_915_){
_start:
{
lean_inc_ref(v_self_915_);
return v_self_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_916_);
lean_dec_ref(v_self_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_918_, lean_object* v_self_919_){
_start:
{
lean_inc_ref(v_self_919_);
return v_self_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_920_, lean_object* v_self_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_920_, v_self_921_);
lean_dec_ref(v_self_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg(){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0));
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___boxed(lean_object* v___dummy_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg();
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0));
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_930_){
_start:
{
lean_object* v_task_931_; lean_object* v_caption_932_; uint8_t v_optional_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_941_; 
v_task_931_ = lean_ctor_get(v_job_930_, 0);
v_caption_932_ = lean_ctor_get(v_job_930_, 2);
v_optional_933_ = lean_ctor_get_uint8(v_job_930_, sizeof(void*)*3);
v_isSharedCheck_941_ = !lean_is_exclusive(v_job_930_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_job_930_, 1);
lean_dec(v_unused_942_);
v___x_935_ = v_job_930_;
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_caption_932_);
lean_inc(v_task_931_);
lean_dec(v_job_930_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v___x_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_task_931_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_caption_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3, v_optional_933_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_943_, lean_object* v_job_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lake_Job_toOpaque___redArg(v_job_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg(){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0));
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg___boxed(lean_object* v___dummy_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lake_instCoeOutJobOpaqueJob___redArg();
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* v_00_u03b1_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0));
return v___x_952_;
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
