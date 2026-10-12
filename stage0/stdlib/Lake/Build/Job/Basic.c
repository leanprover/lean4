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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Lake_JobAction_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lake_JobAction_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lake_JobAction_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_JobAction_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_JobAction_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lake_JobAction_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lake_JobAction_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lake_JobAction_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lake_JobAction_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg(lean_object* v_unknown_24_){
_start:
{
lean_inc(v_unknown_24_);
return v_unknown_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___redArg___boxed(lean_object* v_unknown_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_JobAction_unknown_elim___redArg(v_unknown_25_);
lean_dec(v_unknown_25_);
return v_res_26_;
}
}
lean_object* l_Lake_JobAction_unknown_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_unknown_30_){
_start:
{
lean_inc(v_unknown_30_);
return v_unknown_30_;
}
}
LEAN_EXPORT void l_Lake_JobAction_unknown_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_unknown_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_JobAction_unknown_elim(lean_box(0), v_t_28_, lean_box(0), v_unknown_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unknown_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_unknown_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lake_JobAction_unknown_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_unknown_35_);
lean_dec(v_unknown_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg(lean_object* v_reuse_38_){
_start:
{
lean_inc(v_reuse_38_);
return v_reuse_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_reuse_elim___redArg___boxed(lean_object* v_reuse_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_JobAction_reuse_elim___redArg(v_reuse_39_);
lean_dec(v_reuse_39_);
return v_res_40_;
}
}
lean_object* l_Lake_JobAction_reuse_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_reuse_44_){
_start:
{
lean_inc(v_reuse_44_);
return v_reuse_44_;
}
}
LEAN_EXPORT void l_Lake_JobAction_reuse_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_reuse_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lake_JobAction_reuse_elim(lean_box(0), v_t_42_, lean_box(0), v_reuse_44_);
stack->m_obj
 = v_res_45_;
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
lean_object* l_Lake_JobAction_replay_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_replay_58_){
_start:
{
lean_inc(v_replay_58_);
return v_replay_58_;
}
}
LEAN_EXPORT void l_Lake_JobAction_replay_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_replay_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lake_JobAction_replay_elim(lean_box(0), v_t_56_, lean_box(0), v_replay_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_replay_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_replay_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lake_JobAction_replay_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_replay_63_);
lean_dec(v_replay_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg(lean_object* v_unpack_66_){
_start:
{
lean_inc(v_unpack_66_);
return v_unpack_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___redArg___boxed(lean_object* v_unpack_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lake_JobAction_unpack_elim___redArg(v_unpack_67_);
lean_dec(v_unpack_67_);
return v_res_68_;
}
}
lean_object* l_Lake_JobAction_unpack_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_unpack_72_){
_start:
{
lean_inc(v_unpack_72_);
return v_unpack_72_;
}
}
LEAN_EXPORT void l_Lake_JobAction_unpack_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_unpack_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lake_JobAction_unpack_elim(lean_box(0), v_t_70_, lean_box(0), v_unpack_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_unpack_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_unpack_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Lake_JobAction_unpack_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_unpack_77_);
lean_dec(v_unpack_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg(lean_object* v_fetch_80_){
_start:
{
lean_inc(v_fetch_80_);
return v_fetch_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___redArg___boxed(lean_object* v_fetch_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lake_JobAction_fetch_elim___redArg(v_fetch_81_);
lean_dec(v_fetch_81_);
return v_res_82_;
}
}
lean_object* l_Lake_JobAction_fetch_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_fetch_86_){
_start:
{
lean_inc(v_fetch_86_);
return v_fetch_86_;
}
}
LEAN_EXPORT void l_Lake_JobAction_fetch_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_84_ = stack[1].m_num;
lean_object* v_fetch_86_ = stack[3].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lake_JobAction_fetch_elim(lean_box(0), v_t_84_, lean_box(0), v_fetch_86_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_fetch_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_fetch_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l_Lake_JobAction_fetch_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_fetch_91_);
lean_dec(v_fetch_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg(lean_object* v_build_94_){
_start:
{
lean_inc(v_build_94_);
return v_build_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___redArg___boxed(lean_object* v_build_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lake_JobAction_build_elim___redArg(v_build_95_);
lean_dec(v_build_95_);
return v_res_96_;
}
}
lean_object* l_Lake_JobAction_build_elim(lean_object* v_motive_97_, uint8_t v_t_98_, lean_object* v_h_99_, lean_object* v_build_100_){
_start:
{
lean_inc(v_build_100_);
return v_build_100_;
}
}
LEAN_EXPORT void l_Lake_JobAction_build_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_98_ = stack[1].m_num;
lean_object* v_build_100_ = stack[3].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Lake_JobAction_build_elim(lean_box(0), v_t_98_, lean_box(0), v_build_100_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_build_elim___boxed(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_build_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_Lake_JobAction_build_elim(v_motive_102_, v_t_boxed_106_, v_h_104_, v_build_105_);
lean_dec(v_build_105_);
return v_res_107_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction_default(void){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__12(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(2u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lake_instReprJobAction_repr___closed__13(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
lean_object* l_Lake_instReprJobAction_repr(uint8_t v_x_132_, lean_object* v_prec_133_){
_start:
{
lean_object* v___y_135_; lean_object* v___y_142_; lean_object* v___y_149_; lean_object* v___y_156_; lean_object* v___y_163_; lean_object* v___y_170_; 
switch(v_x_132_)
{
case 0:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_nat_dec_le(v___x_176_, v_prec_133_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_135_ = v___x_178_;
goto v___jp_134_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_135_ = v___x_179_;
goto v___jp_134_;
}
}
case 1:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1024u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_prec_133_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_142_ = v___x_182_;
goto v___jp_141_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_142_ = v___x_183_;
goto v___jp_141_;
}
}
case 2:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_185_ = lean_nat_dec_le(v___x_184_, v_prec_133_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_149_ = v___x_186_;
goto v___jp_148_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_149_ = v___x_187_;
goto v___jp_148_;
}
}
case 3:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1024u);
v___x_189_ = lean_nat_dec_le(v___x_188_, v_prec_133_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_156_ = v___x_190_;
goto v___jp_155_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_156_ = v___x_191_;
goto v___jp_155_;
}
}
case 4:
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1024u);
v___x_193_ = lean_nat_dec_le(v___x_192_, v_prec_133_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_163_ = v___x_194_;
goto v___jp_162_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_163_ = v___x_195_;
goto v___jp_162_;
}
}
default: 
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1024u);
v___x_197_ = lean_nat_dec_le(v___x_196_, v_prec_133_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__12, &l_Lake_instReprJobAction_repr___closed__12_once, _init_l_Lake_instReprJobAction_repr___closed__12);
v___y_170_ = v___x_198_;
goto v___jp_169_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lake_instReprJobAction_repr___closed__13, &l_Lake_instReprJobAction_repr___closed__13_once, _init_l_Lake_instReprJobAction_repr___closed__13);
v___y_170_ = v___x_199_;
goto v___jp_169_;
}
}
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__1));
lean_inc(v___y_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = 0;
v___x_139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_prec_133_);
return v___x_140_;
}
v___jp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__3));
lean_inc(v___y_142_);
v___x_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = 0;
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_prec_133_);
return v___x_147_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_150_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__5));
lean_inc(v___y_149_);
v___x_151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_151_, 0, v___y_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = 0;
v___x_153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*1, v___x_152_);
v___x_154_ = l_Repr_addAppParen(v___x_153_, v_prec_133_);
return v___x_154_;
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__7));
lean_inc(v___y_156_);
v___x_158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_158_, 0, v___y_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = 0;
v___x_160_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v___x_159_);
v___x_161_ = l_Repr_addAppParen(v___x_160_, v_prec_133_);
return v___x_161_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__9));
lean_inc(v___y_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = l_Repr_addAppParen(v___x_167_, v_prec_133_);
return v___x_168_;
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = ((lean_object*)(l_Lake_instReprJobAction_repr___closed__11));
lean_inc(v___y_170_);
v___x_172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_172_, 0, v___y_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = 0;
v___x_174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*1, v___x_173_);
v___x_175_ = l_Repr_addAppParen(v___x_174_, v_prec_133_);
return v___x_175_;
}
}
}
LEAN_EXPORT void l_Lake_instReprJobAction_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_132_ = stack[0].m_num;
lean_object* v_prec_133_ = stack[1].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lake_instReprJobAction_repr(v_x_132_, v_prec_133_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lake_instReprJobAction_repr___boxed(lean_object* v_x_201_, lean_object* v_prec_202_){
_start:
{
uint8_t v_x_333__boxed_203_; lean_object* v_res_204_; 
v_x_333__boxed_203_ = lean_unbox(v_x_201_);
v_res_204_ = l_Lake_instReprJobAction_repr(v_x_333__boxed_203_, v_prec_202_);
lean_dec(v_prec_202_);
return v_res_204_;
}
}
uint8_t l_Lake_JobAction_ofNat(lean_object* v_n_207_){
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
LEAN_EXPORT void l_Lake_JobAction_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_207_ = stack[0].m_obj;
uint8_t v_res_224_;
v_res_224_ = l_Lake_JobAction_ofNat(v_n_207_);
stack->m_num = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ofNat___boxed(lean_object* v_n_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Lake_JobAction_ofNat(v_n_225_);
lean_dec(v_n_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
uint8_t l_Lake_instDecidableEqJobAction(uint8_t v_x_228_, uint8_t v_y_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_230_ = lean_box(v_x_228_);
v___x_231_ = lean_obj_tag_nat(v___x_230_);
lean_dec(v___x_230_);
v___x_232_ = lean_box(v_y_229_);
v___x_233_ = lean_obj_tag_nat(v___x_232_);
lean_dec(v___x_232_);
v___x_234_ = lean_nat_dec_eq(v___x_231_, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqJobAction_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_228_ = stack[0].m_num;
uint8_t v_y_229_ = stack[1].m_num;
uint8_t v_res_235_;
v_res_235_ = l_Lake_instDecidableEqJobAction(v_x_228_, v_y_229_);
stack->m_num = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqJobAction___boxed(lean_object* v_x_236_, lean_object* v_y_237_){
_start:
{
uint8_t v_x_23__boxed_238_; uint8_t v_y_24__boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v_x_23__boxed_238_ = lean_unbox(v_x_236_);
v_y_24__boxed_239_ = lean_unbox(v_y_237_);
v_res_240_ = l_Lake_instDecidableEqJobAction(v_x_23__boxed_238_, v_y_24__boxed_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
uint8_t l_Lake_instOrdJobAction_ord(uint8_t v_x_242_, uint8_t v_y_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_244_ = lean_box(v_x_242_);
v___x_245_ = lean_obj_tag_nat(v___x_244_);
lean_dec(v___x_244_);
v___x_246_ = lean_box(v_y_243_);
v___x_247_ = lean_obj_tag_nat(v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = lean_nat_dec_lt(v___x_245_, v___x_247_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
v___x_249_ = lean_nat_dec_eq(v___x_245_, v___x_247_);
if (v___x_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 2;
return v___x_250_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = 1;
return v___x_251_;
}
}
else
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
}
}
LEAN_EXPORT void l_Lake_instOrdJobAction_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_242_ = stack[0].m_num;
uint8_t v_y_243_ = stack[1].m_num;
uint8_t v_res_253_;
v_res_253_ = l_Lake_instOrdJobAction_ord(v_x_242_, v_y_243_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lake_instOrdJobAction_ord___boxed(lean_object* v_x_254_, lean_object* v_y_255_){
_start:
{
uint8_t v_x_33__boxed_256_; uint8_t v_y_34__boxed_257_; uint8_t v_res_258_; lean_object* v_r_259_; 
v_x_33__boxed_256_ = lean_unbox(v_x_254_);
v_y_34__boxed_257_ = lean_unbox(v_y_255_);
v_res_258_ = l_Lake_instOrdJobAction_ord(v_x_33__boxed_256_, v_y_34__boxed_257_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
static lean_object* _init_l_Lake_JobAction_instLT(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
static lean_object* _init_l_Lake_JobAction_instLE(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
uint8_t l_Lake_JobAction_instMin___lam__0(uint8_t v_x_264_, uint8_t v_y_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = l_Lake_instOrdJobAction_ord(v_x_264_, v_y_265_);
if (v___x_266_ == 2)
{
return v_y_265_;
}
else
{
return v_x_264_;
}
}
}
LEAN_EXPORT void l_Lake_JobAction_instMin___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_264_ = stack[0].m_num;
uint8_t v_y_265_ = stack[1].m_num;
uint8_t v_res_267_;
v_res_267_ = l_Lake_JobAction_instMin___lam__0(v_x_264_, v_y_265_);
stack->m_num = v_res_267_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMin___lam__0___boxed(lean_object* v_x_268_, lean_object* v_y_269_){
_start:
{
uint8_t v_x_boxed_270_; uint8_t v_y_boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_x_boxed_270_ = lean_unbox(v_x_268_);
v_y_boxed_271_ = lean_unbox(v_y_269_);
v_res_272_ = l_Lake_JobAction_instMin___lam__0(v_x_boxed_270_, v_y_boxed_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
uint8_t l_Lake_JobAction_instMax___lam__0(uint8_t v_x_276_, uint8_t v_y_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l_Lake_instOrdJobAction_ord(v_x_276_, v_y_277_);
if (v___x_278_ == 2)
{
return v_x_276_;
}
else
{
return v_y_277_;
}
}
}
LEAN_EXPORT void l_Lake_JobAction_instMax___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_276_ = stack[0].m_num;
uint8_t v_y_277_ = stack[1].m_num;
uint8_t v_res_279_;
v_res_279_ = l_Lake_JobAction_instMax___lam__0(v_x_276_, v_y_277_);
stack->m_num = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_instMax___lam__0___boxed(lean_object* v_x_280_, lean_object* v_y_281_){
_start:
{
uint8_t v_x_boxed_282_; uint8_t v_y_boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_x_boxed_282_ = lean_unbox(v_x_280_);
v_y_boxed_283_ = lean_unbox(v_y_281_);
v_res_284_ = l_Lake_JobAction_instMax___lam__0(v_x_boxed_282_, v_y_boxed_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
uint8_t l_Lake_JobAction_merge(uint8_t v_a_288_, uint8_t v_b_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = l_Lake_instOrdJobAction_ord(v_a_288_, v_b_289_);
if (v___x_290_ == 2)
{
return v_a_288_;
}
else
{
return v_b_289_;
}
}
}
LEAN_EXPORT void l_Lake_JobAction_merge_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_288_ = stack[0].m_num;
uint8_t v_b_289_ = stack[1].m_num;
uint8_t v_res_291_;
v_res_291_ = l_Lake_JobAction_merge(v_a_288_, v_b_289_);
stack->m_num = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_merge___boxed(lean_object* v_a_292_, lean_object* v_b_293_){
_start:
{
uint8_t v_a_boxed_294_; uint8_t v_b_boxed_295_; uint8_t v_res_296_; lean_object* v_r_297_; 
v_a_boxed_294_ = lean_unbox(v_a_292_);
v_b_boxed_295_ = lean_unbox(v_b_293_);
v_res_296_ = l_Lake_JobAction_merge(v_a_boxed_294_, v_b_boxed_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
lean_object* l_Lake_JobAction_verb(uint8_t v_failed_310_, uint8_t v_x_311_){
_start:
{
switch(v_x_311_)
{
case 0:
{
if (v_failed_310_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = ((lean_object*)(l_Lake_JobAction_verb___closed__0));
return v___x_312_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = ((lean_object*)(l_Lake_JobAction_verb___closed__1));
return v___x_313_;
}
}
case 1:
{
if (v_failed_310_ == 0)
{
lean_object* v___x_314_; 
v___x_314_ = ((lean_object*)(l_Lake_JobAction_verb___closed__2));
return v___x_314_;
}
else
{
lean_object* v___x_315_; 
v___x_315_ = ((lean_object*)(l_Lake_JobAction_verb___closed__3));
return v___x_315_;
}
}
case 2:
{
if (v_failed_310_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = ((lean_object*)(l_Lake_JobAction_verb___closed__4));
return v___x_316_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = ((lean_object*)(l_Lake_JobAction_verb___closed__5));
return v___x_317_;
}
}
case 3:
{
if (v_failed_310_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = ((lean_object*)(l_Lake_JobAction_verb___closed__6));
return v___x_318_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = ((lean_object*)(l_Lake_JobAction_verb___closed__7));
return v___x_319_;
}
}
case 4:
{
if (v_failed_310_ == 0)
{
lean_object* v___x_320_; 
v___x_320_ = ((lean_object*)(l_Lake_JobAction_verb___closed__8));
return v___x_320_;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = ((lean_object*)(l_Lake_JobAction_verb___closed__9));
return v___x_321_;
}
}
default: 
{
if (v_failed_310_ == 0)
{
lean_object* v___x_322_; 
v___x_322_ = ((lean_object*)(l_Lake_JobAction_verb___closed__10));
return v___x_322_;
}
else
{
lean_object* v___x_323_; 
v___x_323_ = ((lean_object*)(l_Lake_JobAction_verb___closed__11));
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_JobAction_verb_0interp(lean_interpreter_value* stack)
{
uint8_t v_failed_310_ = stack[0].m_num;
uint8_t v_x_311_ = stack[1].m_num;
lean_object* v_res_324_;
v_res_324_ = l_Lake_JobAction_verb(v_failed_310_, v_x_311_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object* v_failed_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_failed_boxed_327_; uint8_t v_x_136__boxed_328_; lean_object* v_res_329_; 
v_failed_boxed_327_ = lean_unbox(v_failed_325_);
v_x_136__boxed_328_ = lean_unbox(v_x_326_);
v_res_329_ = l_Lake_JobAction_verb(v_failed_boxed_327_, v_x_136__boxed_328_);
return v_res_329_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__2(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__1));
v___x_334_ = l_Lake_BuildTrace_nil(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default___closed__3(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_337_ = 0;
v___x_338_ = 0;
v___x_339_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_340_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_336_);
lean_ctor_set(v___x_340_, 2, v___x_335_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*3, v___x_338_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*3 + 1, v___x_337_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*3 + 2, v___x_337_);
return v___x_340_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState_default(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
return v___x_341_;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState(void){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lake_instInhabitedJobState_default;
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object* v_a_343_, lean_object* v_b_344_){
_start:
{
lean_object* v_log_345_; uint8_t v_action_346_; uint8_t v_wantsRebuild_347_; uint8_t v_canceled_348_; lean_object* v_trace_349_; lean_object* v_buildTime_350_; lean_object* v_log_351_; uint8_t v_action_352_; uint8_t v_wantsRebuild_353_; uint8_t v_canceled_354_; lean_object* v_trace_355_; lean_object* v_buildTime_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_372_; 
v_log_345_ = lean_ctor_get(v_a_343_, 0);
lean_inc_ref(v_log_345_);
v_action_346_ = lean_ctor_get_uint8(v_a_343_, sizeof(void*)*3);
v_wantsRebuild_347_ = lean_ctor_get_uint8(v_a_343_, sizeof(void*)*3 + 1);
v_canceled_348_ = lean_ctor_get_uint8(v_a_343_, sizeof(void*)*3 + 2);
v_trace_349_ = lean_ctor_get(v_a_343_, 1);
lean_inc_ref(v_trace_349_);
v_buildTime_350_ = lean_ctor_get(v_a_343_, 2);
lean_inc(v_buildTime_350_);
lean_dec_ref(v_a_343_);
v_log_351_ = lean_ctor_get(v_b_344_, 0);
v_action_352_ = lean_ctor_get_uint8(v_b_344_, sizeof(void*)*3);
v_wantsRebuild_353_ = lean_ctor_get_uint8(v_b_344_, sizeof(void*)*3 + 1);
v_canceled_354_ = lean_ctor_get_uint8(v_b_344_, sizeof(void*)*3 + 2);
v_trace_355_ = lean_ctor_get(v_b_344_, 1);
v_buildTime_356_ = lean_ctor_get(v_b_344_, 2);
v_isSharedCheck_372_ = !lean_is_exclusive(v_b_344_);
if (v_isSharedCheck_372_ == 0)
{
v___x_358_ = v_b_344_;
v_isShared_359_ = v_isSharedCheck_372_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_buildTime_356_);
lean_inc(v_trace_355_);
lean_inc(v_log_351_);
lean_dec(v_b_344_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_372_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; uint8_t v___x_361_; uint8_t v___y_363_; uint8_t v___y_364_; uint8_t v___y_371_; 
v___x_360_ = l_Array_append___redArg(v_log_345_, v_log_351_);
lean_dec_ref(v_log_351_);
v___x_361_ = l_Lake_JobAction_merge(v_action_346_, v_action_352_);
if (v_wantsRebuild_347_ == 0)
{
v___y_371_ = v_wantsRebuild_353_;
goto v___jp_370_;
}
else
{
v___y_371_ = v_wantsRebuild_347_;
goto v___jp_370_;
}
v___jp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = l_Lake_BuildTrace_mix(v_trace_349_, v_trace_355_);
v___x_366_ = lean_nat_add(v_buildTime_350_, v_buildTime_356_);
lean_dec(v_buildTime_356_);
lean_dec(v_buildTime_350_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 2, v___x_366_);
lean_ctor_set(v___x_358_, 1, v___x_365_);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_368_ = v___x_358_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*3, v___x_361_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*3 + 1, v___y_363_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*3 + 2, v___y_364_);
return v___x_368_;
}
}
v___jp_370_:
{
if (v_canceled_348_ == 0)
{
v___y_363_ = v___y_371_;
v___y_364_ = v_canceled_354_;
goto v___jp_362_;
}
else
{
v___y_363_ = v___y_371_;
v___y_364_ = v_canceled_348_;
goto v___jp_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object* v_f_373_, lean_object* v_s_374_){
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
v___x_384_ = lean_apply_1(v_f_373_, v_log_375_);
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
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object* v_e_389_, lean_object* v_s_390_){
_start:
{
lean_object* v_log_391_; uint8_t v_action_392_; uint8_t v_wantsRebuild_393_; uint8_t v_canceled_394_; lean_object* v_trace_395_; lean_object* v_buildTime_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_log_391_ = lean_ctor_get(v_s_390_, 0);
v_action_392_ = lean_ctor_get_uint8(v_s_390_, sizeof(void*)*3);
v_wantsRebuild_393_ = lean_ctor_get_uint8(v_s_390_, sizeof(void*)*3 + 1);
v_canceled_394_ = lean_ctor_get_uint8(v_s_390_, sizeof(void*)*3 + 2);
v_trace_395_ = lean_ctor_get(v_s_390_, 1);
v_buildTime_396_ = lean_ctor_get(v_s_390_, 2);
v_isSharedCheck_404_ = !lean_is_exclusive(v_s_390_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v_s_390_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_buildTime_396_);
lean_inc(v_trace_395_);
lean_inc(v_log_391_);
lean_dec(v_s_390_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_array_push(v_log_391_, v_e_389_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_trace_395_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_buildTime_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*3, v_action_392_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*3 + 1, v_wantsRebuild_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*3 + 2, v_canceled_394_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object* v_log_405_, lean_object* v_self_406_){
_start:
{
if (lean_obj_tag(v_self_406_) == 0)
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_429_; 
v_a_407_ = lean_ctor_get(v_self_406_, 1);
v_a_408_ = lean_ctor_get(v_self_406_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_self_406_);
if (v_isSharedCheck_429_ == 0)
{
v___x_410_ = v_self_406_;
v_isShared_411_ = v_isSharedCheck_429_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_407_);
lean_inc(v_a_408_);
lean_dec(v_self_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_429_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_log_412_; uint8_t v_action_413_; uint8_t v_wantsRebuild_414_; uint8_t v_canceled_415_; lean_object* v_trace_416_; lean_object* v_buildTime_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_428_; 
v_log_412_ = lean_ctor_get(v_a_407_, 0);
v_action_413_ = lean_ctor_get_uint8(v_a_407_, sizeof(void*)*3);
v_wantsRebuild_414_ = lean_ctor_get_uint8(v_a_407_, sizeof(void*)*3 + 1);
v_canceled_415_ = lean_ctor_get_uint8(v_a_407_, sizeof(void*)*3 + 2);
v_trace_416_ = lean_ctor_get(v_a_407_, 1);
v_buildTime_417_ = lean_ctor_get(v_a_407_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_428_ == 0)
{
v___x_419_ = v_a_407_;
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_buildTime_417_);
lean_inc(v_trace_416_);
lean_inc(v_log_412_);
lean_dec(v_a_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = l_Array_append___redArg(v_log_405_, v_log_412_);
lean_dec_ref(v_log_412_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_trace_416_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_buildTime_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3, v_action_413_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 1, v_wantsRebuild_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 2, v_canceled_415_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v___x_423_);
v___x_425_ = v___x_410_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_408_);
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
else
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_454_; 
v_a_430_ = lean_ctor_get(v_self_406_, 1);
v_a_431_ = lean_ctor_get(v_self_406_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_self_406_);
if (v_isSharedCheck_454_ == 0)
{
v___x_433_ = v_self_406_;
v_isShared_434_ = v_isSharedCheck_454_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_430_);
lean_inc(v_a_431_);
lean_dec(v_self_406_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_454_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_log_435_; uint8_t v_action_436_; uint8_t v_wantsRebuild_437_; uint8_t v_canceled_438_; lean_object* v_trace_439_; lean_object* v_buildTime_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_453_; 
v_log_435_ = lean_ctor_get(v_a_430_, 0);
v_action_436_ = lean_ctor_get_uint8(v_a_430_, sizeof(void*)*3);
v_wantsRebuild_437_ = lean_ctor_get_uint8(v_a_430_, sizeof(void*)*3 + 1);
v_canceled_438_ = lean_ctor_get_uint8(v_a_430_, sizeof(void*)*3 + 2);
v_trace_439_ = lean_ctor_get(v_a_430_, 1);
v_buildTime_440_ = lean_ctor_get(v_a_430_, 2);
v_isSharedCheck_453_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_453_ == 0)
{
v___x_442_ = v_a_430_;
v_isShared_443_ = v_isSharedCheck_453_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_buildTime_440_);
lean_inc(v_trace_439_);
lean_inc(v_log_435_);
lean_dec(v_a_430_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_453_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_444_ = lean_array_get_size(v_log_405_);
v___x_445_ = lean_nat_add(v___x_444_, v_a_431_);
lean_dec(v_a_431_);
v___x_446_ = l_Array_append___redArg(v_log_405_, v_log_435_);
lean_dec_ref(v_log_435_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_446_);
v___x_448_ = v___x_442_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_trace_439_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_buildTime_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*3, v_action_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*3 + 1, v_wantsRebuild_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*3 + 2, v_canceled_438_);
v___x_448_ = v_reuseFailAlloc_452_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_448_);
lean_ctor_set(v___x_433_, 0, v___x_445_);
v___x_450_ = v___x_433_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object* v_00_u03b1_455_, lean_object* v_log_456_, lean_object* v_self_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lake_JobResult_prependLog___redArg(v_log_456_, v_self_457_);
return v___x_458_;
}
}
uint8_t l_Lake_JobResult_isCanceled___redArg(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
else
{
lean_object* v_a_461_; uint8_t v_canceled_462_; 
v_a_461_ = lean_ctor_get(v_x_459_, 1);
v_canceled_462_ = lean_ctor_get_uint8(v_a_461_, sizeof(void*)*3 + 2);
return v_canceled_462_;
}
}
}
LEAN_EXPORT void l_Lake_JobResult_isCanceled___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_459_ = stack[0].m_obj;
uint8_t v_res_463_;
v_res_463_ = l_Lake_JobResult_isCanceled___redArg(v_x_459_);
stack->m_num = v_res_463_;
}
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___redArg___boxed(lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lake_JobResult_isCanceled___redArg(v_x_464_);
lean_dec_ref(v_x_464_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
uint8_t l_Lake_JobResult_isCanceled(lean_object* v_00_u03b1_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
else
{
lean_object* v_a_470_; uint8_t v_canceled_471_; 
v_a_470_ = lean_ctor_get(v_x_468_, 1);
v_canceled_471_ = lean_ctor_get_uint8(v_a_470_, sizeof(void*)*3 + 2);
return v_canceled_471_;
}
}
}
LEAN_EXPORT void l_Lake_JobResult_isCanceled_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_468_ = stack[1].m_obj;
uint8_t v_res_472_;
v_res_472_ = l_Lake_JobResult_isCanceled(lean_box(0), v_x_468_);
stack->m_num = v_res_472_;
}
LEAN_EXPORT lean_object* l_Lake_JobResult_isCanceled___boxed(lean_object* v_00_u03b1_473_, lean_object* v_x_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Lake_JobResult_isCanceled(v_00_u03b1_473_, v_x_474_);
lean_dec_ref(v_x_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__0(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = l_Lake_instInhabitedJobState_default;
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__1(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__0, &l_Lake_instInhabitedJob___redArg___closed__0_once, _init_l_Lake_instInhabitedJob___redArg___closed__0);
v___x_481_ = lean_task_pure(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___redArg___closed__3(void){
_start:
{
uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = 0;
v___x_484_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_485_ = lean_box(0);
v___x_486_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__1, &l_Lake_instInhabitedJob___redArg___closed__1_once, _init_l_Lake_instInhabitedJob___redArg___closed__1);
v___x_487_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*3, v___x_483_);
return v___x_487_;
}
}
lean_object* l_Lake_instInhabitedJob___redArg(){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = lean_obj_once(&l_Lake_instInhabitedJob___redArg___closed__3, &l_Lake_instInhabitedJob___redArg___closed__3_once, _init_l_Lake_instInhabitedJob___redArg___closed__3);
return v___x_489_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_490_;
v_res_490_ = l_Lake_instInhabitedJob___redArg();
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob___redArg___boxed(lean_object* v___dummy_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lake_instInhabitedJob___redArg();
return v_res_492_;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__0(void){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lake_instInhabitedJob___redArg();
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* v_00_u03b1_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lake_instInhabitedJob___closed__0, &l_Lake_instInhabitedJob___closed__0_once, _init_l_Lake_instInhabitedJob___closed__0);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* v_self_496_){
_start:
{
lean_inc_ref(v_self_496_);
return v_self_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* v_self_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lake_Job_cast___redArg(v_self_497_);
lean_dec_ref(v_self_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* v_00_u03b1_499_, lean_object* v_self_500_, lean_object* v_h_501_){
_start:
{
lean_inc_ref(v_self_500_);
return v_self_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* v_00_u03b1_502_, lean_object* v_self_503_, lean_object* v_h_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lake_Job_cast(v_00_u03b1_502_, v_self_503_, v_h_504_);
lean_dec_ref(v_self_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* v_inst_506_, lean_object* v_task_507_, lean_object* v_caption_508_){
_start:
{
uint8_t v___x_509_; lean_object* v___x_510_; 
v___x_509_ = 0;
v___x_510_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_510_, 0, v_task_507_);
lean_ctor_set(v___x_510_, 1, v_inst_506_);
lean_ctor_set(v___x_510_, 2, v_caption_508_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*3, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* v_00_u03b1_511_, lean_object* v_inst_512_, lean_object* v_task_513_, lean_object* v_caption_514_){
_start:
{
uint8_t v___x_515_; lean_object* v___x_516_; 
v___x_515_ = 0;
v___x_516_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_516_, 0, v_task_513_);
lean_ctor_set(v___x_516_, 1, v_inst_512_);
lean_ctor_set(v___x_516_, 2, v_caption_514_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*3, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* v_inst_517_, lean_object* v_log_518_, lean_object* v_caption_519_){
_start:
{
lean_object* v___x_520_; uint8_t v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = 0;
v___x_522_ = 0;
v___x_523_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_524_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_524_, 0, v_log_518_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_ctor_set(v___x_524_, 2, v___x_520_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*3, v___x_521_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*3 + 1, v___x_522_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*3 + 2, v___x_522_);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_520_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_task_pure(v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_inst_517_);
lean_ctor_set(v___x_527_, 2, v_caption_519_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*3, v___x_522_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* v_00_u03b1_528_, lean_object* v_inst_529_, lean_object* v_log_530_, lean_object* v_caption_531_){
_start:
{
lean_object* v___x_532_; uint8_t v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = 0;
v___x_534_ = 0;
v___x_535_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_536_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_536_, 0, v_log_530_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_ctor_set(v___x_536_, 2, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*3, v___x_533_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*3 + 1, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*3 + 2, v___x_534_);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_532_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_task_pure(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_inst_529_);
lean_ctor_set(v___x_539_, 2, v_caption_531_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*3, v___x_534_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* v_kind_540_, lean_object* v_a_541_, lean_object* v_log_542_, lean_object* v_caption_543_){
_start:
{
uint8_t v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_544_ = 0;
v___x_545_ = 0;
v___x_546_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_548_, 0, v_log_542_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3, v___x_544_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 1, v___x_545_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 2, v___x_545_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_541_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_task_pure(v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_kind_540_);
lean_ctor_set(v___x_551_, 2, v_caption_543_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*3, v___x_545_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* v_00_u03b1_552_, lean_object* v_kind_553_, lean_object* v_a_554_, lean_object* v_log_555_, lean_object* v_caption_556_){
_start:
{
uint8_t v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_557_ = 0;
v___x_558_ = 0;
v___x_559_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_561_, 0, v_log_555_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_560_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*3, v___x_557_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*3 + 1, v___x_558_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*3 + 2, v___x_558_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_a_554_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = lean_task_pure(v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_kind_553_);
lean_ctor_set(v___x_564_, 2, v_caption_556_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3, v___x_558_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* v_00_u03b1_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_567_ = lean_box(0);
v___x_568_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_569_ = 0;
v___x_570_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__3, &l_Lake_instInhabitedJobState_default___closed__3_once, _init_l_Lake_instInhabitedJobState_default___closed__3);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_a_566_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_task_pure(v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_567_);
lean_ctor_set(v___x_573_, 2, v___x_568_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*3, v___x_569_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* v_a_576_, lean_object* v_caption_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_581_ = 0;
v___x_582_ = 0;
v___x_583_ = l_Lake_BuildTrace_nil(v_caption_577_);
v___x_584_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_584_, 0, v___x_580_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
lean_ctor_set(v___x_584_, 2, v___x_579_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*3, v___x_581_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*3 + 1, v___x_582_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*3 + 2, v___x_582_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_576_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_task_pure(v___x_585_);
v___x_587_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_588_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_578_);
lean_ctor_set(v___x_588_, 2, v___x_587_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*3, v___x_582_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* v_00_u03b1_589_, lean_object* v_a_590_, lean_object* v_caption_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_592_ = lean_box(0);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_595_ = 0;
v___x_596_ = 0;
v___x_597_ = l_Lake_BuildTrace_nil(v_caption_591_);
v___x_598_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_598_, 0, v___x_594_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_ctor_set(v___x_598_, 2, v___x_593_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*3, v___x_595_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*3 + 1, v___x_596_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*3 + 2, v___x_596_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_a_590_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_task_pure(v___x_599_);
v___x_601_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_592_);
lean_ctor_set(v___x_602_, 2, v___x_601_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*3, v___x_596_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* v_log_603_, lean_object* v_caption_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_605_ = l_Lake_instDataKindUnit;
v___x_606_ = lean_box(0);
v___x_607_ = 0;
v___x_608_ = 0;
v___x_609_ = lean_obj_once(&l_Lake_instInhabitedJobState_default___closed__2, &l_Lake_instInhabitedJobState_default___closed__2_once, _init_l_Lake_instInhabitedJobState_default___closed__2);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_611_, 0, v_log_603_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_610_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*3, v___x_607_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*3 + 1, v___x_608_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*3 + 2, v___x_608_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_606_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_task_pure(v___x_612_);
v___x_614_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_605_);
lean_ctor_set(v___x_614_, 2, v_caption_604_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*3, v___x_608_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* v_traceCaption_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_616_ = lean_box(0);
v___x_617_ = lean_box(0);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = ((lean_object*)(l_Lake_instInhabitedJobState_default___closed__0));
v___x_620_ = 0;
v___x_621_ = 0;
v___x_622_ = l_Lake_BuildTrace_nil(v_traceCaption_615_);
v___x_623_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_623_, 0, v___x_619_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
lean_ctor_set(v___x_623_, 2, v___x_618_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*3, v___x_620_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*3 + 1, v___x_621_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*3 + 2, v___x_621_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_616_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_task_pure(v___x_624_);
v___x_626_ = ((lean_object*)(l_Lake_instInhabitedJob___redArg___closed__2));
v___x_627_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_617_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*3, v___x_621_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* v_job_628_){
_start:
{
lean_object* v_task_629_; lean_object* v___x_630_; lean_object* v_a_631_; lean_object* v_trace_632_; 
v_task_629_ = lean_ctor_get(v_job_628_, 0);
lean_inc_ref(v_task_629_);
lean_dec_ref(v_job_628_);
v___x_630_ = lean_task_get_own(v_task_629_);
v_a_631_ = lean_ctor_get(v___x_630_, 1);
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v_trace_632_ = lean_ctor_get(v_a_631_, 1);
lean_inc_ref(v_trace_632_);
lean_dec(v_a_631_);
return v_trace_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* v_00_u03b1_633_, lean_object* v_job_634_){
_start:
{
lean_object* v_task_635_; lean_object* v___x_636_; lean_object* v_a_637_; lean_object* v_trace_638_; 
v_task_635_ = lean_ctor_get(v_job_634_, 0);
lean_inc_ref(v_task_635_);
lean_dec_ref(v_job_634_);
v___x_636_ = lean_task_get_own(v_task_635_);
v_a_637_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v_trace_638_ = lean_ctor_get(v_a_637_, 1);
lean_inc_ref(v_trace_638_);
lean_dec(v_a_637_);
return v_trace_638_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* v_caption_639_, lean_object* v_job_640_){
_start:
{
lean_object* v_task_641_; lean_object* v_kind_642_; uint8_t v_optional_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_task_641_ = lean_ctor_get(v_job_640_, 0);
v_kind_642_ = lean_ctor_get(v_job_640_, 1);
v_optional_643_ = lean_ctor_get_uint8(v_job_640_, sizeof(void*)*3);
v_isSharedCheck_650_ = !lean_is_exclusive(v_job_640_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_job_640_, 2);
lean_dec(v_unused_651_);
v___x_645_ = v_job_640_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_kind_642_);
lean_inc(v_task_641_);
lean_dec(v_job_640_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 2, v_caption_639_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_task_641_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_kind_642_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_caption_639_);
lean_ctor_set_uint8(v_reuseFailAlloc_649_, sizeof(void*)*3, v_optional_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* v_00_u03b1_652_, lean_object* v_caption_653_, lean_object* v_job_654_){
_start:
{
lean_object* v_task_655_; lean_object* v_kind_656_; uint8_t v_optional_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
v_task_655_ = lean_ctor_get(v_job_654_, 0);
v_kind_656_ = lean_ctor_get(v_job_654_, 1);
v_optional_657_ = lean_ctor_get_uint8(v_job_654_, sizeof(void*)*3);
v_isSharedCheck_664_ = !lean_is_exclusive(v_job_654_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_job_654_, 2);
lean_dec(v_unused_665_);
v___x_659_ = v_job_654_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_kind_656_);
lean_inc(v_task_655_);
lean_dec(v_job_654_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 2, v_caption_653_);
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_task_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_kind_656_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_caption_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_663_, sizeof(void*)*3, v_optional_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* v_caption_666_, lean_object* v_job_667_){
_start:
{
lean_object* v_task_668_; lean_object* v_kind_669_; lean_object* v_caption_670_; uint8_t v_optional_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_task_668_ = lean_ctor_get(v_job_667_, 0);
v_kind_669_ = lean_ctor_get(v_job_667_, 1);
v_caption_670_ = lean_ctor_get(v_job_667_, 2);
v_optional_671_ = lean_ctor_get_uint8(v_job_667_, sizeof(void*)*3);
v___x_672_ = lean_string_utf8_byte_size(v_caption_670_);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_nat_dec_eq(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec_ref(v_caption_666_);
return v_job_667_;
}
else
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_inc(v_kind_669_);
lean_inc_ref(v_task_668_);
v_isSharedCheck_681_ = !lean_is_exclusive(v_job_667_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; 
v_unused_682_ = lean_ctor_get(v_job_667_, 2);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_job_667_, 1);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_job_667_, 0);
lean_dec(v_unused_684_);
v___x_676_ = v_job_667_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_dec(v_job_667_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 2, v_caption_666_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_task_668_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_kind_669_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_caption_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3, v_optional_671_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* v_00_u03b1_685_, lean_object* v_caption_686_, lean_object* v_job_687_){
_start:
{
lean_object* v_task_688_; lean_object* v_kind_689_; lean_object* v_caption_690_; uint8_t v_optional_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_task_688_ = lean_ctor_get(v_job_687_, 0);
v_kind_689_ = lean_ctor_get(v_job_687_, 1);
v_caption_690_ = lean_ctor_get(v_job_687_, 2);
v_optional_691_ = lean_ctor_get_uint8(v_job_687_, sizeof(void*)*3);
v___x_692_ = lean_string_utf8_byte_size(v_caption_690_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_caption_686_);
return v_job_687_;
}
else
{
lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_inc(v_kind_689_);
lean_inc_ref(v_task_688_);
v_isSharedCheck_701_ = !lean_is_exclusive(v_job_687_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_702_ = lean_ctor_get(v_job_687_, 2);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_job_687_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_job_687_, 0);
lean_dec(v_unused_704_);
v___x_696_ = v_job_687_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_dec(v_job_687_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 2, v_caption_686_);
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_task_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_kind_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_caption_686_);
lean_ctor_set_uint8(v_reuseFailAlloc_700_, sizeof(void*)*3, v_optional_691_);
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
}
lean_object* l_Lake_Job_mapResult___redArg(lean_object* v_inst_705_, lean_object* v_f_706_, lean_object* v_self_707_, lean_object* v_prio_708_, uint8_t v_sync_709_){
_start:
{
lean_object* v_task_710_; lean_object* v_caption_711_; uint8_t v_optional_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v_task_710_ = lean_ctor_get(v_self_707_, 0);
v_caption_711_ = lean_ctor_get(v_self_707_, 2);
v_optional_712_ = lean_ctor_get_uint8(v_self_707_, sizeof(void*)*3);
v_isSharedCheck_720_ = !lean_is_exclusive(v_self_707_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_self_707_, 1);
lean_dec(v_unused_721_);
v___x_714_ = v_self_707_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_caption_711_);
lean_inc(v_task_710_);
lean_dec(v_self_707_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_task_map(v_f_706_, v_task_710_, v_prio_708_, v_sync_709_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_inst_705_);
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_inst_705_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_caption_711_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*3, v_optional_712_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_mapResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_705_ = stack[0].m_obj;
lean_object* v_f_706_ = stack[1].m_obj;
lean_object* v_self_707_ = stack[2].m_obj;
lean_object* v_prio_708_ = stack[3].m_obj;
uint8_t v_sync_709_ = stack[4].m_num;
lean_object* v_res_722_;
v_res_722_ = l_Lake_Job_mapResult___redArg(v_inst_705_, v_f_706_, v_self_707_, v_prio_708_, v_sync_709_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* v_inst_723_, lean_object* v_f_724_, lean_object* v_self_725_, lean_object* v_prio_726_, lean_object* v_sync_727_){
_start:
{
uint8_t v_sync_boxed_728_; lean_object* v_res_729_; 
v_sync_boxed_728_ = lean_unbox(v_sync_727_);
v_res_729_ = l_Lake_Job_mapResult___redArg(v_inst_723_, v_f_724_, v_self_725_, v_prio_726_, v_sync_boxed_728_);
return v_res_729_;
}
}
lean_object* l_Lake_Job_mapResult(lean_object* v_00_u03b2_730_, lean_object* v_00_u03b1_731_, lean_object* v_inst_732_, lean_object* v_f_733_, lean_object* v_self_734_, lean_object* v_prio_735_, uint8_t v_sync_736_){
_start:
{
lean_object* v_task_737_; lean_object* v_caption_738_; uint8_t v_optional_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
v_task_737_ = lean_ctor_get(v_self_734_, 0);
v_caption_738_ = lean_ctor_get(v_self_734_, 2);
v_optional_739_ = lean_ctor_get_uint8(v_self_734_, sizeof(void*)*3);
v_isSharedCheck_747_ = !lean_is_exclusive(v_self_734_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_self_734_, 1);
lean_dec(v_unused_748_);
v___x_741_ = v_self_734_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_caption_738_);
lean_inc(v_task_737_);
lean_dec(v_self_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_task_map(v_f_733_, v_task_737_, v_prio_735_, v_sync_736_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v_inst_732_);
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_inst_732_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_caption_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, sizeof(void*)*3, v_optional_739_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_mapResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_732_ = stack[2].m_obj;
lean_object* v_f_733_ = stack[3].m_obj;
lean_object* v_self_734_ = stack[4].m_obj;
lean_object* v_prio_735_ = stack[5].m_obj;
uint8_t v_sync_736_ = stack[6].m_num;
lean_object* v_res_749_;
v_res_749_ = l_Lake_Job_mapResult(lean_box(0), lean_box(0), v_inst_732_, v_f_733_, v_self_734_, v_prio_735_, v_sync_736_);
stack->m_obj
 = v_res_749_;
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* v_00_u03b2_750_, lean_object* v_00_u03b1_751_, lean_object* v_inst_752_, lean_object* v_f_753_, lean_object* v_self_754_, lean_object* v_prio_755_, lean_object* v_sync_756_){
_start:
{
uint8_t v_sync_boxed_757_; lean_object* v_res_758_; 
v_sync_boxed_757_ = lean_unbox(v_sync_756_);
v_res_758_ = l_Lake_Job_mapResult(v_00_u03b2_750_, v_00_u03b1_751_, v_inst_752_, v_f_753_, v_self_754_, v_prio_755_, v_sync_boxed_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* v_f_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_761_ = lean_ctor_get(v_x_760_, 0);
lean_inc(v_a_761_);
v_a_762_ = lean_ctor_get(v_x_760_, 1);
lean_inc(v_a_762_);
lean_dec_ref_known(v_x_760_, 2);
v___x_763_ = lean_apply_2(v_f_759_, v_a_761_, v_a_762_);
return v___x_763_;
}
else
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_f_759_);
v_a_764_ = lean_ctor_get(v_x_760_, 0);
v_a_765_ = lean_ctor_get(v_x_760_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v_x_760_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_inc(v_a_764_);
lean_dec(v_x_760_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_764_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
lean_object* l_Lake_Job_mapOk___redArg(lean_object* v_inst_773_, lean_object* v_f_774_, lean_object* v_self_775_, lean_object* v_prio_776_, uint8_t v_sync_777_){
_start:
{
lean_object* v_task_778_; lean_object* v_caption_779_; uint8_t v_optional_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_789_; 
v_task_778_ = lean_ctor_get(v_self_775_, 0);
v_caption_779_ = lean_ctor_get(v_self_775_, 2);
v_optional_780_ = lean_ctor_get_uint8(v_self_775_, sizeof(void*)*3);
v_isSharedCheck_789_ = !lean_is_exclusive(v_self_775_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_self_775_, 1);
lean_dec(v_unused_790_);
v___x_782_ = v_self_775_;
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_caption_779_);
lean_inc(v_task_778_);
lean_dec(v_self_775_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___f_784_ = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(v___f_784_, 0, v_f_774_);
v___x_785_ = lean_task_map(v___f_784_, v_task_778_, v_prio_776_, v_sync_777_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_inst_773_);
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_inst_773_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_caption_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_788_, sizeof(void*)*3, v_optional_780_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_mapOk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_773_ = stack[0].m_obj;
lean_object* v_f_774_ = stack[1].m_obj;
lean_object* v_self_775_ = stack[2].m_obj;
lean_object* v_prio_776_ = stack[3].m_obj;
uint8_t v_sync_777_ = stack[4].m_num;
lean_object* v_res_791_;
v_res_791_ = l_Lake_Job_mapOk___redArg(v_inst_773_, v_f_774_, v_self_775_, v_prio_776_, v_sync_777_);
stack->m_obj
 = v_res_791_;
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
lean_object* l_Lake_Job_mapOk(lean_object* v_00_u03b2_799_, lean_object* v_00_u03b1_800_, lean_object* v_inst_801_, lean_object* v_f_802_, lean_object* v_self_803_, lean_object* v_prio_804_, uint8_t v_sync_805_){
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
LEAN_EXPORT void l_Lake_Job_mapOk_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_801_ = stack[2].m_obj;
lean_object* v_f_802_ = stack[3].m_obj;
lean_object* v_self_803_ = stack[4].m_obj;
lean_object* v_prio_804_ = stack[5].m_obj;
uint8_t v_sync_805_ = stack[6].m_num;
lean_object* v_res_819_;
v_res_819_ = l_Lake_Job_mapOk(lean_box(0), lean_box(0), v_inst_801_, v_f_802_, v_self_803_, v_prio_804_, v_sync_805_);
stack->m_obj
 = v_res_819_;
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* v_00_u03b2_820_, lean_object* v_00_u03b1_821_, lean_object* v_inst_822_, lean_object* v_f_823_, lean_object* v_self_824_, lean_object* v_prio_825_, lean_object* v_sync_826_){
_start:
{
uint8_t v_sync_boxed_827_; lean_object* v_res_828_; 
v_sync_boxed_827_ = lean_unbox(v_sync_826_);
v_res_828_ = l_Lake_Job_mapOk(v_00_u03b2_820_, v_00_u03b1_821_, v_inst_822_, v_f_823_, v_self_824_, v_prio_825_, v_sync_boxed_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* v_f_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_840_; 
v_a_831_ = lean_ctor_get(v_x_830_, 0);
v_a_832_ = lean_ctor_get(v_x_830_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_840_ == 0)
{
v___x_834_ = v_x_830_;
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_inc(v_a_831_);
lean_dec(v_x_830_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_apply_1(v_f_829_, v_a_831_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_a_832_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v_a_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_f_829_);
v_a_841_ = lean_ctor_get(v_x_830_, 0);
v_a_842_ = lean_ctor_get(v_x_830_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v_x_830_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_inc(v_a_841_);
lean_dec(v_x_830_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_841_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
lean_object* l_Lake_Job_map___redArg(lean_object* v_inst_850_, lean_object* v_f_851_, lean_object* v_self_852_, lean_object* v_prio_853_, uint8_t v_sync_854_){
_start:
{
lean_object* v_task_855_; lean_object* v_caption_856_; uint8_t v_optional_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_866_; 
v_task_855_ = lean_ctor_get(v_self_852_, 0);
v_caption_856_ = lean_ctor_get(v_self_852_, 2);
v_optional_857_ = lean_ctor_get_uint8(v_self_852_, sizeof(void*)*3);
v_isSharedCheck_866_ = !lean_is_exclusive(v_self_852_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_self_852_, 1);
lean_dec(v_unused_867_);
v___x_859_ = v_self_852_;
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_caption_856_);
lean_inc(v_task_855_);
lean_dec(v_self_852_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___f_861_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_861_, 0, v_f_851_);
v___x_862_ = lean_task_map(v___f_861_, v_task_855_, v_prio_853_, v_sync_854_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v_inst_850_);
lean_ctor_set(v___x_859_, 0, v___x_862_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_inst_850_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_caption_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_865_, sizeof(void*)*3, v_optional_857_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_850_ = stack[0].m_obj;
lean_object* v_f_851_ = stack[1].m_obj;
lean_object* v_self_852_ = stack[2].m_obj;
lean_object* v_prio_853_ = stack[3].m_obj;
uint8_t v_sync_854_ = stack[4].m_num;
lean_object* v_res_868_;
v_res_868_ = l_Lake_Job_map___redArg(v_inst_850_, v_f_851_, v_self_852_, v_prio_853_, v_sync_854_);
stack->m_obj
 = v_res_868_;
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* v_inst_869_, lean_object* v_f_870_, lean_object* v_self_871_, lean_object* v_prio_872_, lean_object* v_sync_873_){
_start:
{
uint8_t v_sync_boxed_874_; lean_object* v_res_875_; 
v_sync_boxed_874_ = lean_unbox(v_sync_873_);
v_res_875_ = l_Lake_Job_map___redArg(v_inst_869_, v_f_870_, v_self_871_, v_prio_872_, v_sync_boxed_874_);
return v_res_875_;
}
}
lean_object* l_Lake_Job_map(lean_object* v_00_u03b2_876_, lean_object* v_00_u03b1_877_, lean_object* v_inst_878_, lean_object* v_f_879_, lean_object* v_self_880_, lean_object* v_prio_881_, uint8_t v_sync_882_){
_start:
{
lean_object* v_task_883_; lean_object* v_caption_884_; uint8_t v_optional_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
v_task_883_ = lean_ctor_get(v_self_880_, 0);
v_caption_884_ = lean_ctor_get(v_self_880_, 2);
v_optional_885_ = lean_ctor_get_uint8(v_self_880_, sizeof(void*)*3);
v_isSharedCheck_894_ = !lean_is_exclusive(v_self_880_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_self_880_, 1);
lean_dec(v_unused_895_);
v___x_887_ = v_self_880_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_caption_884_);
lean_inc(v_task_883_);
lean_dec(v_self_880_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___f_889_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_889_, 0, v_f_879_);
v___x_890_ = lean_task_map(v___f_889_, v_task_883_, v_prio_881_, v_sync_882_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_inst_878_);
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_inst_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_caption_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*3, v_optional_885_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_878_ = stack[2].m_obj;
lean_object* v_f_879_ = stack[3].m_obj;
lean_object* v_self_880_ = stack[4].m_obj;
lean_object* v_prio_881_ = stack[5].m_obj;
uint8_t v_sync_882_ = stack[6].m_num;
lean_object* v_res_896_;
v_res_896_ = l_Lake_Job_map(lean_box(0), lean_box(0), v_inst_878_, v_f_879_, v_self_880_, v_prio_881_, v_sync_882_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* v_00_u03b2_897_, lean_object* v_00_u03b1_898_, lean_object* v_inst_899_, lean_object* v_f_900_, lean_object* v_self_901_, lean_object* v_prio_902_, lean_object* v_sync_903_){
_start:
{
uint8_t v_sync_boxed_904_; lean_object* v_res_905_; 
v_sync_boxed_904_ = lean_unbox(v_sync_903_);
v_res_905_ = l_Lake_Job_map(v_00_u03b2_897_, v_00_u03b1_898_, v_inst_899_, v_f_900_, v_self_901_, v_prio_902_, v_sync_boxed_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_f_908_, lean_object* v_self_909_){
_start:
{
lean_object* v_task_910_; lean_object* v_caption_911_; uint8_t v_optional_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_924_; 
v_task_910_ = lean_ctor_get(v_self_909_, 0);
v_caption_911_ = lean_ctor_get(v_self_909_, 2);
v_optional_912_ = lean_ctor_get_uint8(v_self_909_, sizeof(void*)*3);
v_isSharedCheck_924_ = !lean_is_exclusive(v_self_909_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v_self_909_, 1);
lean_dec(v_unused_925_);
v___x_914_ = v_self_909_;
v_isShared_915_ = v_isSharedCheck_924_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_caption_911_);
lean_inc(v_task_910_);
lean_dec(v_self_909_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_924_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___f_916_ = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_916_, 0, v_f_908_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = 0;
v___x_920_ = lean_task_map(v___f_916_, v_task_910_, v___x_918_, v___x_919_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_917_);
lean_ctor_set(v___x_914_, 0, v___x_920_);
v___x_922_ = v___x_914_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_caption_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_923_, sizeof(void*)*3, v_optional_912_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* v___f_926_, lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_931_, 0, lean_box(0));
lean_closure_set(v___x_931_, 1, lean_box(0));
lean_closure_set(v___x_931_, 2, v___y_929_);
v___x_932_ = lean_apply_4(v___f_926_, lean_box(0), lean_box(0), v___x_931_, v___y_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* v_self_940_){
_start:
{
lean_inc_ref(v_self_940_);
return v_self_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* v_self_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_941_);
lean_dec_ref(v_self_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* v_00_u03b1_943_, lean_object* v_self_944_){
_start:
{
lean_inc_ref(v_self_944_);
return v_self_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* v_00_u03b1_945_, lean_object* v_self_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(v_00_u03b1_945_, v_self_946_);
lean_dec_ref(v_self_946_);
return v_res_947_;
}
}
lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg(){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0));
return v___x_950_;
}
}
LEAN_EXPORT void l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_951_;
v_res_951_ = l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg();
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___boxed(lean_object* v___dummy_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg();
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* v_00_u03b1_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Lake_instCoeOutJobTaskOpaqueJobTask___redArg___closed__0));
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* v_job_956_){
_start:
{
lean_object* v_task_957_; lean_object* v_caption_958_; uint8_t v_optional_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_967_; 
v_task_957_ = lean_ctor_get(v_job_956_, 0);
v_caption_958_ = lean_ctor_get(v_job_956_, 2);
v_optional_959_ = lean_ctor_get_uint8(v_job_956_, sizeof(void*)*3);
v_isSharedCheck_967_ = !lean_is_exclusive(v_job_956_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_job_956_, 1);
lean_dec(v_unused_968_);
v___x_961_ = v_job_956_;
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_caption_958_);
lean_inc(v_task_957_);
lean_dec(v_job_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = lean_box(0);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_task_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_caption_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_optional_959_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* v_00_u03b1_969_, lean_object* v_job_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lake_Job_toOpaque___redArg(v_job_970_);
return v___x_971_;
}
}
lean_object* l_Lake_instCoeOutJobOpaqueJob___redArg(){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l_Lake_instCoeOutJobOpaqueJob___redArg___closed__0));
return v___x_974_;
}
}
LEAN_EXPORT void l_Lake_instCoeOutJobOpaqueJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_975_;
v_res_975_ = l_Lake_instCoeOutJobOpaqueJob___redArg();
stack->m_obj
 = v_res_975_;
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
