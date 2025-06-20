// Lean compiler output
// Module: Lake.Build.Job.Basic
// Imports: Lake.Util.Log Lake.Util.Task Lake.Util.Opaque Lake.Build.Trace Lake.Build.Data
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
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_instInhabitedJob___closed__3;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqJobAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object*, lean_object*);
static lean_object* l_Lake_reprJobAction___closed__6____x40_Lake_Build_Job_Basic___hyg_21_;
LEAN_EXPORT uint8_t l_Lake_instMinJobAction___lam__0(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(uint8_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedJob___closed__1;
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdJobAction;
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object*, lean_object*);
static lean_object* l_Lake_JobAction_verb___closed__1;
LEAN_EXPORT uint8_t l_Lake_instMaxJobAction___lam__0(uint8_t, uint8_t);
static lean_object* l_Lake_reprJobAction___closed__4____x40_Lake_Build_Job_Basic___hyg_21_;
static lean_object* l_Lake_instOrdJobAction___closed__0;
LEAN_EXPORT lean_object* l_Lake_instMaxJobAction;
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lake_reprJobAction___closed__0____x40_Lake_Build_Job_Basic___hyg_21_;
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedJobState___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedJob___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_instPure;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
static lean_object* l_Lake_instInhabitedJobState___closed__3;
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLTJobAction;
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_instPure___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object*);
static lean_object* l_Lake_JobAction_verb___closed__2;
LEAN_EXPORT lean_object* l_Lake_instMaxJobAction___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_;
LEAN_EXPORT lean_object* l_Lake_instDecidableEqJobAction___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object*);
LEAN_EXPORT lean_object* l_Lake_reprJobAction____x40_Lake_Build_Job_Basic___hyg_21____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinJobAction;
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor;
LEAN_EXPORT lean_object* l_Lake_instMinJobAction___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object*, lean_object*);
static lean_object* l_Lake_reprJobAction___closed__5____x40_Lake_Build_Job_Basic___hyg_21_;
static lean_object* l_Lake_instInhabitedJob___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedJobAction;
LEAN_EXPORT lean_object* l_Lake_JobAction_merge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprJobAction___closed__0;
static lean_object* l_Lake_JobAction_verb___closed__4;
LEAN_EXPORT lean_object* l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx(uint8_t);
static lean_object* l_Lake_reprJobAction___closed__3____x40_Lake_Build_Job_Basic___hyg_21_;
static lean_object* l_Lake_reprJobAction___closed__1____x40_Lake_Build_Job_Basic___hyg_21_;
LEAN_EXPORT lean_object* l_Lake_instLEJobAction;
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_JobAction_verb___closed__6;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_JobAction_verb___closed__5;
static lean_object* l_Lake_reprJobAction___closed__2____x40_Lake_Build_Job_Basic___hyg_21_;
LEAN_EXPORT uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
static lean_object* l_Lake_JobAction_verb___closed__3;
LEAN_EXPORT uint8_t l_Lake_JobAction_ofNat(lean_object*);
static lean_object* l_Lake_JobAction_verb___closed__7;
static lean_object* l_Lake_instCoeOutJobOpaqueJob___closed__0;
LEAN_EXPORT lean_object* l_Lake_instReprJobAction;
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object*, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object*);
static lean_object* l_Lake_reprJobAction___closed__7____x40_Lake_Build_Job_Basic___hyg_21_;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedJobState___closed__2;
static lean_object* l_Lake_JobAction_verb___closed__0;
static lean_object* l_Lake_instInhabitedJobState___closed__1;
LEAN_EXPORT lean_object* l_Lake_reprJobAction____x40_Lake_Build_Job_Basic___hyg_21_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedJobState;
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_Job_instPure___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_JobAction_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_JobAction_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_JobAction_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_JobAction_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_JobAction_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_JobAction_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lake_instInhabitedJobAction() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__0____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.JobAction.unknown", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__1____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprJobAction___closed__0____x40_Lake_Build_Job_Basic___hyg_21_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__2____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.JobAction.replay", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__3____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprJobAction___closed__2____x40_Lake_Build_Job_Basic___hyg_21_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__4____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.JobAction.fetch", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__5____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprJobAction___closed__4____x40_Lake_Build_Job_Basic___hyg_21_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__6____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.JobAction.build", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__7____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprJobAction___closed__6____x40_Lake_Build_Job_Basic___hyg_21_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_reprJobAction____x40_Lake_Build_Job_Basic___hyg_21_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; lean_object* x_27; 
switch (x_1) {
case 0:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_;
x_3 = x_37;
goto block_10;
}
else
{
lean_object* x_38; 
x_38 = l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_;
x_3 = x_38;
goto block_10;
}
}
case 1:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_;
x_11 = x_41;
goto block_18;
}
else
{
lean_object* x_42; 
x_42 = l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_;
x_11 = x_42;
goto block_18;
}
}
case 2:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_;
x_19 = x_45;
goto block_26;
}
else
{
lean_object* x_46; 
x_46 = l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_;
x_19 = x_46;
goto block_26;
}
}
default: 
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(1024u);
x_48 = lean_nat_dec_le(x_47, x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_;
x_27 = x_49;
goto block_34;
}
else
{
lean_object* x_50; 
x_50 = l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_;
x_27 = x_50;
goto block_34;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lake_reprJobAction___closed__1____x40_Lake_Build_Job_Basic___hyg_21_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lake_reprJobAction___closed__3____x40_Lake_Build_Job_Basic___hyg_21_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = l_Lake_reprJobAction___closed__5____x40_Lake_Build_Job_Basic___hyg_21_;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = l_Repr_addAppParen(x_23, x_2);
return x_25;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = l_Lake_reprJobAction___closed__7____x40_Lake_Build_Job_Basic___hyg_21_;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = l_Repr_addAppParen(x_31, x_2);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_reprJobAction____x40_Lake_Build_Job_Basic___hyg_21____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_reprJobAction____x40_Lake_Build_Job_Basic___hyg_21_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprJobAction___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_reprJobAction____x40_Lake_Build_Job_Basic___hyg_21____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprJobAction() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprJobAction___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(3);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(2);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_JobAction_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqJobAction(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_JobAction_toCtorIdx(x_1);
x_4 = l_Lake_JobAction_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqJobAction___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqJobAction(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_box(x_2);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(2);
x_10 = lean_unbox(x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
return x_12;
}
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
case 2:
{
lean_object* x_15; 
x_15 = lean_box(x_2);
switch (lean_obj_tag(x_15)) {
case 2:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
return x_17;
}
case 3:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
default: 
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_15);
x_20 = lean_box(2);
x_21 = lean_unbox(x_20);
return x_21;
}
}
}
default: 
{
lean_object* x_22; 
x_22 = lean_box(x_2);
if (lean_obj_tag(x_22) == 3)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_22);
x_25 = lean_box(2);
x_26 = lean_unbox(x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instOrdJobAction___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instOrdJobAction() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instOrdJobAction___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instLTJobAction() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLEJobAction() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinJobAction___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(x_1, x_2);
x_4 = lean_box(x_3);
if (lean_obj_tag(x_4) == 2)
{
return x_2;
}
else
{
lean_dec(x_4);
return x_1;
}
}
}
static lean_object* _init_l_Lake_instMinJobAction() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMinJobAction___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinJobAction___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instMinJobAction___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxJobAction___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(x_1, x_2);
x_4 = lean_box(x_3);
if (lean_obj_tag(x_4) == 2)
{
return x_1;
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
static lean_object* _init_l_Lake_instMaxJobAction() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMaxJobAction___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxJobAction___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instMaxJobAction___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_JobAction_merge(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(x_1, x_2);
x_4 = lean_box(x_3);
if (lean_obj_tag(x_4) == 2)
{
return x_1;
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_merge___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_JobAction_merge(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ran", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Running", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Replayed", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Replaying", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fetched", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fetching", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Built", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_JobAction_verb___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Building", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_2) {
case 0:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = l_Lake_JobAction_verb___closed__0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lake_JobAction_verb___closed__1;
return x_4;
}
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_JobAction_verb___closed__2;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lake_JobAction_verb___closed__3;
return x_6;
}
}
case 2:
{
if (x_1 == 0)
{
lean_object* x_7; 
x_7 = l_Lake_JobAction_verb___closed__4;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lake_JobAction_verb___closed__5;
return x_8;
}
}
default: 
{
if (x_1 == 0)
{
lean_object* x_9; 
x_9 = l_Lake_JobAction_verb___closed__6;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lake_JobAction_verb___closed__7;
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobAction_verb___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_JobAction_verb(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedJobState___closed__1;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_instInhabitedJobState___closed__2;
x_2 = lean_box(0);
x_3 = l_Lake_instInhabitedJobState___closed__0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedJobState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedJobState___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Array_append___redArg(x_3, x_7);
lean_dec(x_7);
x_11 = l_Lake_JobAction_merge(x_4, x_8);
x_12 = l_Lake_BuildTrace_mix(x_5, x_9);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_10);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_11);
return x_2;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_13);
lean_dec(x_2);
x_16 = l_Array_append___redArg(x_3, x_13);
lean_dec(x_13);
x_17 = l_Lake_JobAction_merge(x_4, x_14);
x_18 = l_Lake_BuildTrace_mix(x_5, x_15);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_modifyLog(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_6);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_logEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_dec(x_2);
x_9 = lean_array_push(x_6, x_1);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Array_append___redArg(x_1, x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_8);
lean_dec(x_4);
x_11 = l_Array_append___redArg(x_1, x_8);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_9);
lean_ctor_set(x_2, 1, x_12);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_18 = x_13;
} else {
 lean_dec_ref(x_13);
 x_18 = lean_box(0);
}
x_19 = l_Array_append___redArg(x_1, x_15);
lean_dec(x_15);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 1);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_array_get_size(x_1);
x_28 = lean_nat_add(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
x_29 = l_Array_append___redArg(x_1, x_26);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_29);
lean_ctor_set(x_2, 0, x_28);
return x_2;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_31);
lean_dec(x_23);
x_34 = lean_array_get_size(x_1);
x_35 = lean_nat_add(x_34, x_30);
lean_dec(x_30);
lean_dec(x_34);
x_36 = l_Array_append___redArg(x_1, x_31);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_32);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = lean_array_get_size(x_1);
x_45 = lean_nat_add(x_44, x_39);
lean_dec(x_39);
lean_dec(x_44);
x_46 = l_Array_append___redArg(x_1, x_40);
lean_dec(x_40);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 1);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobResult_prependLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_JobResult_prependLog___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedJobState___closed__3;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedJob___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedJob___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = l_Lake_instInhabitedJob___closed__2;
x_3 = lean_box(0);
x_4 = l_Lake_instInhabitedJob___closed__1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedJob(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedJob___closed__3;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Job_cast___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Job_cast(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_ofTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_4);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = l_Lake_instInhabitedJobState___closed__2;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_task_pure(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_3);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_13);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_error(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = l_Lake_instInhabitedJobState___closed__2;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_task_pure(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_4);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_box(0);
x_6 = l_Lake_instInhabitedJobState___closed__2;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_task_pure(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_4);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_13);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_pure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_box(0);
x_7 = l_Lake_instInhabitedJobState___closed__2;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_task_pure(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_5);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
return x_13;
}
}
static lean_object* _init_l_Lake_Job_instPure___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Job_instPure___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_instInhabitedJobState___closed__2;
x_2 = lean_box(0);
x_3 = l_Lake_Job_instPure___lam__0___closed__0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instPure___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_box(0);
x_4 = l_Lake_instInhabitedJob___closed__2;
x_5 = l_Lake_Job_instPure___lam__0___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_task_pure(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_10);
return x_9;
}
}
static lean_object* _init_l_Lake_Job_instPure() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Job_instPure___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_box(0);
x_4 = l_Lake_Job_instPure___lam__0___closed__0;
x_5 = lean_box(0);
x_6 = l_Lake_BuildTrace_nil(x_2);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_task_pure(x_9);
x_11 = l_Lake_instInhabitedJob___closed__2;
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_traceRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_box(0);
x_5 = l_Lake_Job_instPure___lam__0___closed__0;
x_6 = lean_box(0);
x_7 = l_Lake_BuildTrace_nil(x_3);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_task_pure(x_10);
x_12 = l_Lake_instInhabitedJob___closed__2;
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_15);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = l_Lake_instDataKindUnit;
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = l_Lake_instInhabitedJobState___closed__2;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_task_pure(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_2);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_13);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_nil(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lake_Job_instPure___lam__0___closed__0;
x_5 = lean_box(0);
x_6 = l_Lake_BuildTrace_nil(x_1);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_task_pure(x_9);
x_11 = l_Lake_instInhabitedJob___closed__2;
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_getTrace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_task_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 2);
lean_dec(x_4);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 2);
lean_dec(x_5);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_string_utf8_byte_size(x_5);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_6);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_setCaption_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_string_utf8_byte_size(x_6);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_7);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_task_map(x_2, x_7, x_4, x_5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_task_map(x_2, x_10, x_4, x_5);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = lean_task_map(x_4, x_9, x_6, x_7);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_15 = lean_task_map(x_4, x_12, x_6, x_7);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lake_Job_mapResult___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lake_Job_mapResult(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_task_map(x_9, x_7, x_4, x_5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_task_map(x_14, x_11, x_4, x_5);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_task_map(x_11, x_9, x_6, x_7);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_16 = lean_alloc_closure((void*)(l_Lake_Job_mapOk___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_4);
x_17 = lean_task_map(x_16, x_13, x_6, x_7);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lake_Job_mapOk___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapOk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lake_Job_mapOk(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_task_map(x_9, x_7, x_4, x_5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_task_map(x_14, x_11, x_4, x_5);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_task_map(x_11, x_9, x_6, x_7);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_16 = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_4);
x_17 = lean_task_map(x_16, x_13, x_6, x_7);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lake_Job_map___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lake_Job_map(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = lean_task_map(x_8, x_6, x_10, x_12);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_17 = lean_alloc_closure((void*)(l_Lake_Job_map___redArg___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_3);
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = lean_task_map(x_17, x_14, x_19, x_21);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_16);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_instFunctor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_Job_instFunctor() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lake_Job_instFunctor___lam__1), 4, 0);
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lake_Job_instFunctor___lam__0), 5, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobTaskOpaqueJobTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_toOpaque(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Job_toOpaque___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instCoeOutJobOpaqueJob___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Job_toOpaque), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutJobOpaqueJob(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeOutJobOpaqueJob___closed__0;
return x_2;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Task(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Opaque(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Data(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Task(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Opaque(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedJobAction = _init_l_Lake_instInhabitedJobAction();
l_Lake_reprJobAction___closed__0____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__0____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__0____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__1____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__1____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__1____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__2____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__2____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__2____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__3____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__3____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__3____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__4____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__4____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__4____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__5____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__5____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__5____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__6____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__6____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__6____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__7____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__7____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__7____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__8____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_ = _init_l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_();
lean_mark_persistent(l_Lake_reprJobAction___closed__9____x40_Lake_Build_Job_Basic___hyg_21_);
l_Lake_instReprJobAction___closed__0 = _init_l_Lake_instReprJobAction___closed__0();
lean_mark_persistent(l_Lake_instReprJobAction___closed__0);
l_Lake_instReprJobAction = _init_l_Lake_instReprJobAction();
lean_mark_persistent(l_Lake_instReprJobAction);
l_Lake_instOrdJobAction___closed__0 = _init_l_Lake_instOrdJobAction___closed__0();
lean_mark_persistent(l_Lake_instOrdJobAction___closed__0);
l_Lake_instOrdJobAction = _init_l_Lake_instOrdJobAction();
lean_mark_persistent(l_Lake_instOrdJobAction);
l_Lake_instLTJobAction = _init_l_Lake_instLTJobAction();
lean_mark_persistent(l_Lake_instLTJobAction);
l_Lake_instLEJobAction = _init_l_Lake_instLEJobAction();
lean_mark_persistent(l_Lake_instLEJobAction);
l_Lake_instMinJobAction = _init_l_Lake_instMinJobAction();
lean_mark_persistent(l_Lake_instMinJobAction);
l_Lake_instMaxJobAction = _init_l_Lake_instMaxJobAction();
lean_mark_persistent(l_Lake_instMaxJobAction);
l_Lake_JobAction_verb___closed__0 = _init_l_Lake_JobAction_verb___closed__0();
lean_mark_persistent(l_Lake_JobAction_verb___closed__0);
l_Lake_JobAction_verb___closed__1 = _init_l_Lake_JobAction_verb___closed__1();
lean_mark_persistent(l_Lake_JobAction_verb___closed__1);
l_Lake_JobAction_verb___closed__2 = _init_l_Lake_JobAction_verb___closed__2();
lean_mark_persistent(l_Lake_JobAction_verb___closed__2);
l_Lake_JobAction_verb___closed__3 = _init_l_Lake_JobAction_verb___closed__3();
lean_mark_persistent(l_Lake_JobAction_verb___closed__3);
l_Lake_JobAction_verb___closed__4 = _init_l_Lake_JobAction_verb___closed__4();
lean_mark_persistent(l_Lake_JobAction_verb___closed__4);
l_Lake_JobAction_verb___closed__5 = _init_l_Lake_JobAction_verb___closed__5();
lean_mark_persistent(l_Lake_JobAction_verb___closed__5);
l_Lake_JobAction_verb___closed__6 = _init_l_Lake_JobAction_verb___closed__6();
lean_mark_persistent(l_Lake_JobAction_verb___closed__6);
l_Lake_JobAction_verb___closed__7 = _init_l_Lake_JobAction_verb___closed__7();
lean_mark_persistent(l_Lake_JobAction_verb___closed__7);
l_Lake_instInhabitedJobState___closed__0 = _init_l_Lake_instInhabitedJobState___closed__0();
lean_mark_persistent(l_Lake_instInhabitedJobState___closed__0);
l_Lake_instInhabitedJobState___closed__1 = _init_l_Lake_instInhabitedJobState___closed__1();
lean_mark_persistent(l_Lake_instInhabitedJobState___closed__1);
l_Lake_instInhabitedJobState___closed__2 = _init_l_Lake_instInhabitedJobState___closed__2();
lean_mark_persistent(l_Lake_instInhabitedJobState___closed__2);
l_Lake_instInhabitedJobState___closed__3 = _init_l_Lake_instInhabitedJobState___closed__3();
lean_mark_persistent(l_Lake_instInhabitedJobState___closed__3);
l_Lake_instInhabitedJobState = _init_l_Lake_instInhabitedJobState();
lean_mark_persistent(l_Lake_instInhabitedJobState);
l_Lake_instInhabitedJob___closed__0 = _init_l_Lake_instInhabitedJob___closed__0();
lean_mark_persistent(l_Lake_instInhabitedJob___closed__0);
l_Lake_instInhabitedJob___closed__1 = _init_l_Lake_instInhabitedJob___closed__1();
lean_mark_persistent(l_Lake_instInhabitedJob___closed__1);
l_Lake_instInhabitedJob___closed__2 = _init_l_Lake_instInhabitedJob___closed__2();
lean_mark_persistent(l_Lake_instInhabitedJob___closed__2);
l_Lake_instInhabitedJob___closed__3 = _init_l_Lake_instInhabitedJob___closed__3();
lean_mark_persistent(l_Lake_instInhabitedJob___closed__3);
l_Lake_Job_instPure___lam__0___closed__0 = _init_l_Lake_Job_instPure___lam__0___closed__0();
lean_mark_persistent(l_Lake_Job_instPure___lam__0___closed__0);
l_Lake_Job_instPure___lam__0___closed__1 = _init_l_Lake_Job_instPure___lam__0___closed__1();
lean_mark_persistent(l_Lake_Job_instPure___lam__0___closed__1);
l_Lake_Job_instPure = _init_l_Lake_Job_instPure();
lean_mark_persistent(l_Lake_Job_instPure);
l_Lake_Job_instFunctor = _init_l_Lake_Job_instFunctor();
lean_mark_persistent(l_Lake_Job_instFunctor);
l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0 = _init_l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0();
lean_mark_persistent(l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0);
l_Lake_instCoeOutJobOpaqueJob___closed__0 = _init_l_Lake_instCoeOutJobOpaqueJob___closed__0();
lean_mark_persistent(l_Lake_instCoeOutJobOpaqueJob___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
