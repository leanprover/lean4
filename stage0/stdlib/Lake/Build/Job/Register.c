// Lean compiler output
// Module: Lake.Build.Job.Register
// Imports: Lake.Build.Fetch
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
static lean_object* l_Lake_ensureJob___redArg___closed__5;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_JobState_renew___closed__0;
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_ensureJob___redArg___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__3;
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__6;
lean_object* l_ST_Prim_Ref_modifyUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__15;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__4;
static lean_object* l_Lake_ensureJob___redArg___closed__11;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__13;
lean_object* l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__14;
static lean_object* l_Lake_ensureJob___redArg___closed__12;
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_JobState_renew___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = l_Lake_JobState_renew___closed__0;
x_8 = 0;
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_8);
return x_1;
}
else
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_inc(x_9);
lean_dec(x_3);
x_12 = l_Lake_JobState_renew___closed__0;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set_uint64(x_14, sizeof(void*)*3, x_10);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_13);
return x_1;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint64(x_15, sizeof(void*)*3);
x_18 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_20 = l_Lake_JobState_renew___closed__0;
x_21 = 0;
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(0, 3, 8);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint64(x_22, sizeof(void*)*3, x_17);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_dec(x_9);
x_10 = l_Lake_JobState_renew___closed__0;
x_11 = 0;
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_2, 0, x_10);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_11);
return x_1;
}
else
{
lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_inc(x_12);
lean_dec(x_4);
x_15 = l_Lake_JobState_renew___closed__0;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set_uint64(x_17, sizeof(void*)*3, x_13);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_16);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_21 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_21);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_22 = x_4;
} else {
 lean_dec_ref(x_4);
 x_22 = lean_box(0);
}
x_23 = l_Lake_JobState_renew___closed__0;
x_24 = 0;
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 3, 8);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set_uint64(x_25, sizeof(void*)*3, x_20);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_23);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_2);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_29 = x_1;
} else {
 lean_dec_ref(x_1);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get_uint64(x_27, sizeof(void*)*3);
x_32 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_33 = x_27;
} else {
 lean_dec_ref(x_27);
 x_33 = lean_box(0);
}
x_34 = l_Lake_JobState_renew___closed__0;
x_35 = 0;
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 3, 8);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set_uint64(x_36, sizeof(void*)*3, x_31);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_35);
if (lean_is_scalar(x_29)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_29;
}
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_43, 1);
lean_dec(x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lake_JobState_renew___closed__0;
x_49 = 0;
lean_ctor_set(x_43, 1, x_48);
lean_ctor_set(x_40, 0, x_48);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_49);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
else
{
lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get_uint64(x_43, sizeof(void*)*3);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
lean_inc(x_50);
lean_dec(x_43);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lake_JobState_renew___closed__0;
x_55 = 0;
x_56 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set_uint64(x_56, sizeof(void*)*3, x_51);
lean_ctor_set(x_40, 1, x_56);
lean_ctor_set(x_40, 0, x_54);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_55);
lean_ctor_set(x_1, 0, x_53);
return x_1;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_dec(x_40);
x_58 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_58);
x_59 = lean_ctor_get_uint64(x_57, sizeof(void*)*3);
x_60 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Lake_JobState_renew___closed__0;
x_64 = 0;
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 3, 8);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set_uint64(x_65, sizeof(void*)*3, x_59);
x_66 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_64);
lean_ctor_set(x_1, 1, x_66);
lean_ctor_set(x_1, 0, x_62);
return x_1;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get_uint64(x_68, sizeof(void*)*3);
x_72 = lean_ctor_get(x_68, 2);
lean_inc_ref(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Lake_JobState_renew___closed__0;
x_76 = 0;
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 3, 8);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set_uint64(x_77, sizeof(void*)*3, x_71);
if (lean_is_scalar(x_69)) {
 x_78 = lean_alloc_ctor(0, 2, 1);
} else {
 x_78 = x_69;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_76);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_alloc_closure((void*)(l_Lake_Job_renew___redArg___lam__0), 1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_Job_renew___redArg___lam__0), 1, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = 1;
x_15 = lean_task_map(x_12, x_8, x_13, x_14);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Job_renew___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_Job_toOpaque___redArg(x_1);
x_4 = lean_array_push(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_Job_renew___redArg(x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyUnsafe___boxed), 5, 4);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_1);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_7);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
lean_inc_ref(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_11);
lean_inc_ref(x_10);
x_14 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_3, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_7);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_4);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_6);
lean_inc_ref(x_20);
x_21 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_19);
lean_inc_ref(x_18);
x_23 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_18);
lean_closure_set(x_23, 3, x_22);
x_24 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_3, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_9);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_8);
lean_inc_ref(x_7);
x_14 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_7);
x_15 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_13);
lean_inc_ref(x_12);
x_16 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_12);
lean_closure_set(x_16, 3, x_15);
x_17 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_5, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_9);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_8);
lean_inc_ref(x_22);
x_23 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_21);
lean_inc_ref(x_20);
x_25 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_4);
lean_closure_set(x_25, 2, x_20);
lean_closure_set(x_25, 3, x_24);
x_26 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_5, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_registerJob___redArg___lam__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lake_registerJob___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
x_10 = l_Lake_registerJob(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___redArg___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ensureJob___redArg___closed__2;
x_2 = l_Lake_ensureJob___redArg___closed__5;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ensureJob___redArg___closed__3;
x_2 = l_Lake_ensureJob___redArg___closed__6;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ensureJob___redArg___closed__2;
x_2 = l_Lake_ensureJob___redArg___closed__7;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ensureJob___redArg___closed__2;
x_2 = l_Lake_ensureJob___redArg___closed__8;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ensureJob___redArg___closed__1;
x_2 = l_Lake_ensureJob___redArg___closed__9;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___redArg___closed__12;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lake_ensureJob___redArg___closed__0;
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_62; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_dec(x_19);
lean_inc_ref(x_14);
lean_inc_ref(x_16);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_14);
lean_inc_ref(x_14);
lean_inc_ref(x_16);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_14);
lean_inc_ref(x_20);
lean_inc_ref(x_16);
x_22 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_20);
lean_inc_ref(x_14);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_23, 0, x_15);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_14);
x_24 = l_Lake_EStateT_instFunctor___redArg(x_15);
lean_inc_ref(x_16);
x_25 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_25, 0, x_16);
lean_ctor_set(x_12, 4, x_21);
lean_ctor_set(x_12, 3, x_22);
lean_ctor_set(x_12, 2, x_23);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_20);
x_26 = l_ReaderT_instMonad___redArg(x_10);
x_27 = l_ReaderT_instMonad___redArg(x_26);
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = l_Lake_EquipT_instMonad___redArg(x_29);
x_31 = l_Lake_ensureJob___redArg___closed__10;
x_32 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_32, 0, x_16);
lean_closure_set(x_32, 1, x_14);
x_33 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = 1;
x_39 = l_IO_FS_withIsolatedStreams___redArg(x_30, x_37, x_31, x_2, x_38);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_40 = lean_apply_7(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_43);
x_119 = lean_ctor_get(x_41, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_41, 1);
lean_inc(x_120);
lean_dec_ref(x_41);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_string_utf8_byte_size(x_121);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_126 = l_Lake_ensureJob___redArg___closed__14;
x_127 = l_Lake_ensureJob___redArg___closed__15;
x_128 = l_Substring_takeWhileAux(x_121, x_123, x_127, x_124);
x_129 = l_Substring_takeRightWhileAux(x_121, x_128, x_127, x_123);
x_130 = lean_string_utf8_extract(x_121, x_128, x_129);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_121);
x_131 = lean_string_append(x_126, x_130);
lean_dec_ref(x_130);
x_132 = 1;
x_133 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_132);
x_134 = lean_box(0);
x_135 = lean_array_push(x_120, x_133);
x_136 = l_Lake_ensureJob___redArg___lam__1(x_122, x_134, x_3, x_4, x_5, x_6, x_7, x_135, x_42);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_62 = x_136;
goto block_118;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_123);
lean_dec(x_121);
x_137 = lean_box(0);
x_138 = l_Lake_ensureJob___redArg___lam__1(x_122, x_137, x_3, x_4, x_5, x_6, x_7, x_120, x_42);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_62 = x_138;
goto block_118;
}
}
else
{
lean_object* x_139; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_139 = lean_ctor_get(x_41, 1);
lean_inc(x_139);
lean_dec_ref(x_41);
x_45 = x_139;
x_46 = x_42;
goto block_61;
}
block_61:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc_ref(x_45);
x_47 = l_Array_shrink___redArg(x_45, x_44);
x_48 = lean_array_get_size(x_45);
x_49 = l_Array_extract___redArg(x_45, x_44, x_48);
lean_dec_ref(x_45);
x_50 = l_Lake_ensureJob___redArg___closed__11;
x_51 = lean_unsigned_to_nat(0u);
x_52 = 0;
x_53 = l_Lake_ensureJob___redArg___closed__13;
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_task_pure(x_55);
x_57 = 0;
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_47);
if (lean_is_scalar(x_43)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_43;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_46);
return x_60;
}
block_118:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_lt(x_44, x_68);
if (x_69 == 0)
{
lean_dec(x_68);
lean_free_object(x_63);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_44);
lean_dec(x_1);
return x_62;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_62, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_62, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_66);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_ctor_get(x_66, 1);
lean_dec(x_75);
lean_inc(x_67);
x_76 = l_Array_shrink___redArg(x_67, x_44);
x_77 = l_Array_extract___redArg(x_67, x_44, x_68);
lean_dec(x_67);
x_78 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_78, 0, x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_task_map(x_78, x_74, x_79, x_38);
lean_ctor_set(x_66, 1, x_1);
lean_ctor_set(x_66, 0, x_80);
lean_ctor_set(x_63, 1, x_76);
return x_62;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_66, 0);
x_82 = lean_ctor_get(x_66, 2);
x_83 = lean_ctor_get_uint8(x_66, sizeof(void*)*3);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_66);
lean_inc(x_67);
x_84 = l_Array_shrink___redArg(x_67, x_44);
x_85 = l_Array_extract___redArg(x_67, x_44, x_68);
lean_dec(x_67);
x_86 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_86, 0, x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_task_map(x_86, x_81, x_87, x_38);
x_89 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_1);
lean_ctor_set(x_89, 2, x_82);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_83);
lean_ctor_set(x_63, 1, x_84);
lean_ctor_set(x_63, 0, x_89);
return x_62;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_62);
x_90 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_66, 2);
lean_inc_ref(x_91);
x_92 = lean_ctor_get_uint8(x_66, sizeof(void*)*3);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 x_93 = x_66;
} else {
 lean_dec_ref(x_66);
 x_93 = lean_box(0);
}
lean_inc(x_67);
x_94 = l_Array_shrink___redArg(x_67, x_44);
x_95 = l_Array_extract___redArg(x_67, x_44, x_68);
lean_dec(x_67);
x_96 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_96, 0, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_task_map(x_96, x_90, x_97, x_38);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 3, 1);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_1);
lean_ctor_set(x_99, 2, x_91);
lean_ctor_set_uint8(x_99, sizeof(void*)*3, x_92);
lean_ctor_set(x_63, 1, x_94);
lean_ctor_set(x_63, 0, x_99);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_63);
lean_ctor_set(x_100, 1, x_64);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_63, 0);
x_102 = lean_ctor_get(x_63, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_63);
x_103 = lean_array_get_size(x_102);
x_104 = lean_nat_dec_lt(x_44, x_103);
if (x_104 == 0)
{
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_64);
lean_dec(x_44);
lean_dec(x_1);
return x_62;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_105 = x_62;
} else {
 lean_dec_ref(x_62);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_101, 2);
lean_inc_ref(x_107);
x_108 = lean_ctor_get_uint8(x_101, sizeof(void*)*3);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
 x_109 = lean_box(0);
}
lean_inc(x_102);
x_110 = l_Array_shrink___redArg(x_102, x_44);
x_111 = l_Array_extract___redArg(x_102, x_44, x_103);
lean_dec(x_102);
x_112 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_112, 0, x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_task_map(x_112, x_106, x_113, x_38);
if (lean_is_scalar(x_109)) {
 x_115 = lean_alloc_ctor(0, 3, 1);
} else {
 x_115 = x_109;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_1);
lean_ctor_set(x_115, 2, x_107);
lean_ctor_set_uint8(x_115, sizeof(void*)*3, x_108);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_110);
if (lean_is_scalar(x_105)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_105;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_64);
return x_117;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_186; 
x_140 = lean_ctor_get(x_10, 1);
x_141 = lean_ctor_get(x_12, 0);
x_142 = lean_ctor_get(x_12, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_12);
lean_inc_ref(x_140);
lean_inc_ref(x_142);
x_143 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_143, 0, x_142);
lean_closure_set(x_143, 1, x_140);
lean_inc_ref(x_140);
lean_inc_ref(x_142);
x_144 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_144, 0, x_142);
lean_closure_set(x_144, 1, x_140);
lean_inc_ref(x_143);
lean_inc_ref(x_142);
x_145 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_145, 0, x_142);
lean_closure_set(x_145, 1, x_143);
lean_inc_ref(x_140);
lean_inc_ref(x_142);
lean_inc_ref(x_141);
x_146 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_146, 0, x_141);
lean_closure_set(x_146, 1, x_142);
lean_closure_set(x_146, 2, x_140);
x_147 = l_Lake_EStateT_instFunctor___redArg(x_141);
lean_inc_ref(x_142);
x_148 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_148, 0, x_142);
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_146);
lean_ctor_set(x_149, 3, x_145);
lean_ctor_set(x_149, 4, x_144);
lean_ctor_set(x_10, 1, x_143);
lean_ctor_set(x_10, 0, x_149);
x_150 = l_ReaderT_instMonad___redArg(x_10);
x_151 = l_ReaderT_instMonad___redArg(x_150);
x_152 = l_ReaderT_instMonad___redArg(x_151);
x_153 = l_ReaderT_instMonad___redArg(x_152);
x_154 = l_Lake_EquipT_instMonad___redArg(x_153);
x_155 = l_Lake_ensureJob___redArg___closed__10;
x_156 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_156, 0, x_142);
lean_closure_set(x_156, 1, x_140);
x_157 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_157, 0, x_156);
x_158 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_158, 0, x_157);
x_159 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_159, 0, x_158);
x_160 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_160, 0, x_159);
x_161 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_161, 0, x_160);
x_162 = 1;
x_163 = l_IO_FS_withIsolatedStreams___redArg(x_154, x_161, x_155, x_2, x_162);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_164 = lean_apply_7(x_163, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_dec(x_167);
x_208 = lean_ctor_get(x_165, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_165, 1);
lean_inc(x_209);
lean_dec_ref(x_165);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_string_utf8_byte_size(x_210);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_nat_dec_eq(x_212, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_215 = l_Lake_ensureJob___redArg___closed__14;
x_216 = l_Lake_ensureJob___redArg___closed__15;
x_217 = l_Substring_takeWhileAux(x_210, x_212, x_216, x_213);
x_218 = l_Substring_takeRightWhileAux(x_210, x_217, x_216, x_212);
x_219 = lean_string_utf8_extract(x_210, x_217, x_218);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_210);
x_220 = lean_string_append(x_215, x_219);
lean_dec_ref(x_219);
x_221 = 1;
x_222 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*1, x_221);
x_223 = lean_box(0);
x_224 = lean_array_push(x_209, x_222);
x_225 = l_Lake_ensureJob___redArg___lam__1(x_211, x_223, x_3, x_4, x_5, x_6, x_7, x_224, x_166);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_186 = x_225;
goto block_207;
}
else
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_212);
lean_dec(x_210);
x_226 = lean_box(0);
x_227 = l_Lake_ensureJob___redArg___lam__1(x_211, x_226, x_3, x_4, x_5, x_6, x_7, x_209, x_166);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_186 = x_227;
goto block_207;
}
}
else
{
lean_object* x_228; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_228 = lean_ctor_get(x_165, 1);
lean_inc(x_228);
lean_dec_ref(x_165);
x_169 = x_228;
x_170 = x_166;
goto block_185;
}
block_185:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_inc_ref(x_169);
x_171 = l_Array_shrink___redArg(x_169, x_168);
x_172 = lean_array_get_size(x_169);
x_173 = l_Array_extract___redArg(x_169, x_168, x_172);
lean_dec_ref(x_169);
x_174 = l_Lake_ensureJob___redArg___closed__11;
x_175 = lean_unsigned_to_nat(0u);
x_176 = 0;
x_177 = l_Lake_ensureJob___redArg___closed__13;
x_178 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*2, x_176);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_task_pure(x_179);
x_181 = 0;
x_182 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_1);
lean_ctor_set(x_182, 2, x_174);
lean_ctor_set_uint8(x_182, sizeof(void*)*3, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_171);
if (lean_is_scalar(x_167)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_167;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_170);
return x_184;
}
block_207:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_array_get_size(x_190);
x_193 = lean_nat_dec_lt(x_168, x_192);
if (x_193 == 0)
{
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_168);
lean_dec(x_1);
return x_186;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_189, 2);
lean_inc_ref(x_196);
x_197 = lean_ctor_get_uint8(x_189, sizeof(void*)*3);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
lean_inc(x_190);
x_199 = l_Array_shrink___redArg(x_190, x_168);
x_200 = l_Array_extract___redArg(x_190, x_168, x_192);
lean_dec(x_190);
x_201 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_201, 0, x_200);
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_task_map(x_201, x_195, x_202, x_162);
if (lean_is_scalar(x_198)) {
 x_204 = lean_alloc_ctor(0, 3, 1);
} else {
 x_204 = x_198;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_1);
lean_ctor_set(x_204, 2, x_196);
lean_ctor_set_uint8(x_204, sizeof(void*)*3, x_197);
if (lean_is_scalar(x_191)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_191;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_199);
if (lean_is_scalar(x_194)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_194;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_188);
return x_206;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_278; 
x_229 = lean_ctor_get(x_10, 0);
x_230 = lean_ctor_get(x_10, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_10);
x_231 = lean_ctor_get(x_229, 0);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc_ref(x_232);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 lean_ctor_release(x_229, 2);
 lean_ctor_release(x_229, 3);
 lean_ctor_release(x_229, 4);
 x_233 = x_229;
} else {
 lean_dec_ref(x_229);
 x_233 = lean_box(0);
}
lean_inc_ref(x_230);
lean_inc_ref(x_232);
x_234 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_234, 0, x_232);
lean_closure_set(x_234, 1, x_230);
lean_inc_ref(x_230);
lean_inc_ref(x_232);
x_235 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_235, 0, x_232);
lean_closure_set(x_235, 1, x_230);
lean_inc_ref(x_234);
lean_inc_ref(x_232);
x_236 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_236, 0, x_232);
lean_closure_set(x_236, 1, x_234);
lean_inc_ref(x_230);
lean_inc_ref(x_232);
lean_inc_ref(x_231);
x_237 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_237, 0, x_231);
lean_closure_set(x_237, 1, x_232);
lean_closure_set(x_237, 2, x_230);
x_238 = l_Lake_EStateT_instFunctor___redArg(x_231);
lean_inc_ref(x_232);
x_239 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_239, 0, x_232);
if (lean_is_scalar(x_233)) {
 x_240 = lean_alloc_ctor(0, 5, 0);
} else {
 x_240 = x_233;
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_240, 2, x_237);
lean_ctor_set(x_240, 3, x_236);
lean_ctor_set(x_240, 4, x_235);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_234);
x_242 = l_ReaderT_instMonad___redArg(x_241);
x_243 = l_ReaderT_instMonad___redArg(x_242);
x_244 = l_ReaderT_instMonad___redArg(x_243);
x_245 = l_ReaderT_instMonad___redArg(x_244);
x_246 = l_Lake_EquipT_instMonad___redArg(x_245);
x_247 = l_Lake_ensureJob___redArg___closed__10;
x_248 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_248, 0, x_232);
lean_closure_set(x_248, 1, x_230);
x_249 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_249, 0, x_248);
x_250 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_250, 0, x_249);
x_251 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_251, 0, x_250);
x_252 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_252, 0, x_251);
x_253 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_253, 0, x_252);
x_254 = 1;
x_255 = l_IO_FS_withIsolatedStreams___redArg(x_246, x_253, x_247, x_2, x_254);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_256 = lean_apply_7(x_255, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_259 = x_256;
} else {
 lean_dec_ref(x_256);
 x_259 = lean_box(0);
}
x_260 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_dec(x_259);
x_300 = lean_ctor_get(x_257, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_257, 1);
lean_inc(x_301);
lean_dec_ref(x_257);
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_string_utf8_byte_size(x_302);
x_305 = lean_unsigned_to_nat(0u);
x_306 = lean_nat_dec_eq(x_304, x_305);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_307 = l_Lake_ensureJob___redArg___closed__14;
x_308 = l_Lake_ensureJob___redArg___closed__15;
x_309 = l_Substring_takeWhileAux(x_302, x_304, x_308, x_305);
x_310 = l_Substring_takeRightWhileAux(x_302, x_309, x_308, x_304);
x_311 = lean_string_utf8_extract(x_302, x_309, x_310);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_302);
x_312 = lean_string_append(x_307, x_311);
lean_dec_ref(x_311);
x_313 = 1;
x_314 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set_uint8(x_314, sizeof(void*)*1, x_313);
x_315 = lean_box(0);
x_316 = lean_array_push(x_301, x_314);
x_317 = l_Lake_ensureJob___redArg___lam__1(x_303, x_315, x_3, x_4, x_5, x_6, x_7, x_316, x_258);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_278 = x_317;
goto block_299;
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_304);
lean_dec(x_302);
x_318 = lean_box(0);
x_319 = l_Lake_ensureJob___redArg___lam__1(x_303, x_318, x_3, x_4, x_5, x_6, x_7, x_301, x_258);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_278 = x_319;
goto block_299;
}
}
else
{
lean_object* x_320; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_320 = lean_ctor_get(x_257, 1);
lean_inc(x_320);
lean_dec_ref(x_257);
x_261 = x_320;
x_262 = x_258;
goto block_277;
}
block_277:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_inc_ref(x_261);
x_263 = l_Array_shrink___redArg(x_261, x_260);
x_264 = lean_array_get_size(x_261);
x_265 = l_Array_extract___redArg(x_261, x_260, x_264);
lean_dec_ref(x_261);
x_266 = l_Lake_ensureJob___redArg___closed__11;
x_267 = lean_unsigned_to_nat(0u);
x_268 = 0;
x_269 = l_Lake_ensureJob___redArg___closed__13;
x_270 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_270, 0, x_265);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set_uint8(x_270, sizeof(void*)*2, x_268);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_267);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_task_pure(x_271);
x_273 = 0;
x_274 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_1);
lean_ctor_set(x_274, 2, x_266);
lean_ctor_set_uint8(x_274, sizeof(void*)*3, x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_263);
if (lean_is_scalar(x_259)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_259;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_262);
return x_276;
}
block_299:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_279, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_283 = x_279;
} else {
 lean_dec_ref(x_279);
 x_283 = lean_box(0);
}
x_284 = lean_array_get_size(x_282);
x_285 = lean_nat_dec_lt(x_260, x_284);
if (x_285 == 0)
{
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_260);
lean_dec(x_1);
return x_278;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_286 = x_278;
} else {
 lean_dec_ref(x_278);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_281, 0);
lean_inc_ref(x_287);
x_288 = lean_ctor_get(x_281, 2);
lean_inc_ref(x_288);
x_289 = lean_ctor_get_uint8(x_281, sizeof(void*)*3);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 x_290 = x_281;
} else {
 lean_dec_ref(x_281);
 x_290 = lean_box(0);
}
lean_inc(x_282);
x_291 = l_Array_shrink___redArg(x_282, x_260);
x_292 = l_Array_extract___redArg(x_282, x_260, x_284);
lean_dec(x_282);
x_293 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_293, 0, x_292);
x_294 = lean_unsigned_to_nat(0u);
x_295 = lean_task_map(x_293, x_287, x_294, x_254);
if (lean_is_scalar(x_290)) {
 x_296 = lean_alloc_ctor(0, 3, 1);
} else {
 x_296 = x_290;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_1);
lean_ctor_set(x_296, 2, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*3, x_289);
if (lean_is_scalar(x_283)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_283;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_291);
if (lean_is_scalar(x_286)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_286;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_280);
return x_298;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_ensureJob___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ensureJob___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc_ref(x_9);
x_12 = l_Lake_ensureJob___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_14, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_9, 3);
lean_inc(x_20);
lean_dec_ref(x_9);
x_21 = lean_st_ref_take(x_20, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_inc_ref(x_14);
x_24 = l_Lake_Job_toOpaque___redArg(x_14);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_st_ref_set(x_20, x_25, x_23);
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lake_Job_renew___redArg(x_14);
lean_ctor_set(x_13, 0, x_29);
lean_ctor_set(x_26, 0, x_13);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lake_Job_renew___redArg(x_14);
lean_ctor_set(x_13, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_ctor_get(x_9, 3);
lean_inc(x_35);
lean_dec_ref(x_9);
x_36 = lean_st_ref_take(x_35, x_15);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_2);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_4);
lean_inc_ref(x_39);
x_40 = l_Lake_Job_toOpaque___redArg(x_39);
x_41 = lean_array_push(x_37, x_40);
x_42 = lean_st_ref_set(x_35, x_41, x_38);
lean_dec(x_35);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_13, 0, x_45);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_50 = x_14;
} else {
 lean_dec_ref(x_14);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_9, 3);
lean_inc(x_51);
lean_dec_ref(x_9);
x_52 = lean_st_ref_take(x_51, x_15);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 3, 1);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set(x_55, 2, x_2);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_4);
lean_inc_ref(x_55);
x_56 = l_Lake_Job_toOpaque___redArg(x_55);
x_57 = lean_array_push(x_53, x_56);
x_58 = lean_st_ref_set(x_51, x_57, x_54);
lean_dec(x_51);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lake_Job_renew___redArg(x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_47);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_10);
x_13 = l_Lake_ensureJob___redArg(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_15, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_10, 3);
lean_inc(x_21);
lean_dec_ref(x_10);
x_22 = lean_st_ref_take(x_21, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_5);
lean_inc_ref(x_15);
x_25 = l_Lake_Job_toOpaque___redArg(x_15);
x_26 = lean_array_push(x_23, x_25);
x_27 = lean_st_ref_set(x_21, x_26, x_24);
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l_Lake_Job_renew___redArg(x_15);
lean_ctor_set(x_14, 0, x_30);
lean_ctor_set(x_27, 0, x_14);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lake_Job_renew___redArg(x_15);
lean_ctor_set(x_14, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_ctor_get(x_10, 3);
lean_inc(x_36);
lean_dec_ref(x_10);
x_37 = lean_st_ref_take(x_36, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_3);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_5);
lean_inc_ref(x_40);
x_41 = l_Lake_Job_toOpaque___redArg(x_40);
x_42 = lean_array_push(x_38, x_41);
x_43 = lean_st_ref_set(x_36, x_42, x_39);
lean_dec(x_36);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = l_Lake_Job_renew___redArg(x_40);
lean_ctor_set(x_14, 0, x_46);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_14);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_dec(x_14);
x_49 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_51 = x_15;
} else {
 lean_dec_ref(x_15);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_10, 3);
lean_inc(x_52);
lean_dec_ref(x_10);
x_53 = lean_st_ref_take(x_52, x_16);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
if (lean_is_scalar(x_51)) {
 x_56 = lean_alloc_ctor(0, 3, 1);
} else {
 x_56 = x_51;
}
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_3);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_5);
lean_inc_ref(x_56);
x_57 = l_Lake_Job_toOpaque___redArg(x_56);
x_58 = lean_array_push(x_54, x_57);
x_59 = lean_st_ref_set(x_52, x_58, x_55);
lean_dec(x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = l_Lake_Job_renew___redArg(x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_48);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_withRegisterJob___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_withRegisterJob(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_8);
x_9 = lean_string_utf8_byte_size(x_8);
lean_dec_ref(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_2, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_st_ref_take(x_18, x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = 0;
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_23);
lean_inc_ref(x_2);
x_24 = l_Lake_Job_toOpaque___redArg(x_2);
x_25 = lean_array_push(x_21, x_24);
x_26 = lean_st_ref_set(x_18, x_25, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lake_Job_renew___redArg(x_2);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 0, x_29);
lean_ctor_set(x_26, 0, x_19);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lake_Job_renew___redArg(x_2);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = 0;
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_35);
lean_inc_ref(x_2);
x_36 = l_Lake_Job_toOpaque___redArg(x_2);
x_37 = lean_array_push(x_33, x_36);
x_38 = lean_st_ref_set(x_18, x_37, x_34);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = l_Lake_Job_renew___redArg(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
x_44 = lean_ctor_get(x_3, 3);
x_45 = lean_st_ref_take(x_44, x_5);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = 0;
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_7);
lean_ctor_set(x_50, 2, x_1);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
lean_inc_ref(x_50);
x_51 = l_Lake_Job_toOpaque___redArg(x_50);
x_52 = lean_array_push(x_46, x_51);
x_53 = lean_st_ref_set(x_44, x_52, x_47);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = l_Lake_Job_renew___redArg(x_50);
if (lean_is_scalar(x_48)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_48;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_13);
x_14 = lean_string_utf8_byte_size(x_13);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_st_ref_take(x_23, x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = 0;
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_28);
lean_inc_ref(x_3);
x_29 = l_Lake_Job_toOpaque___redArg(x_3);
x_30 = lean_array_push(x_26, x_29);
x_31 = lean_st_ref_set(x_23, x_30, x_27);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lake_Job_renew___redArg(x_3);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 0, x_34);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lake_Job_renew___redArg(x_3);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = 0;
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_40);
lean_inc_ref(x_3);
x_41 = l_Lake_Job_toOpaque___redArg(x_3);
x_42 = lean_array_push(x_38, x_41);
x_43 = lean_st_ref_set(x_23, x_42, x_39);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = l_Lake_Job_renew___redArg(x_3);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_9);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_3);
x_49 = lean_ctor_get(x_8, 3);
x_50 = lean_st_ref_take(x_49, x_10);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = 0;
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_11);
lean_ctor_set(x_55, 1, x_12);
lean_ctor_set(x_55, 2, x_2);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_54);
lean_inc_ref(x_55);
x_56 = l_Lake_Job_toOpaque___redArg(x_55);
x_57 = lean_array_push(x_51, x_56);
x_58 = lean_st_ref_set(x_49, x_57, x_52);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lake_Job_renew___redArg(x_55);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_9);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_maybeRegisterJob___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_maybeRegisterJob(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_JobState_renew___closed__0 = _init_l_Lake_JobState_renew___closed__0();
lean_mark_persistent(l_Lake_JobState_renew___closed__0);
l_Lake_ensureJob___redArg___closed__0 = _init_l_Lake_ensureJob___redArg___closed__0();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__0);
l_Lake_ensureJob___redArg___closed__1 = _init_l_Lake_ensureJob___redArg___closed__1();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__1);
l_Lake_ensureJob___redArg___closed__2 = _init_l_Lake_ensureJob___redArg___closed__2();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__2);
l_Lake_ensureJob___redArg___closed__3 = _init_l_Lake_ensureJob___redArg___closed__3();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__3);
l_Lake_ensureJob___redArg___closed__4 = _init_l_Lake_ensureJob___redArg___closed__4();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__4);
l_Lake_ensureJob___redArg___closed__5 = _init_l_Lake_ensureJob___redArg___closed__5();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__5);
l_Lake_ensureJob___redArg___closed__6 = _init_l_Lake_ensureJob___redArg___closed__6();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__6);
l_Lake_ensureJob___redArg___closed__7 = _init_l_Lake_ensureJob___redArg___closed__7();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__7);
l_Lake_ensureJob___redArg___closed__8 = _init_l_Lake_ensureJob___redArg___closed__8();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__8);
l_Lake_ensureJob___redArg___closed__9 = _init_l_Lake_ensureJob___redArg___closed__9();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__9);
l_Lake_ensureJob___redArg___closed__10 = _init_l_Lake_ensureJob___redArg___closed__10();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__10);
l_Lake_ensureJob___redArg___closed__11 = _init_l_Lake_ensureJob___redArg___closed__11();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__11);
l_Lake_ensureJob___redArg___closed__12 = _init_l_Lake_ensureJob___redArg___closed__12();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__12);
l_Lake_ensureJob___redArg___closed__13 = _init_l_Lake_ensureJob___redArg___closed__13();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__13);
l_Lake_ensureJob___redArg___closed__14 = _init_l_Lake_ensureJob___redArg___closed__14();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__14);
l_Lake_ensureJob___redArg___closed__15 = _init_l_Lake_ensureJob___redArg___closed__15();
lean_mark_persistent(l_Lake_ensureJob___redArg___closed__15);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
