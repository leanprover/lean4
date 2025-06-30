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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = l_Lake_JobState_renew___closed__0;
x_8 = lean_box(0);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
x_9 = lean_unbox(x_8);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_9);
return x_1;
}
else
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lake_JobState_renew___closed__0;
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_11);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_16);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_17, sizeof(void*)*3);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
x_22 = l_Lake_JobState_renew___closed__0;
x_23 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 3, 8);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set_uint64(x_24, sizeof(void*)*3, x_19);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_26);
return x_25;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 1);
lean_dec(x_9);
x_10 = l_Lake_JobState_renew___closed__0;
x_11 = lean_box(0);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_2, 0, x_10);
x_12 = lean_unbox(x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_12);
return x_1;
}
else
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_13);
lean_dec(x_4);
x_16 = l_Lake_JobState_renew___closed__0;
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set_uint64(x_18, sizeof(void*)*3, x_14);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_24 = x_4;
} else {
 lean_dec_ref(x_4);
 x_24 = lean_box(0);
}
x_25 = l_Lake_JobState_renew___closed__0;
x_26 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 3, 8);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set_uint64(x_27, sizeof(void*)*3, x_22);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_2);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_32 = x_1;
} else {
 lean_dec_ref(x_1);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_30, sizeof(void*)*3);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_36 = x_30;
} else {
 lean_dec_ref(x_30);
 x_36 = lean_box(0);
}
x_37 = l_Lake_JobState_renew___closed__0;
x_38 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 3, 8);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set_uint64(x_39, sizeof(void*)*3, x_34);
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_unbox(x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_32)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_32;
}
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_ctor_get(x_44, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_47, 1);
lean_dec(x_50);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lake_JobState_renew___closed__0;
x_53 = lean_box(0);
lean_ctor_set(x_47, 1, x_52);
lean_ctor_set(x_44, 0, x_52);
x_54 = lean_unbox(x_53);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_54);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
else
{
lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get_uint64(x_47, sizeof(void*)*3);
x_57 = lean_ctor_get(x_47, 2);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_47);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lake_JobState_renew___closed__0;
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set_uint64(x_61, sizeof(void*)*3, x_56);
lean_ctor_set(x_44, 1, x_61);
lean_ctor_set(x_44, 0, x_59);
x_62 = lean_unbox(x_60);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_62);
lean_ctor_set(x_1, 0, x_58);
return x_1;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_dec(x_44);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_63, sizeof(void*)*3);
x_66 = lean_ctor_get(x_63, 2);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lake_JobState_renew___closed__0;
x_70 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 3, 8);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_65);
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_unbox(x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_73);
lean_ctor_set(x_1, 1, x_72);
lean_ctor_set(x_1, 0, x_68);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get_uint64(x_75, sizeof(void*)*3);
x_79 = lean_ctor_get(x_75, 2);
lean_inc(x_79);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_80 = x_75;
} else {
 lean_dec_ref(x_75);
 x_80 = lean_box(0);
}
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lake_JobState_renew___closed__0;
x_83 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 3, 8);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set_uint64(x_84, sizeof(void*)*3, x_78);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 2, 1);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_unbox(x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_86);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_85);
return x_87;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_alloc_closure((void*)(l_Lake_Job_renew___redArg___lam__0), 1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = lean_task_map(x_4, x_3, x_5, x_7);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_Job_renew___redArg___lam__0), 1, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = lean_task_map(x_13, x_9, x_14, x_16);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_12);
return x_18;
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
lean_dec(x_5);
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
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_10);
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
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_4);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_6);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_19);
lean_inc(x_18);
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
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_8);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_7);
x_15 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_13);
lean_inc(x_12);
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
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_8);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_21);
lean_inc(x_20);
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
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lake_registerJob___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_65; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_dec(x_19);
lean_inc(x_14);
lean_inc(x_16);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_14);
lean_inc(x_14);
lean_inc(x_16);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_14);
lean_inc(x_20);
lean_inc(x_16);
x_22 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_20);
lean_inc(x_14);
lean_inc(x_16);
lean_inc(x_15);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_23, 0, x_15);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_14);
x_24 = l_Lake_EStateT_instFunctor___redArg(x_15);
lean_inc(x_16);
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
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
x_40 = l_IO_FS_withIsolatedStreams___redArg(x_30, x_37, x_31, x_2, x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = lean_apply_7(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_array_get_size(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_44);
x_126 = lean_ctor_get(x_42, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_42, 1);
lean_inc(x_127);
lean_dec(x_42);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_string_utf8_byte_size(x_128);
x_131 = lean_unsigned_to_nat(0u);
x_132 = lean_nat_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_133 = l_Lake_ensureJob___redArg___closed__14;
x_134 = l_Lake_ensureJob___redArg___closed__15;
x_135 = l_Substring_takeWhileAux(x_128, x_130, x_134, x_131);
x_136 = l_Substring_takeRightWhileAux(x_128, x_135, x_134, x_130);
x_137 = lean_string_utf8_extract(x_128, x_135, x_136);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_128);
x_138 = lean_string_append(x_133, x_137);
lean_dec(x_137);
x_139 = lean_box(1);
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_138);
x_141 = lean_unbox(x_139);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_141);
x_142 = lean_box(0);
x_143 = lean_array_push(x_127, x_140);
x_144 = l_Lake_ensureJob___redArg___lam__1(x_129, x_142, x_3, x_4, x_5, x_6, x_7, x_143, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = x_144;
goto block_125;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_130);
lean_dec(x_128);
x_145 = lean_box(0);
x_146 = l_Lake_ensureJob___redArg___lam__1(x_129, x_145, x_3, x_4, x_5, x_6, x_7, x_127, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = x_146;
goto block_125;
}
}
else
{
lean_object* x_147; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = lean_ctor_get(x_42, 1);
lean_inc(x_147);
lean_dec(x_42);
x_46 = x_147;
x_47 = x_43;
goto block_64;
}
block_64:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
lean_inc(x_46);
x_48 = l_Array_shrink___redArg(x_46, x_45);
x_49 = lean_array_get_size(x_46);
x_50 = l_Array_extract___redArg(x_46, x_45, x_49);
lean_dec(x_46);
x_51 = l_Lake_ensureJob___redArg___closed__11;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_box(0);
x_54 = l_Lake_ensureJob___redArg___closed__13;
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_56);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_task_pure(x_57);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_1);
lean_ctor_set(x_60, 2, x_51);
x_61 = lean_unbox(x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_48);
if (lean_is_scalar(x_44)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_44;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_47);
return x_63;
}
block_125:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_66, 1);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_45, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_free_object(x_66);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_45);
lean_dec(x_1);
return x_65;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_65);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_65, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_65, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_69);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_69, 0);
x_78 = lean_ctor_get(x_69, 1);
lean_dec(x_78);
lean_inc(x_70);
x_79 = l_Array_shrink___redArg(x_70, x_45);
x_80 = l_Array_extract___redArg(x_70, x_45, x_71);
lean_dec(x_70);
x_81 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_81, 0, x_80);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_unbox(x_38);
x_84 = lean_task_map(x_81, x_77, x_82, x_83);
lean_ctor_set(x_69, 1, x_1);
lean_ctor_set(x_69, 0, x_84);
lean_ctor_set(x_66, 1, x_79);
return x_65;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_ctor_get(x_69, 0);
x_86 = lean_ctor_get(x_69, 2);
x_87 = lean_ctor_get_uint8(x_69, sizeof(void*)*3);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_69);
lean_inc(x_70);
x_88 = l_Array_shrink___redArg(x_70, x_45);
x_89 = l_Array_extract___redArg(x_70, x_45, x_71);
lean_dec(x_70);
x_90 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_unbox(x_38);
x_93 = lean_task_map(x_90, x_85, x_91, x_92);
x_94 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_1);
lean_ctor_set(x_94, 2, x_86);
lean_ctor_set_uint8(x_94, sizeof(void*)*3, x_87);
lean_ctor_set(x_66, 1, x_88);
lean_ctor_set(x_66, 0, x_94);
return x_65;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_65);
x_95 = lean_ctor_get(x_69, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_69, 2);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_69, sizeof(void*)*3);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 x_98 = x_69;
} else {
 lean_dec_ref(x_69);
 x_98 = lean_box(0);
}
lean_inc(x_70);
x_99 = l_Array_shrink___redArg(x_70, x_45);
x_100 = l_Array_extract___redArg(x_70, x_45, x_71);
lean_dec(x_70);
x_101 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_101, 0, x_100);
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_unbox(x_38);
x_104 = lean_task_map(x_101, x_95, x_102, x_103);
if (lean_is_scalar(x_98)) {
 x_105 = lean_alloc_ctor(0, 3, 1);
} else {
 x_105 = x_98;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_1);
lean_ctor_set(x_105, 2, x_96);
lean_ctor_set_uint8(x_105, sizeof(void*)*3, x_97);
lean_ctor_set(x_66, 1, x_99);
lean_ctor_set(x_66, 0, x_105);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_66);
lean_ctor_set(x_106, 1, x_67);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_66, 0);
x_108 = lean_ctor_get(x_66, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_66);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_45, x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_67);
lean_dec(x_45);
lean_dec(x_1);
return x_65;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_111 = x_65;
} else {
 lean_dec_ref(x_65);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 2);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_107, sizeof(void*)*3);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 x_115 = x_107;
} else {
 lean_dec_ref(x_107);
 x_115 = lean_box(0);
}
lean_inc(x_108);
x_116 = l_Array_shrink___redArg(x_108, x_45);
x_117 = l_Array_extract___redArg(x_108, x_45, x_109);
lean_dec(x_108);
x_118 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_118, 0, x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_unbox(x_38);
x_121 = lean_task_map(x_118, x_112, x_119, x_120);
if (lean_is_scalar(x_115)) {
 x_122 = lean_alloc_ctor(0, 3, 1);
} else {
 x_122 = x_115;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_1);
lean_ctor_set(x_122, 2, x_113);
lean_ctor_set_uint8(x_122, sizeof(void*)*3, x_114);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_116);
if (lean_is_scalar(x_111)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_111;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_67);
return x_124;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_197; 
x_148 = lean_ctor_get(x_10, 1);
x_149 = lean_ctor_get(x_12, 0);
x_150 = lean_ctor_get(x_12, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_12);
lean_inc(x_148);
lean_inc(x_150);
x_151 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_151, 0, x_150);
lean_closure_set(x_151, 1, x_148);
lean_inc(x_148);
lean_inc(x_150);
x_152 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_152, 0, x_150);
lean_closure_set(x_152, 1, x_148);
lean_inc(x_151);
lean_inc(x_150);
x_153 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_153, 0, x_150);
lean_closure_set(x_153, 1, x_151);
lean_inc(x_148);
lean_inc(x_150);
lean_inc(x_149);
x_154 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_154, 0, x_149);
lean_closure_set(x_154, 1, x_150);
lean_closure_set(x_154, 2, x_148);
x_155 = l_Lake_EStateT_instFunctor___redArg(x_149);
lean_inc(x_150);
x_156 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_156, 0, x_150);
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_154);
lean_ctor_set(x_157, 3, x_153);
lean_ctor_set(x_157, 4, x_152);
lean_ctor_set(x_10, 1, x_151);
lean_ctor_set(x_10, 0, x_157);
x_158 = l_ReaderT_instMonad___redArg(x_10);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = l_ReaderT_instMonad___redArg(x_159);
x_161 = l_ReaderT_instMonad___redArg(x_160);
x_162 = l_Lake_EquipT_instMonad___redArg(x_161);
x_163 = l_Lake_ensureJob___redArg___closed__10;
x_164 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_164, 0, x_150);
lean_closure_set(x_164, 1, x_148);
x_165 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_165, 0, x_164);
x_166 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_166, 0, x_165);
x_167 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_167, 0, x_166);
x_168 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_168, 0, x_167);
x_169 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_169, 0, x_168);
x_170 = lean_box(1);
x_171 = lean_unbox(x_170);
x_172 = l_IO_FS_withIsolatedStreams___redArg(x_162, x_169, x_163, x_2, x_171);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_173 = lean_apply_7(x_172, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_array_get_size(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_dec(x_176);
x_220 = lean_ctor_get(x_174, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_174, 1);
lean_inc(x_221);
lean_dec(x_174);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_224 = lean_string_utf8_byte_size(x_222);
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_nat_dec_eq(x_224, x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_227 = l_Lake_ensureJob___redArg___closed__14;
x_228 = l_Lake_ensureJob___redArg___closed__15;
x_229 = l_Substring_takeWhileAux(x_222, x_224, x_228, x_225);
x_230 = l_Substring_takeRightWhileAux(x_222, x_229, x_228, x_224);
x_231 = lean_string_utf8_extract(x_222, x_229, x_230);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_222);
x_232 = lean_string_append(x_227, x_231);
lean_dec(x_231);
x_233 = lean_box(1);
x_234 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_234, 0, x_232);
x_235 = lean_unbox(x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*1, x_235);
x_236 = lean_box(0);
x_237 = lean_array_push(x_221, x_234);
x_238 = l_Lake_ensureJob___redArg___lam__1(x_223, x_236, x_3, x_4, x_5, x_6, x_7, x_237, x_175);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = x_238;
goto block_219;
}
else
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_224);
lean_dec(x_222);
x_239 = lean_box(0);
x_240 = l_Lake_ensureJob___redArg___lam__1(x_223, x_239, x_3, x_4, x_5, x_6, x_7, x_221, x_175);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = x_240;
goto block_219;
}
}
else
{
lean_object* x_241; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_241 = lean_ctor_get(x_174, 1);
lean_inc(x_241);
lean_dec(x_174);
x_178 = x_241;
x_179 = x_175;
goto block_196;
}
block_196:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; 
lean_inc(x_178);
x_180 = l_Array_shrink___redArg(x_178, x_177);
x_181 = lean_array_get_size(x_178);
x_182 = l_Array_extract___redArg(x_178, x_177, x_181);
lean_dec(x_178);
x_183 = l_Lake_ensureJob___redArg___closed__11;
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_box(0);
x_186 = l_Lake_ensureJob___redArg___closed__13;
x_187 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_unbox(x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*2, x_188);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_187);
x_190 = lean_task_pure(x_189);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_1);
lean_ctor_set(x_192, 2, x_183);
x_193 = lean_unbox(x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*3, x_193);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_180);
if (lean_is_scalar(x_176)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_176;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_179);
return x_195;
}
block_219:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_202 = x_198;
} else {
 lean_dec_ref(x_198);
 x_202 = lean_box(0);
}
x_203 = lean_array_get_size(x_201);
x_204 = lean_nat_dec_lt(x_177, x_203);
if (x_204 == 0)
{
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_177);
lean_dec(x_1);
return x_197;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_205 = x_197;
} else {
 lean_dec_ref(x_197);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 2);
lean_inc(x_207);
x_208 = lean_ctor_get_uint8(x_200, sizeof(void*)*3);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 x_209 = x_200;
} else {
 lean_dec_ref(x_200);
 x_209 = lean_box(0);
}
lean_inc(x_201);
x_210 = l_Array_shrink___redArg(x_201, x_177);
x_211 = l_Array_extract___redArg(x_201, x_177, x_203);
lean_dec(x_201);
x_212 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_212, 0, x_211);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_unbox(x_170);
x_215 = lean_task_map(x_212, x_206, x_213, x_214);
if (lean_is_scalar(x_209)) {
 x_216 = lean_alloc_ctor(0, 3, 1);
} else {
 x_216 = x_209;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_1);
lean_ctor_set(x_216, 2, x_207);
lean_ctor_set_uint8(x_216, sizeof(void*)*3, x_208);
if (lean_is_scalar(x_202)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_202;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_210);
if (lean_is_scalar(x_205)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_205;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_199);
return x_218;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_294; 
x_242 = lean_ctor_get(x_10, 0);
x_243 = lean_ctor_get(x_10, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_10);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 lean_ctor_release(x_242, 3);
 lean_ctor_release(x_242, 4);
 x_246 = x_242;
} else {
 lean_dec_ref(x_242);
 x_246 = lean_box(0);
}
lean_inc(x_243);
lean_inc(x_245);
x_247 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_247, 0, x_245);
lean_closure_set(x_247, 1, x_243);
lean_inc(x_243);
lean_inc(x_245);
x_248 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_248, 0, x_245);
lean_closure_set(x_248, 1, x_243);
lean_inc(x_247);
lean_inc(x_245);
x_249 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_249, 0, x_245);
lean_closure_set(x_249, 1, x_247);
lean_inc(x_243);
lean_inc(x_245);
lean_inc(x_244);
x_250 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_250, 0, x_244);
lean_closure_set(x_250, 1, x_245);
lean_closure_set(x_250, 2, x_243);
x_251 = l_Lake_EStateT_instFunctor___redArg(x_244);
lean_inc(x_245);
x_252 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_252, 0, x_245);
if (lean_is_scalar(x_246)) {
 x_253 = lean_alloc_ctor(0, 5, 0);
} else {
 x_253 = x_246;
}
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_250);
lean_ctor_set(x_253, 3, x_249);
lean_ctor_set(x_253, 4, x_248);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_247);
x_255 = l_ReaderT_instMonad___redArg(x_254);
x_256 = l_ReaderT_instMonad___redArg(x_255);
x_257 = l_ReaderT_instMonad___redArg(x_256);
x_258 = l_ReaderT_instMonad___redArg(x_257);
x_259 = l_Lake_EquipT_instMonad___redArg(x_258);
x_260 = l_Lake_ensureJob___redArg___closed__10;
x_261 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_261, 0, x_245);
lean_closure_set(x_261, 1, x_243);
x_262 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_262, 0, x_261);
x_263 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_263, 0, x_262);
x_264 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_264, 0, x_263);
x_265 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_265, 0, x_264);
x_266 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_266, 0, x_265);
x_267 = lean_box(1);
x_268 = lean_unbox(x_267);
x_269 = l_IO_FS_withIsolatedStreams___redArg(x_259, x_266, x_260, x_2, x_268);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_270 = lean_apply_7(x_269, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
x_274 = lean_array_get_size(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
lean_dec(x_273);
x_317 = lean_ctor_get(x_271, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_271, 1);
lean_inc(x_318);
lean_dec(x_271);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = lean_string_utf8_byte_size(x_319);
x_322 = lean_unsigned_to_nat(0u);
x_323 = lean_nat_dec_eq(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_324 = l_Lake_ensureJob___redArg___closed__14;
x_325 = l_Lake_ensureJob___redArg___closed__15;
x_326 = l_Substring_takeWhileAux(x_319, x_321, x_325, x_322);
x_327 = l_Substring_takeRightWhileAux(x_319, x_326, x_325, x_321);
x_328 = lean_string_utf8_extract(x_319, x_326, x_327);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_319);
x_329 = lean_string_append(x_324, x_328);
lean_dec(x_328);
x_330 = lean_box(1);
x_331 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_331, 0, x_329);
x_332 = lean_unbox(x_330);
lean_ctor_set_uint8(x_331, sizeof(void*)*1, x_332);
x_333 = lean_box(0);
x_334 = lean_array_push(x_318, x_331);
x_335 = l_Lake_ensureJob___redArg___lam__1(x_320, x_333, x_3, x_4, x_5, x_6, x_7, x_334, x_272);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_294 = x_335;
goto block_316;
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_321);
lean_dec(x_319);
x_336 = lean_box(0);
x_337 = l_Lake_ensureJob___redArg___lam__1(x_320, x_336, x_3, x_4, x_5, x_6, x_7, x_318, x_272);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_294 = x_337;
goto block_316;
}
}
else
{
lean_object* x_338; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_338 = lean_ctor_get(x_271, 1);
lean_inc(x_338);
lean_dec(x_271);
x_275 = x_338;
x_276 = x_272;
goto block_293;
}
block_293:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; 
lean_inc(x_275);
x_277 = l_Array_shrink___redArg(x_275, x_274);
x_278 = lean_array_get_size(x_275);
x_279 = l_Array_extract___redArg(x_275, x_274, x_278);
lean_dec(x_275);
x_280 = l_Lake_ensureJob___redArg___closed__11;
x_281 = lean_unsigned_to_nat(0u);
x_282 = lean_box(0);
x_283 = l_Lake_ensureJob___redArg___closed__13;
x_284 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_284, 0, x_279);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_unbox(x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*2, x_285);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_284);
x_287 = lean_task_pure(x_286);
x_288 = lean_box(0);
x_289 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_1);
lean_ctor_set(x_289, 2, x_280);
x_290 = lean_unbox(x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*3, x_290);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_277);
if (lean_is_scalar(x_273)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_273;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_276);
return x_292;
}
block_316:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_299 = x_295;
} else {
 lean_dec_ref(x_295);
 x_299 = lean_box(0);
}
x_300 = lean_array_get_size(x_298);
x_301 = lean_nat_dec_lt(x_274, x_300);
if (x_301 == 0)
{
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_274);
lean_dec(x_1);
return x_294;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_302 = x_294;
} else {
 lean_dec_ref(x_294);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_297, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_297, 2);
lean_inc(x_304);
x_305 = lean_ctor_get_uint8(x_297, sizeof(void*)*3);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 lean_ctor_release(x_297, 2);
 x_306 = x_297;
} else {
 lean_dec_ref(x_297);
 x_306 = lean_box(0);
}
lean_inc(x_298);
x_307 = l_Array_shrink___redArg(x_298, x_274);
x_308 = l_Array_extract___redArg(x_298, x_274, x_300);
lean_dec(x_298);
x_309 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(x_309, 0, x_308);
x_310 = lean_unsigned_to_nat(0u);
x_311 = lean_unbox(x_267);
x_312 = lean_task_map(x_309, x_303, x_310, x_311);
if (lean_is_scalar(x_306)) {
 x_313 = lean_alloc_ctor(0, 3, 1);
} else {
 x_313 = x_306;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_1);
lean_ctor_set(x_313, 2, x_304);
lean_ctor_set_uint8(x_313, sizeof(void*)*3, x_305);
if (lean_is_scalar(x_299)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_299;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_307);
if (lean_is_scalar(x_302)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_302;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_296);
return x_315;
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_9);
x_12 = l_Lake_ensureJob___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
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
lean_dec(x_9);
x_21 = lean_st_ref_take(x_20, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_inc(x_14);
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
lean_dec(x_9);
x_36 = lean_st_ref_take(x_35, x_15);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_2);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_4);
lean_inc(x_39);
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
lean_inc(x_48);
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
lean_dec(x_9);
x_52 = lean_st_ref_take(x_51, x_15);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 3, 1);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set(x_55, 2, x_2);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_4);
lean_inc(x_55);
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
lean_inc(x_10);
x_13 = l_Lake_ensureJob___redArg(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
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
lean_dec(x_10);
x_22 = lean_st_ref_take(x_21, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_5);
lean_inc(x_15);
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
lean_dec(x_10);
x_37 = lean_st_ref_take(x_36, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_3);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_5);
lean_inc(x_40);
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
lean_inc(x_49);
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
lean_dec(x_10);
x_53 = lean_st_ref_take(x_52, x_16);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
if (lean_is_scalar(x_51)) {
 x_56 = lean_alloc_ctor(0, 3, 1);
} else {
 x_56 = x_51;
}
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_3);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_5);
lean_inc(x_56);
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
lean_dec(x_4);
x_13 = l_Lake_withRegisterJob___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_withRegisterJob(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_box(0);
lean_ctor_set(x_2, 2, x_1);
x_24 = lean_unbox(x_23);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_24);
lean_inc(x_2);
x_25 = l_Lake_Job_toOpaque___redArg(x_2);
x_26 = lean_array_push(x_21, x_25);
x_27 = lean_st_ref_set(x_18, x_26, x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l_Lake_Job_renew___redArg(x_2);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 0, x_30);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lake_Job_renew___redArg(x_2);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_box(0);
lean_ctor_set(x_2, 2, x_1);
x_37 = lean_unbox(x_36);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_37);
lean_inc(x_2);
x_38 = l_Lake_Job_toOpaque___redArg(x_2);
x_39 = lean_array_push(x_34, x_38);
x_40 = lean_st_ref_set(x_18, x_39, x_35);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = l_Lake_Job_renew___redArg(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_4);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_3, 3);
x_47 = lean_st_ref_take(x_46, x_5);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_7);
lean_ctor_set(x_52, 2, x_1);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_53);
lean_inc(x_52);
x_54 = l_Lake_Job_toOpaque___redArg(x_52);
x_55 = lean_array_push(x_48, x_54);
x_56 = lean_st_ref_set(x_46, x_55, x_49);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = l_Lake_Job_renew___redArg(x_52);
if (lean_is_scalar(x_50)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_50;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
x_14 = lean_string_utf8_byte_size(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_box(0);
lean_ctor_set(x_3, 2, x_2);
x_29 = lean_unbox(x_28);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_29);
lean_inc(x_3);
x_30 = l_Lake_Job_toOpaque___redArg(x_3);
x_31 = lean_array_push(x_26, x_30);
x_32 = lean_st_ref_set(x_23, x_31, x_27);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = l_Lake_Job_renew___redArg(x_3);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 0, x_35);
lean_ctor_set(x_32, 0, x_24);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l_Lake_Job_renew___redArg(x_3);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_box(0);
lean_ctor_set(x_3, 2, x_2);
x_42 = lean_unbox(x_41);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_42);
lean_inc(x_3);
x_43 = l_Lake_Job_toOpaque___redArg(x_3);
x_44 = lean_array_push(x_39, x_43);
x_45 = lean_st_ref_set(x_23, x_44, x_40);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = l_Lake_Job_renew___redArg(x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
x_51 = lean_ctor_get(x_8, 3);
x_52 = lean_st_ref_take(x_51, x_10);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_12);
lean_ctor_set(x_57, 2, x_2);
x_58 = lean_unbox(x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_58);
lean_inc(x_57);
x_59 = l_Lake_Job_toOpaque___redArg(x_57);
x_60 = lean_array_push(x_53, x_59);
x_61 = lean_st_ref_set(x_51, x_60, x_54);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = l_Lake_Job_renew___redArg(x_57);
if (lean_is_scalar(x_55)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_55;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_9);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_maybeRegisterJob___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_maybeRegisterJob(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
