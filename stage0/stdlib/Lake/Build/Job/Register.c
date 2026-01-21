// Lean compiler output
// Module: Lake.Build.Job.Register
// Imports: public import Lake.Build.Fetch
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_JobState_renew___closed__0;
lean_object* lean_get_set_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Job_renew___redArg___closed__0;
static lean_object* l_Lake_ensureJob___redArg___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__6;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___redArg___closed__4;
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 1);
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lake_JobState_renew___closed__0;
x_10 = 0;
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 0, x_9);
lean_ctor_set_uint8(x_1, sizeof(void*)*3, x_10);
return x_1;
}
else
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lake_JobState_renew___closed__0;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set_uint64(x_17, sizeof(void*)*3, x_12);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*3, x_16);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
x_21 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lake_JobState_renew___closed__0;
x_25 = 0;
if (lean_is_scalar(x_22)) {
 x_26 = lean_alloc_ctor(0, 3, 8);
} else {
 x_26 = x_22;
}
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set_uint64(x_26, sizeof(void*)*3, x_20);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_25);
return x_27;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lake_JobState_renew___closed__0;
x_13 = 0;
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_2, 2, x_11);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_13);
return x_1;
}
else
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lake_JobState_renew___closed__0;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set_uint64(x_20, sizeof(void*)*3, x_15);
lean_ctor_set(x_2, 2, x_17);
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_19);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_24 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_24);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_25 = x_4;
} else {
 lean_dec_ref(x_4);
 x_25 = lean_box(0);
}
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lake_JobState_renew___closed__0;
x_28 = 0;
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 3, 8);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set_uint64(x_29, sizeof(void*)*3, x_23);
lean_ctor_set(x_2, 2, x_26);
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_27);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_2);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_33 = x_1;
} else {
 lean_dec_ref(x_1);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_34);
x_35 = lean_ctor_get_uint64(x_31, sizeof(void*)*3);
x_36 = lean_ctor_get(x_31, 2);
lean_inc_ref(x_36);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_37 = x_31;
} else {
 lean_dec_ref(x_31);
 x_37 = lean_box(0);
}
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lake_JobState_renew___closed__0;
x_40 = 0;
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 3, 8);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set_uint64(x_41, sizeof(void*)*3, x_35);
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_40);
if (lean_is_scalar(x_33)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_33;
}
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_45, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_48, 1);
lean_dec(x_52);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lake_JobState_renew___closed__0;
x_55 = 0;
lean_ctor_set(x_48, 1, x_54);
lean_ctor_set(x_45, 2, x_53);
lean_ctor_set(x_45, 0, x_54);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_55);
lean_ctor_set(x_1, 0, x_53);
return x_1;
}
else
{
lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get_uint64(x_48, sizeof(void*)*3);
x_58 = lean_ctor_get(x_48, 2);
lean_inc(x_58);
lean_inc(x_56);
lean_dec(x_48);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lake_JobState_renew___closed__0;
x_61 = 0;
x_62 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_58);
lean_ctor_set_uint64(x_62, sizeof(void*)*3, x_57);
lean_ctor_set(x_45, 2, x_59);
lean_ctor_set(x_45, 1, x_62);
lean_ctor_set(x_45, 0, x_60);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_61);
lean_ctor_set(x_1, 0, x_59);
return x_1;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_dec(x_45);
x_64 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get_uint64(x_63, sizeof(void*)*3);
x_66 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_66);
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
x_70 = 0;
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 3, 8);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_65);
x_72 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*3, x_70);
lean_ctor_set(x_1, 1, x_72);
lean_ctor_set(x_1, 0, x_68);
return x_1;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get_uint64(x_74, sizeof(void*)*3);
x_78 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_78);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
 x_79 = lean_box(0);
}
x_80 = lean_unsigned_to_nat(0u);
x_81 = l_Lake_JobState_renew___closed__0;
x_82 = 0;
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 3, 8);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set_uint64(x_83, sizeof(void*)*3, x_77);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(0, 3, 1);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_82);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
static lean_object* _init_l_Lake_Job_renew___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Job_renew___redArg___lam__0), 1, 0);
return x_1;
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
x_4 = l_Lake_Job_renew___redArg___closed__0;
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
x_12 = l_Lake_Job_renew___redArg___closed__0;
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
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec_ref(x_7);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
lean_inc_ref(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
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
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec_ref(x_7);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_4);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_6);
lean_inc_ref(x_20);
x_21 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
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
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lake_registerJob___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
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
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec_ref(x_9);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_8);
lean_inc_ref(x_7);
x_14 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_7);
x_15 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
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
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec_ref(x_9);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_8);
lean_inc_ref(x_22);
x_23 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
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
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
x_10 = l_Lake_registerJob(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_get_set_stdout(x_1);
lean_dec_ref(x_6);
x_7 = lean_get_set_stderr(x_2);
lean_dec_ref(x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_ensureJob___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ensureJob___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_ByteArray_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___redArg___closed__2;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Basic", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_ensureJob___redArg___closed__7;
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(185u);
x_4 = l_Lake_ensureJob___redArg___closed__6;
x_5 = l_Lake_ensureJob___redArg___closed__5;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_33; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lake_ensureJob___redArg___closed__0;
x_12 = lean_st_mk_ref(x_11);
lean_inc(x_12);
x_13 = l_IO_FS_Stream_ofBuffer(x_12);
lean_inc_ref(x_13);
x_14 = lean_get_set_stdout(x_13);
x_15 = lean_get_set_stderr(x_13);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
x_17 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_91; 
x_68 = lean_ctor_get(x_16, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_dec_ref(x_16);
lean_inc(x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_68);
x_71 = l_Lake_ensureJob___redArg___lam__0(x_14, x_15, x_70, x_69);
lean_dec_ref(x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
lean_dec(x_73);
x_91 = lean_string_validate_utf8(x_74);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_74);
x_92 = l_Lake_ensureJob___redArg___closed__1;
x_93 = l_Lake_ensureJob___redArg___closed__8;
x_94 = l_panic___redArg(x_92, x_93);
x_75 = x_94;
goto block_90;
}
else
{
lean_object* x_95; 
x_95 = lean_string_from_utf8_unchecked(x_74);
x_75 = x_95;
goto block_90;
}
block_90:
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_string_utf8_byte_size(x_75);
x_77 = lean_nat_dec_eq(x_76, x_10);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = l_Lake_ensureJob___redArg___closed__4;
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_10);
lean_ctor_set(x_79, 2, x_76);
x_80 = l_String_Slice_trimAscii(x_79);
lean_dec_ref(x_79);
x_81 = l_String_Slice_toString(x_80);
lean_dec_ref(x_80);
x_82 = lean_string_append(x_78, x_81);
lean_dec_ref(x_81);
x_83 = 1;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_box(0);
x_86 = lean_array_push(x_72, x_84);
x_87 = l_Lake_ensureJob___redArg___lam__2(x_68, x_85, x_3, x_4, x_5, x_6, x_7, x_86);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_33 = x_87;
goto block_67;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_75);
x_88 = lean_box(0);
x_89 = l_Lake_ensureJob___redArg___lam__2(x_68, x_88, x_3, x_4, x_5, x_6, x_7, x_72);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_33 = x_89;
goto block_67;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_96 = lean_ctor_get(x_16, 1);
lean_inc(x_96);
lean_dec_ref(x_16);
x_97 = lean_box(0);
x_98 = l_Lake_ensureJob___redArg___lam__0(x_14, x_15, x_97, x_96);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_18 = x_99;
x_19 = lean_box(0);
goto block_32;
}
block_32:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_18);
x_20 = l_Array_shrink___redArg(x_18, x_17);
x_21 = lean_array_get_size(x_18);
x_22 = l_Array_extract___redArg(x_18, x_17, x_21);
lean_dec_ref(x_18);
x_23 = l_Lake_ensureJob___redArg___closed__1;
x_24 = 0;
x_25 = l_Lake_ensureJob___redArg___closed__3;
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_task_pure(x_27);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
return x_31;
}
block_67:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_array_get_size(x_35);
x_37 = lean_nat_dec_lt(x_17, x_36);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_1);
return x_33;
}
else
{
uint8_t x_38; 
lean_inc(x_35);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_dec(x_43);
lean_inc(x_35);
x_44 = l_Array_shrink___redArg(x_35, x_17);
x_45 = l_Array_extract___redArg(x_35, x_17, x_36);
lean_dec(x_35);
x_46 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__1), 2, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = lean_task_map(x_46, x_42, x_10, x_37);
lean_ctor_set(x_34, 1, x_1);
lean_ctor_set(x_34, 0, x_47);
lean_ctor_set(x_33, 1, x_44);
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 2);
x_50 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
lean_inc(x_35);
x_51 = l_Array_shrink___redArg(x_35, x_17);
x_52 = l_Array_extract___redArg(x_35, x_17, x_36);
lean_dec(x_35);
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__1), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_task_map(x_53, x_48, x_10, x_37);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_1);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_50);
lean_ctor_set(x_33, 1, x_51);
lean_ctor_set(x_33, 0, x_55);
return x_33;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
x_56 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_57);
x_58 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_59 = x_34;
} else {
 lean_dec_ref(x_34);
 x_59 = lean_box(0);
}
lean_inc(x_35);
x_60 = l_Array_shrink___redArg(x_35, x_17);
x_61 = l_Array_extract___redArg(x_35, x_17, x_36);
lean_dec(x_35);
x_62 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__1), 2, 1);
lean_closure_set(x_62, 0, x_61);
x_63 = lean_task_map(x_62, x_56, x_10, x_37);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 3, 1);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_1);
lean_ctor_set(x_64, 2, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_33, 1);
lean_inc(x_66);
lean_dec_ref(x_33);
x_18 = x_66;
x_19 = lean_box(0);
goto block_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ensureJob___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_ensureJob___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_ensureJob(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
lean_inc_ref(x_9);
x_12 = l_Lake_ensureJob___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_9, 3);
lean_inc(x_17);
lean_dec_ref(x_9);
x_18 = lean_st_ref_take(x_17);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_inc_ref(x_14);
x_19 = l_Lake_Job_toOpaque___redArg(x_14);
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_st_ref_set(x_17, x_20);
lean_dec(x_17);
x_22 = l_Lake_Job_renew___redArg(x_14);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_ctor_get(x_9, 3);
lean_inc(x_25);
lean_dec_ref(x_9);
x_26 = lean_st_ref_take(x_25);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_4);
lean_inc_ref(x_27);
x_28 = l_Lake_Job_toOpaque___redArg(x_27);
x_29 = lean_array_push(x_26, x_28);
x_30 = lean_st_ref_set(x_25, x_29);
lean_dec(x_25);
x_31 = l_Lake_Job_renew___redArg(x_27);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_9, 3);
lean_inc(x_37);
lean_dec_ref(x_9);
x_38 = lean_st_ref_take(x_37);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 3, 1);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_2);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_4);
lean_inc_ref(x_39);
x_40 = l_Lake_Job_toOpaque___redArg(x_39);
x_41 = lean_array_push(x_38, x_40);
x_42 = lean_st_ref_set(x_37, x_41);
lean_dec(x_37);
x_43 = l_Lake_Job_renew___redArg(x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_33);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_withRegisterJob___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
lean_inc_ref(x_10);
x_13 = l_Lake_ensureJob___redArg(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 3);
lean_inc(x_18);
lean_dec_ref(x_10);
x_19 = lean_st_ref_take(x_18);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_5);
lean_inc_ref(x_15);
x_20 = l_Lake_Job_toOpaque___redArg(x_15);
x_21 = lean_array_push(x_19, x_20);
x_22 = lean_st_ref_set(x_18, x_21);
lean_dec(x_18);
x_23 = l_Lake_Job_renew___redArg(x_15);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_ctor_get(x_10, 3);
lean_inc(x_26);
lean_dec_ref(x_10);
x_27 = lean_st_ref_take(x_26);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_5);
lean_inc_ref(x_28);
x_29 = l_Lake_Job_toOpaque___redArg(x_28);
x_30 = lean_array_push(x_27, x_29);
x_31 = lean_st_ref_set(x_26, x_30);
lean_dec(x_26);
x_32 = l_Lake_Job_renew___redArg(x_28);
lean_ctor_set(x_13, 0, x_32);
return x_13;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_10, 3);
lean_inc(x_38);
lean_dec_ref(x_10);
x_39 = lean_st_ref_take(x_38);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 3, 1);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_3);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_5);
lean_inc_ref(x_40);
x_41 = l_Lake_Job_toOpaque___redArg(x_40);
x_42 = lean_array_push(x_39, x_41);
x_43 = lean_st_ref_set(x_38, x_42);
lean_dec(x_38);
x_44 = l_Lake_Job_renew___redArg(x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_34);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_withRegisterJob(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_string_utf8_byte_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; 
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_2, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_st_ref_take(x_17);
x_19 = 0;
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_19);
lean_inc_ref(x_2);
x_20 = l_Lake_Job_toOpaque___redArg(x_2);
x_21 = lean_array_push(x_18, x_20);
x_22 = lean_st_ref_set(x_17, x_21);
x_23 = l_Lake_Job_renew___redArg(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_st_ref_take(x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_7);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
lean_inc_ref(x_28);
x_29 = l_Lake_Job_toOpaque___redArg(x_28);
x_30 = lean_array_push(x_26, x_29);
x_31 = lean_st_ref_set(x_25, x_30);
x_32 = l_Lake_Job_renew___redArg(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_maybeRegisterJob___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_string_utf8_byte_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
lean_inc(x_12);
lean_inc_ref(x_11);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_3, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_8, 3);
x_23 = lean_st_ref_take(x_22);
x_24 = 0;
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_24);
lean_inc_ref(x_3);
x_25 = l_Lake_Job_toOpaque___redArg(x_3);
x_26 = lean_array_push(x_23, x_25);
x_27 = lean_st_ref_set(x_22, x_26);
x_28 = l_Lake_Job_renew___redArg(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
x_30 = lean_ctor_get(x_8, 3);
x_31 = lean_st_ref_take(x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_12);
lean_ctor_set(x_33, 2, x_2);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
lean_inc_ref(x_33);
x_34 = l_Lake_Job_toOpaque___redArg(x_33);
x_35 = lean_array_push(x_31, x_34);
x_36 = lean_st_ref_set(x_30, x_35);
x_37 = l_Lake_Job_renew___redArg(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_maybeRegisterJob(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_JobState_renew___closed__0 = _init_l_Lake_JobState_renew___closed__0();
lean_mark_persistent(l_Lake_JobState_renew___closed__0);
l_Lake_Job_renew___redArg___closed__0 = _init_l_Lake_Job_renew___redArg___closed__0();
lean_mark_persistent(l_Lake_Job_renew___redArg___closed__0);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
