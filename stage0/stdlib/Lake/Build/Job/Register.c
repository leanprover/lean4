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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_JobState_renew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_JobState_renew___closed__0 = (const lean_object*)&l_Lake_JobState_renew___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_Job_renew___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Job_renew___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Job_renew___redArg___closed__0 = (const lean_object*)&l_Lake_Job_renew___redArg___closed__0_value;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_panic___at___00Lake_ensureJob_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lake_ensureJob_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lake_ensureJob_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lake_ensureJob_spec__0(lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_once_cell_t l_Lake_ensureJob___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ensureJob___redArg___closed__0;
static const lean_string_object l_Lake_ensureJob___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_ensureJob___redArg___closed__1 = (const lean_object*)&l_Lake_ensureJob___redArg___closed__1_value;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
static lean_once_cell_t l_Lake_ensureJob___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ensureJob___redArg___closed__2;
static const lean_string_object l_Lake_ensureJob___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "stdout/stderr:\n"};
static const lean_object* l_Lake_ensureJob___redArg___closed__3 = (const lean_object*)&l_Lake_ensureJob___redArg___closed__3_value;
static const lean_string_object l_Lake_ensureJob___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_Lake_ensureJob___redArg___closed__4 = (const lean_object*)&l_Lake_ensureJob___redArg___closed__4_value;
static const lean_string_object l_Lake_ensureJob___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_Lake_ensureJob___redArg___closed__5 = (const lean_object*)&l_Lake_ensureJob___redArg___closed__5_value;
static const lean_string_object l_Lake_ensureJob___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_Lake_ensureJob___redArg___closed__6 = (const lean_object*)&l_Lake_ensureJob___redArg___closed__6_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_ensureJob___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ensureJob___redArg___closed__7;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_24; 
x_2 = lean_ctor_get(x_1, 1);
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_3 = x_1;
x_4 = x_24;
goto block_23;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_21; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_7 = lean_ctor_get(x_2, 2);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_8 = x_2;
x_9 = x_21;
goto block_20;
}
else
{
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = ((lean_object*)(l_Lake_JobState_renew___closed__0));
x_12 = 0;
x_13 = 0;
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_11);
x_14 = x_8;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_7);
lean_ctor_set_uint64(x_19, sizeof(void*)*3, x_6);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_4 == 0)
{
lean_ctor_set(x_3, 2, x_10);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_11);
x_15 = x_3;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_10);
x_15 = x_17;
goto block_16;
}
block_16:
{
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_13);
return x_15;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_34; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_2, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_2, 0);
lean_dec(x_36);
x_4 = x_2;
x_5 = x_34;
goto block_33;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_31; 
x_6 = lean_ctor_get(x_1, 0);
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_7 = x_1;
x_8 = x_31;
goto block_30;
}
else
{
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_28; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_11 = lean_ctor_get(x_3, 2);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_3, 1);
lean_dec(x_29);
x_12 = x_3;
x_13 = x_28;
goto block_27;
}
else
{
lean_inc(x_11);
lean_inc(x_9);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = ((lean_object*)(l_Lake_JobState_renew___closed__0));
x_16 = 0;
x_17 = 0;
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_15);
x_18 = x_12;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_11);
lean_ctor_set_uint64(x_26, sizeof(void*)*3, x_10);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_5 == 0)
{
lean_ctor_set(x_4, 2, x_14);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_15);
x_19 = x_4;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_14);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_17);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_19);
x_20 = x_7;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_69; 
x_37 = lean_ctor_get(x_1, 1);
x_69 = !lean_is_exclusive(x_1);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_1, 0);
lean_dec(x_70);
x_38 = x_1;
x_39 = x_69;
goto block_68;
}
else
{
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_65; 
x_40 = lean_ctor_get(x_37, 1);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_37, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 0);
lean_dec(x_67);
x_41 = x_37;
x_42 = x_65;
goto block_64;
}
else
{
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_62; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get_uint64(x_40, sizeof(void*)*3);
x_45 = lean_ctor_get(x_40, 2);
x_62 = !lean_is_exclusive(x_40);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_40, 1);
lean_dec(x_63);
x_46 = x_40;
x_47 = x_62;
goto block_61;
}
else
{
lean_inc(x_45);
lean_inc(x_43);
lean_dec(x_40);
x_46 = lean_box(0);
x_47 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = ((lean_object*)(l_Lake_JobState_renew___closed__0));
x_50 = 0;
x_51 = 0;
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_49);
x_52 = x_46;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set(x_60, 2, x_45);
lean_ctor_set_uint64(x_60, sizeof(void*)*3, x_44);
x_52 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_53; 
if (x_42 == 0)
{
lean_ctor_set(x_41, 2, x_48);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_49);
x_53 = x_41;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_52);
lean_ctor_set(x_58, 2, x_48);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*3 + 1, x_51);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_53);
lean_ctor_set(x_38, 0, x_48);
x_54 = x_38;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_53);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
x_6 = x_1;
x_7 = x_16;
goto block_15;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = ((lean_object*)(l_Lake_Job_renew___redArg___closed__0));
x_9 = lean_unsigned_to_nat(0u);
x_10 = 1;
x_11 = lean_task_map(x_8, x_2, x_9, x_10);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_11);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_5);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_22; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_5, 2);
lean_dec(x_23);
x_10 = x_5;
x_11 = x_22;
goto block_21;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec_ref(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_4);
x_14 = x_10;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_4);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_6);
lean_inc_ref(x_14);
x_15 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_13);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_12);
lean_closure_set(x_17, 3, x_16);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_3, x_17);
return x_18;
}
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_24; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_7, 2);
lean_dec(x_25);
x_12 = x_7;
x_13 = x_24;
goto block_23;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec_ref(x_9);
if (x_13 == 0)
{
lean_ctor_set(x_12, 2, x_6);
x_16 = x_12;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_6);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_8);
lean_inc_ref(x_16);
x_17 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_15);
lean_inc(x_14);
x_19 = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_18);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_5, x_19);
return x_20;
}
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
LEAN_EXPORT lean_object* l_panic___at___00Lake_ensureJob_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_panic___at___00Lake_ensureJob_spec__0___closed__0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
static lean_object* _init_l_Lake_ensureJob___redArg___closed__0(void) {
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
static lean_object* _init_l_Lake_ensureJob___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_ensureJob___redArg___closed__1));
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lake_ensureJob___redArg___closed__6));
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(193u);
x_4 = ((lean_object*)(l_Lake_ensureJob___redArg___closed__5));
x_5 = ((lean_object*)(l_Lake_ensureJob___redArg___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_32; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_obj_once(&l_Lake_ensureJob___redArg___closed__0, &l_Lake_ensureJob___redArg___closed__0_once, _init_l_Lake_ensureJob___redArg___closed__0);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_86; 
x_63 = lean_ctor_get(x_16, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_16, 1);
lean_inc(x_64);
lean_dec_ref(x_16);
lean_inc(x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = l_Lake_ensureJob___redArg___lam__0(x_14, x_15, x_65, x_64);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
lean_dec(x_68);
x_86 = lean_string_validate_utf8(x_69);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_69);
x_87 = lean_obj_once(&l_Lake_ensureJob___redArg___closed__7, &l_Lake_ensureJob___redArg___closed__7_once, _init_l_Lake_ensureJob___redArg___closed__7);
x_88 = l_panic___at___00Lake_ensureJob_spec__0(x_87);
x_70 = x_88;
goto block_85;
}
else
{
lean_object* x_89; 
x_89 = lean_string_from_utf8_unchecked(x_69);
x_70 = x_89;
goto block_85;
}
block_85:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_string_utf8_byte_size(x_70);
x_72 = lean_nat_dec_eq(x_71, x_10);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = ((lean_object*)(l_Lake_ensureJob___redArg___closed__3));
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_10);
lean_ctor_set(x_74, 2, x_71);
x_75 = l_String_Slice_trimAscii(x_74);
lean_dec_ref(x_74);
x_76 = l_String_Slice_toString(x_75);
lean_dec_ref(x_75);
x_77 = lean_string_append(x_73, x_76);
lean_dec_ref(x_76);
x_78 = 1;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_box(0);
x_81 = lean_array_push(x_67, x_79);
x_82 = l_Lake_ensureJob___redArg___lam__2(x_63, x_80, x_3, x_4, x_5, x_6, x_7, x_81);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_32 = x_82;
goto block_62;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_70);
x_83 = lean_box(0);
x_84 = l_Lake_ensureJob___redArg___lam__2(x_63, x_83, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_32 = x_84;
goto block_62;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_90 = lean_ctor_get(x_16, 1);
lean_inc(x_90);
lean_dec_ref(x_16);
x_91 = lean_box(0);
x_92 = l_Lake_ensureJob___redArg___lam__0(x_14, x_15, x_91, x_90);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_18 = x_93;
goto block_31;
}
block_31:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_18);
x_19 = l_Array_shrink___redArg(x_18, x_17);
x_20 = lean_array_get_size(x_18);
x_21 = l_Array_extract___redArg(x_18, x_17, x_20);
lean_dec_ref(x_18);
x_22 = ((lean_object*)(l_panic___at___00Lake_ensureJob_spec__0___closed__0));
x_23 = 0;
x_24 = 0;
x_25 = lean_obj_once(&l_Lake_ensureJob___redArg___closed__2, &l_Lake_ensureJob___redArg___closed__2_once, _init_l_Lake_ensureJob___redArg___closed__2);
x_26 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_task_pure(x_27);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
return x_30;
}
block_62:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_17, x_35);
if (x_36 == 0)
{
lean_dec(x_33);
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; uint8_t x_58; 
lean_inc(x_34);
x_58 = !lean_is_exclusive(x_32);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_32, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_32, 0);
lean_dec(x_60);
x_37 = x_32;
x_38 = x_58;
goto block_57;
}
else
{
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_55; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 2);
x_41 = lean_ctor_get_uint8(x_33, sizeof(void*)*3);
x_55 = !lean_is_exclusive(x_33);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_33, 1);
lean_dec(x_56);
x_42 = x_33;
x_43 = x_55;
goto block_54;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_42 = lean_box(0);
x_43 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_34);
x_44 = l_Array_shrink___redArg(x_34, x_17);
x_45 = l_Array_extract___redArg(x_34, x_17, x_35);
lean_dec(x_34);
x_46 = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__1), 2, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = lean_task_map(x_46, x_39, x_10, x_36);
if (x_43 == 0)
{
lean_ctor_set(x_42, 1, x_1);
lean_ctor_set(x_42, 0, x_47);
x_48 = x_42;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_1);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_41);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_44);
lean_ctor_set(x_37, 0, x_48);
x_49 = x_37;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_44);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_32, 1);
lean_inc(x_61);
lean_dec_ref(x_32);
x_18 = x_61;
goto block_31;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_37; 
lean_inc_ref(x_9);
x_12 = l_Lake_ensureJob___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
x_15 = x_12;
x_16 = x_37;
goto block_36;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_34; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_13, 2);
lean_dec(x_35);
x_19 = x_13;
x_20 = x_34;
goto block_33;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 3);
lean_inc(x_21);
lean_dec_ref(x_9);
x_22 = lean_st_ref_take(x_21);
if (x_20 == 0)
{
lean_ctor_set(x_19, 2, x_2);
x_23 = x_19;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_2);
x_23 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_4);
lean_inc_ref(x_23);
x_24 = l_Lake_Job_toOpaque___redArg(x_23);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_st_ref_set(x_21, x_25);
lean_dec(x_21);
x_27 = l_Lake_Job_renew___redArg(x_23);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_27);
x_28 = x_15;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_14);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_38; 
lean_inc_ref(x_10);
x_13 = l_Lake_ensureJob___redArg(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
x_16 = x_13;
x_17 = x_38;
goto block_37;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_35; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_14, 2);
lean_dec(x_36);
x_20 = x_14;
x_21 = x_35;
goto block_34;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 3);
lean_inc(x_22);
lean_dec_ref(x_10);
x_23 = lean_st_ref_take(x_22);
if (x_21 == 0)
{
lean_ctor_set(x_20, 2, x_3);
x_24 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_3);
x_24 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_5);
lean_inc_ref(x_24);
x_25 = l_Lake_Job_toOpaque___redArg(x_24);
x_26 = lean_array_push(x_23, x_25);
x_27 = lean_st_ref_set(x_22, x_26);
lean_dec(x_22);
x_28 = l_Lake_Job_renew___redArg(x_24);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_28);
x_29 = x_16;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_15);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
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
lean_object* x_13; uint8_t x_14; uint8_t x_27; 
lean_inc(x_7);
lean_inc_ref(x_6);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_2, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 0);
lean_dec(x_30);
x_13 = x_2;
x_14 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_st_ref_take(x_15);
x_17 = 0;
if (x_14 == 0)
{
lean_ctor_set(x_13, 2, x_1);
x_18 = x_13;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_1);
x_18 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
lean_inc_ref(x_18);
x_19 = l_Lake_Job_toOpaque___redArg(x_18);
x_20 = lean_array_push(x_16, x_19);
x_21 = lean_st_ref_set(x_15, x_20);
x_22 = l_Lake_Job_renew___redArg(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
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
lean_object* x_18; uint8_t x_19; uint8_t x_32; 
lean_inc(x_12);
lean_inc_ref(x_11);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_3, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_dec(x_35);
x_18 = x_3;
x_19 = x_32;
goto block_31;
}
else
{
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_8, 3);
x_21 = lean_st_ref_take(x_20);
x_22 = 0;
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_2);
x_23 = x_18;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_2);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_22);
lean_inc_ref(x_23);
x_24 = l_Lake_Job_toOpaque___redArg(x_23);
x_25 = lean_array_push(x_21, x_24);
x_26 = lean_st_ref_set(x_20, x_25);
x_27 = l_Lake_Job_renew___redArg(x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
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
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Fetch(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Job_Register(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Job_Register(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Job_Register(builtin);
}
#ifdef __cplusplus
}
#endif
