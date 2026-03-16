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
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static const lean_array_object l_Lake_JobState_renew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_JobState_renew___closed__0 = (const lean_object*)&l_Lake_JobState_renew___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_Job_renew___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Job_renew___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Job_renew___redArg___closed__0 = (const lean_object*)&l_Lake_Job_renew___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_panic___at___00Lake_ensureJob_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lake_ensureJob_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lake_ensureJob_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lake_ensureJob_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_ensureJob___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ensureJob___redArg___closed__0;
static const lean_string_object l_Lake_ensureJob___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_ensureJob___redArg___closed__1 = (const lean_object*)&l_Lake_ensureJob___redArg___closed__1_value;
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
static lean_once_cell_t l_Lake_ensureJob___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ensureJob___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobState_renew(lean_object* v_s_3_){
_start:
{
lean_object* v_trace_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_26_; 
v_trace_4_ = lean_ctor_get(v_s_3_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_s_3_);
if (v_isSharedCheck_26_ == 0)
{
lean_object* v_unused_27_; lean_object* v_unused_28_; 
v_unused_27_ = lean_ctor_get(v_s_3_, 2);
lean_dec(v_unused_27_);
v_unused_28_ = lean_ctor_get(v_s_3_, 0);
lean_dec(v_unused_28_);
v___x_6_ = v_s_3_;
v_isShared_7_ = v_isSharedCheck_26_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_trace_4_);
lean_dec(v_s_3_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_26_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v_caption_8_; uint64_t v_hash_9_; lean_object* v_mtime_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_24_; 
v_caption_8_ = lean_ctor_get(v_trace_4_, 0);
v_hash_9_ = lean_ctor_get_uint64(v_trace_4_, sizeof(void*)*3);
v_mtime_10_ = lean_ctor_get(v_trace_4_, 2);
v_isSharedCheck_24_ = !lean_is_exclusive(v_trace_4_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v_trace_4_, 1);
lean_dec(v_unused_25_);
v___x_12_ = v_trace_4_;
v_isShared_13_ = v_isSharedCheck_24_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_mtime_10_);
lean_inc(v_caption_8_);
lean_dec(v_trace_4_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_24_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; uint8_t v___x_17_; lean_object* v___x_19_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = ((lean_object*)(l_Lake_JobState_renew___closed__0));
v___x_16_ = 0;
v___x_17_ = 0;
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_15_);
v___x_19_ = v___x_12_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_caption_8_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_mtime_10_);
lean_ctor_set_uint64(v_reuseFailAlloc_23_, sizeof(void*)*3, v_hash_9_);
v___x_19_ = v_reuseFailAlloc_23_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_21_; 
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 2, v___x_14_);
lean_ctor_set(v___x_6_, 1, v___x_19_);
lean_ctor_set(v___x_6_, 0, v___x_15_);
v___x_21_ = v___x_6_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_22_, 2, v___x_14_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*3, v___x_16_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*3 + 1, v___x_17_);
return v___x_21_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg___lam__0(lean_object* v_x_29_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_trace_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_62_; 
v_a_30_ = lean_ctor_get(v_x_29_, 1);
lean_inc(v_a_30_);
v_trace_31_ = lean_ctor_get(v_a_30_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_a_30_);
if (v_isSharedCheck_62_ == 0)
{
lean_object* v_unused_63_; lean_object* v_unused_64_; 
v_unused_63_ = lean_ctor_get(v_a_30_, 2);
lean_dec(v_unused_63_);
v_unused_64_ = lean_ctor_get(v_a_30_, 0);
lean_dec(v_unused_64_);
v___x_33_ = v_a_30_;
v_isShared_34_ = v_isSharedCheck_62_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_trace_31_);
lean_dec(v_a_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_62_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_60_; 
v_a_35_ = lean_ctor_get(v_x_29_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_29_);
if (v_isSharedCheck_60_ == 0)
{
lean_object* v_unused_61_; 
v_unused_61_ = lean_ctor_get(v_x_29_, 1);
lean_dec(v_unused_61_);
v___x_37_ = v_x_29_;
v_isShared_38_ = v_isSharedCheck_60_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v_x_29_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_60_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v_caption_39_; uint64_t v_hash_40_; lean_object* v_mtime_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_58_; 
v_caption_39_ = lean_ctor_get(v_trace_31_, 0);
v_hash_40_ = lean_ctor_get_uint64(v_trace_31_, sizeof(void*)*3);
v_mtime_41_ = lean_ctor_get(v_trace_31_, 2);
v_isSharedCheck_58_ = !lean_is_exclusive(v_trace_31_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; 
v_unused_59_ = lean_ctor_get(v_trace_31_, 1);
lean_dec(v_unused_59_);
v___x_43_ = v_trace_31_;
v_isShared_44_ = v_isSharedCheck_58_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_mtime_41_);
lean_inc(v_caption_39_);
lean_dec(v_trace_31_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_58_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; uint8_t v___x_48_; lean_object* v___x_50_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = ((lean_object*)(l_Lake_JobState_renew___closed__0));
v___x_47_ = 0;
v___x_48_ = 0;
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v___x_46_);
v___x_50_ = v___x_43_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_caption_39_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_57_, 2, v_mtime_41_);
lean_ctor_set_uint64(v_reuseFailAlloc_57_, sizeof(void*)*3, v_hash_40_);
v___x_50_ = v_reuseFailAlloc_57_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_52_; 
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 2, v___x_45_);
lean_ctor_set(v___x_33_, 1, v___x_50_);
lean_ctor_set(v___x_33_, 0, v___x_46_);
v___x_52_ = v___x_33_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 2, v___x_45_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*3, v___x_47_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*3 + 1, v___x_48_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v___x_52_);
v___x_54_ = v___x_37_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_35_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_97_; 
v_a_65_ = lean_ctor_get(v_x_29_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_29_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v_x_29_, 0);
lean_dec(v_unused_98_);
v___x_67_ = v_x_29_;
v_isShared_68_ = v_isSharedCheck_97_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v_x_29_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_97_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v_trace_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_94_; 
v_trace_69_ = lean_ctor_get(v_a_65_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; 
v_unused_95_ = lean_ctor_get(v_a_65_, 2);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_a_65_, 0);
lean_dec(v_unused_96_);
v___x_71_ = v_a_65_;
v_isShared_72_ = v_isSharedCheck_94_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_trace_69_);
lean_dec(v_a_65_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_94_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_caption_73_; uint64_t v_hash_74_; lean_object* v_mtime_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_92_; 
v_caption_73_ = lean_ctor_get(v_trace_69_, 0);
v_hash_74_ = lean_ctor_get_uint64(v_trace_69_, sizeof(void*)*3);
v_mtime_75_ = lean_ctor_get(v_trace_69_, 2);
v_isSharedCheck_92_ = !lean_is_exclusive(v_trace_69_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_trace_69_, 1);
lean_dec(v_unused_93_);
v___x_77_ = v_trace_69_;
v_isShared_78_ = v_isSharedCheck_92_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_mtime_75_);
lean_inc(v_caption_73_);
lean_dec(v_trace_69_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_92_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; uint8_t v___x_82_; lean_object* v___x_84_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = ((lean_object*)(l_Lake_JobState_renew___closed__0));
v___x_81_ = 0;
v___x_82_ = 0;
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_80_);
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_caption_73_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_mtime_75_);
lean_ctor_set_uint64(v_reuseFailAlloc_91_, sizeof(void*)*3, v_hash_74_);
v___x_84_ = v_reuseFailAlloc_91_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_86_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 2, v___x_79_);
lean_ctor_set(v___x_71_, 1, v___x_84_);
lean_ctor_set(v___x_71_, 0, v___x_80_);
v___x_86_ = v___x_71_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v___x_79_);
v___x_86_ = v_reuseFailAlloc_90_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_88_; 
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3, v___x_81_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 1, v___x_82_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_86_);
lean_ctor_set(v___x_67_, 0, v___x_79_);
v___x_88_ = v___x_67_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew___redArg(lean_object* v_self_100_){
_start:
{
lean_object* v_task_101_; lean_object* v_kind_102_; lean_object* v_caption_103_; uint8_t v_optional_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_115_; 
v_task_101_ = lean_ctor_get(v_self_100_, 0);
v_kind_102_ = lean_ctor_get(v_self_100_, 1);
v_caption_103_ = lean_ctor_get(v_self_100_, 2);
v_optional_104_ = lean_ctor_get_uint8(v_self_100_, sizeof(void*)*3);
v_isSharedCheck_115_ = !lean_is_exclusive(v_self_100_);
if (v_isSharedCheck_115_ == 0)
{
v___x_106_ = v_self_100_;
v_isShared_107_ = v_isSharedCheck_115_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_caption_103_);
lean_inc(v_kind_102_);
lean_inc(v_task_101_);
lean_dec(v_self_100_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_115_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___f_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___f_108_ = ((lean_object*)(l_Lake_Job_renew___redArg___closed__0));
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = 1;
v___x_111_ = lean_task_map(v___f_108_, v_task_101_, v___x_109_, v___x_110_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_111_);
v___x_113_ = v___x_106_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_kind_102_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_caption_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_114_, sizeof(void*)*3, v_optional_104_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_renew(lean_object* v_00_u03b1_116_, lean_object* v_self_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lake_Job_renew___redArg(v_self_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__0(lean_object* v_job_119_, lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = l_Lake_Job_toOpaque___redArg(v_job_119_);
v___x_122_ = lean_array_push(v_x_120_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__1(lean_object* v_job_123_, lean_object* v_toPure_124_, lean_object* v_____r_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = l_Lake_Job_renew___redArg(v_job_123_);
v___x_127_ = lean_apply_2(v_toPure_124_, lean_box(0), v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___lam__2(lean_object* v___f_128_, lean_object* v_inst_129_, lean_object* v_toBind_130_, lean_object* v___f_131_, lean_object* v_____do__lift_132_){
_start:
{
lean_object* v_registeredJobs_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_registeredJobs_133_ = lean_ctor_get(v_____do__lift_132_, 3);
lean_inc(v_registeredJobs_133_);
lean_dec_ref(v_____do__lift_132_);
v___x_134_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyUnsafe___boxed), 5, 4);
lean_closure_set(v___x_134_, 0, lean_box(0));
lean_closure_set(v___x_134_, 1, lean_box(0));
lean_closure_set(v___x_134_, 2, v_registeredJobs_133_);
lean_closure_set(v___x_134_, 3, v___f_128_);
v___x_135_ = lean_apply_2(v_inst_129_, lean_box(0), v___x_134_);
v___x_136_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v___x_135_, v___f_131_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg(lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_caption_140_, lean_object* v_job_141_, uint8_t v_optional_142_){
_start:
{
lean_object* v_toApplicative_143_; lean_object* v_task_144_; lean_object* v_kind_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_158_; 
v_toApplicative_143_ = lean_ctor_get(v_inst_137_, 0);
lean_inc_ref(v_toApplicative_143_);
v_task_144_ = lean_ctor_get(v_job_141_, 0);
v_kind_145_ = lean_ctor_get(v_job_141_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_job_141_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_job_141_, 2);
lean_dec(v_unused_159_);
v___x_147_ = v_job_141_;
v_isShared_148_ = v_isSharedCheck_158_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_kind_145_);
lean_inc(v_task_144_);
lean_dec(v_job_141_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_158_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_toBind_149_; lean_object* v_toPure_150_; lean_object* v_job_152_; 
v_toBind_149_ = lean_ctor_get(v_inst_137_, 1);
lean_inc(v_toBind_149_);
lean_dec_ref(v_inst_137_);
v_toPure_150_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_150_);
lean_dec_ref(v_toApplicative_143_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 2, v_caption_140_);
v_job_152_ = v___x_147_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_task_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_kind_145_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_caption_140_);
v_job_152_ = v_reuseFailAlloc_157_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___x_156_; 
lean_ctor_set_uint8(v_job_152_, sizeof(void*)*3, v_optional_142_);
lean_inc_ref(v_job_152_);
v___f_153_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(v___f_153_, 0, v_job_152_);
v___f_154_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
lean_closure_set(v___f_154_, 0, v_job_152_);
lean_closure_set(v___f_154_, 1, v_toPure_150_);
lean_inc(v_toBind_149_);
v___f_155_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(v___f_155_, 0, v___f_153_);
lean_closure_set(v___f_155_, 1, v_inst_138_);
lean_closure_set(v___f_155_, 2, v_toBind_149_);
lean_closure_set(v___f_155_, 3, v___f_154_);
v___x_156_ = lean_apply_4(v_toBind_149_, lean_box(0), lean_box(0), v_inst_139_, v___f_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_caption_163_, lean_object* v_job_164_, lean_object* v_optional_165_){
_start:
{
uint8_t v_optional_boxed_166_; lean_object* v_res_167_; 
v_optional_boxed_166_ = lean_unbox(v_optional_165_);
v_res_167_ = l_Lake_registerJob___redArg(v_inst_160_, v_inst_161_, v_inst_162_, v_caption_163_, v_job_164_, v_optional_boxed_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob(lean_object* v_m_168_, lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_caption_173_, lean_object* v_job_174_, uint8_t v_optional_175_){
_start:
{
lean_object* v_toApplicative_176_; lean_object* v_task_177_; lean_object* v_kind_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_191_; 
v_toApplicative_176_ = lean_ctor_get(v_inst_170_, 0);
lean_inc_ref(v_toApplicative_176_);
v_task_177_ = lean_ctor_get(v_job_174_, 0);
v_kind_178_ = lean_ctor_get(v_job_174_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_job_174_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v_job_174_, 2);
lean_dec(v_unused_192_);
v___x_180_ = v_job_174_;
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_kind_178_);
lean_inc(v_task_177_);
lean_dec(v_job_174_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_toBind_182_; lean_object* v_toPure_183_; lean_object* v_job_185_; 
v_toBind_182_ = lean_ctor_get(v_inst_170_, 1);
lean_inc(v_toBind_182_);
lean_dec_ref(v_inst_170_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_176_, 1);
lean_inc(v_toPure_183_);
lean_dec_ref(v_toApplicative_176_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 2, v_caption_173_);
v_job_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_task_177_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_kind_178_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_caption_173_);
v_job_185_ = v_reuseFailAlloc_190_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; 
lean_ctor_set_uint8(v_job_185_, sizeof(void*)*3, v_optional_175_);
lean_inc_ref(v_job_185_);
v___f_186_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(v___f_186_, 0, v_job_185_);
v___f_187_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
lean_closure_set(v___f_187_, 0, v_job_185_);
lean_closure_set(v___f_187_, 1, v_toPure_183_);
lean_inc(v_toBind_182_);
v___f_188_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(v___f_188_, 0, v___f_186_);
lean_closure_set(v___f_188_, 1, v_inst_171_);
lean_closure_set(v___f_188_, 2, v_toBind_182_);
lean_closure_set(v___f_188_, 3, v___f_187_);
v___x_189_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v_inst_172_, v___f_188_);
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object* v_m_193_, lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_caption_198_, lean_object* v_job_199_, lean_object* v_optional_200_){
_start:
{
uint8_t v_optional_boxed_201_; lean_object* v_res_202_; 
v_optional_boxed_201_ = lean_unbox(v_optional_200_);
v_res_202_ = l_Lake_registerJob(v_m_193_, v_00_u03b1_194_, v_inst_195_, v_inst_196_, v_inst_197_, v_caption_198_, v_job_199_, v_optional_boxed_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_ensureJob_spec__0(lean_object* v_msg_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_panic___at___00Lake_ensureJob_spec__0___closed__0));
v___x_206_ = lean_panic_fn(v___x_205_, v_msg_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object* v_val_207_, lean_object* v_val_208_, lean_object* v_a_x3f_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = lean_get_set_stdout(v_val_207_);
lean_dec_ref(v___x_212_);
v___x_213_ = lean_get_set_stderr(v_val_208_);
lean_dec_ref(v___x_213_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___y_210_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0___boxed(lean_object* v_val_216_, lean_object* v_val_217_, lean_object* v_a_x3f_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lake_ensureJob___redArg___lam__0(v_val_216_, v_val_217_, v_a_x3f_218_, v___y_219_);
lean_dec(v_a_x3f_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object* v___x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lake_JobResult_prependLog___redArg(v___x_222_, v_x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2(lean_object* v_a_225_, lean_object* v_____r_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_a_225_);
lean_ctor_set(v___x_234_, 1, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2___boxed(lean_object* v_a_235_, lean_object* v_____r_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lake_ensureJob___redArg___lam__2(v_a_235_, v_____r_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_244_;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__0(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_ByteArray_empty;
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__2(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__1));
v___x_250_ = l_Lake_BuildTrace_nil(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__7(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__6));
v___x_256_ = lean_unsigned_to_nat(46u);
v___x_257_ = lean_unsigned_to_nat(193u);
v___x_258_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__5));
v___x_259_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__4));
v___x_260_ = l_mkPanicMessageWithDecl(v___x_259_, v___x_258_, v___x_257_, v___x_256_, v___x_255_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg(lean_object* v_inst_261_, lean_object* v_x_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_iniPos_277_; lean_object* v_a_279_; lean_object* v___y_293_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__0, &l_Lake_ensureJob___redArg___closed__0_once, _init_l_Lake_ensureJob___redArg___closed__0);
v___x_272_ = lean_st_mk_ref(v___x_271_);
lean_inc(v___x_272_);
v___x_273_ = l_IO_FS_Stream_ofBuffer(v___x_272_);
lean_inc_ref(v___x_273_);
v___x_274_ = lean_get_set_stdout(v___x_273_);
v___x_275_ = lean_get_set_stderr(v___x_273_);
lean_inc_ref(v_a_268_);
lean_inc_ref(v_a_267_);
lean_inc(v_a_266_);
lean_inc(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
v___x_276_ = lean_apply_7(v_x_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, lean_box(0));
v_iniPos_277_ = lean_array_get_size(v_a_268_);
lean_dec_ref(v_a_268_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_323_; lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_a_327_; lean_object* v___x_328_; lean_object* v_data_329_; lean_object* v___y_331_; uint8_t v___x_346_; 
v_a_323_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_323_);
v_a_324_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_a_324_);
lean_dec_ref(v___x_276_);
lean_inc(v_a_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_323_);
v___x_326_ = l_Lake_ensureJob___redArg___lam__0(v___x_274_, v___x_275_, v___x_325_, v_a_324_);
lean_dec_ref(v___x_325_);
v_a_327_ = lean_ctor_get(v___x_326_, 1);
lean_inc(v_a_327_);
lean_dec_ref(v___x_326_);
v___x_328_ = lean_st_ref_get(v___x_272_);
lean_dec(v___x_272_);
v_data_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_data_329_);
lean_dec(v___x_328_);
v___x_346_ = lean_string_validate_utf8(v_data_329_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec_ref(v_data_329_);
v___x_347_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__7, &l_Lake_ensureJob___redArg___closed__7_once, _init_l_Lake_ensureJob___redArg___closed__7);
v___x_348_ = l_panic___at___00Lake_ensureJob_spec__0(v___x_347_);
v___y_331_ = v___x_348_;
goto v___jp_330_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_string_from_utf8_unchecked(v_data_329_);
v___y_331_ = v___x_349_;
goto v___jp_330_;
}
v___jp_330_:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_string_utf8_byte_size(v___y_331_);
v___x_333_ = lean_nat_dec_eq(v___x_332_, v___x_270_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_334_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__3));
v___x_335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_335_, 0, v___y_331_);
lean_ctor_set(v___x_335_, 1, v___x_270_);
lean_ctor_set(v___x_335_, 2, v___x_332_);
v___x_336_ = l_String_Slice_trimAscii(v___x_335_);
lean_dec_ref(v___x_335_);
v___x_337_ = l_String_Slice_toString(v___x_336_);
lean_dec_ref(v___x_336_);
v___x_338_ = lean_string_append(v___x_334_, v___x_337_);
lean_dec_ref(v___x_337_);
v___x_339_ = 1;
v___x_340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_339_);
v___x_341_ = lean_box(0);
v___x_342_ = lean_array_push(v_a_327_, v___x_340_);
v___x_343_ = l_Lake_ensureJob___redArg___lam__2(v_a_323_, v___x_341_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v___x_342_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
v___y_293_ = v___x_343_;
goto v___jp_292_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec_ref(v___y_331_);
v___x_344_ = lean_box(0);
v___x_345_ = l_Lake_ensureJob___redArg___lam__2(v_a_323_, v___x_344_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_327_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
v___y_293_ = v___x_345_;
goto v___jp_292_;
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_a_353_; 
lean_dec(v___x_272_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
v_a_350_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_a_350_);
lean_dec_ref(v___x_276_);
v___x_351_ = lean_box(0);
v___x_352_ = l_Lake_ensureJob___redArg___lam__0(v___x_274_, v___x_275_, v___x_351_, v_a_350_);
v_a_353_ = lean_ctor_get(v___x_352_, 1);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v_a_279_ = v_a_353_;
goto v___jp_278_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_inc_ref(v_a_279_);
v___x_280_ = l_Array_shrink___redArg(v_a_279_, v_iniPos_277_);
v___x_281_ = lean_array_get_size(v_a_279_);
v___x_282_ = l_Array_extract___redArg(v_a_279_, v_iniPos_277_, v___x_281_);
lean_dec_ref(v_a_279_);
v___x_283_ = ((lean_object*)(l_panic___at___00Lake_ensureJob_spec__0___closed__0));
v___x_284_ = 0;
v___x_285_ = 0;
v___x_286_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__2, &l_Lake_ensureJob___redArg___closed__2_once, _init_l_Lake_ensureJob___redArg___closed__2);
v___x_287_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_287_, 0, v___x_282_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_ctor_set(v___x_287_, 2, v___x_270_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*3, v___x_284_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*3 + 1, v___x_285_);
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_270_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_task_pure(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_inst_261_);
lean_ctor_set(v___x_290_, 2, v___x_283_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*3, v___x_285_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_280_);
return v___x_291_;
}
v___jp_292_:
{
if (lean_obj_tag(v___y_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_a_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_a_294_ = lean_ctor_get(v___y_293_, 0);
lean_inc(v_a_294_);
v_a_295_ = lean_ctor_get(v___y_293_, 1);
v___x_296_ = lean_array_get_size(v_a_295_);
v___x_297_ = lean_nat_dec_lt(v_iniPos_277_, v___x_296_);
if (v___x_297_ == 0)
{
lean_dec(v_a_294_);
lean_dec(v_inst_261_);
return v___y_293_;
}
else
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_319_; 
lean_inc(v_a_295_);
v_isSharedCheck_319_ = !lean_is_exclusive(v___y_293_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_320_ = lean_ctor_get(v___y_293_, 1);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v___y_293_, 0);
lean_dec(v_unused_321_);
v___x_299_ = v___y_293_;
v_isShared_300_ = v_isSharedCheck_319_;
goto v_resetjp_298_;
}
else
{
lean_dec(v___y_293_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_319_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_task_301_; lean_object* v_caption_302_; uint8_t v_optional_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_317_; 
v_task_301_ = lean_ctor_get(v_a_294_, 0);
v_caption_302_ = lean_ctor_get(v_a_294_, 2);
v_optional_303_ = lean_ctor_get_uint8(v_a_294_, sizeof(void*)*3);
v_isSharedCheck_317_ = !lean_is_exclusive(v_a_294_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_a_294_, 1);
lean_dec(v_unused_318_);
v___x_305_ = v_a_294_;
v_isShared_306_ = v_isSharedCheck_317_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_caption_302_);
lean_inc(v_task_301_);
lean_dec(v_a_294_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_317_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
lean_inc(v_a_295_);
v___x_307_ = l_Array_shrink___redArg(v_a_295_, v_iniPos_277_);
v___x_308_ = l_Array_extract___redArg(v_a_295_, v_iniPos_277_, v___x_296_);
lean_dec(v_a_295_);
v___f_309_ = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__1), 2, 1);
lean_closure_set(v___f_309_, 0, v___x_308_);
v___x_310_ = lean_task_map(v___f_309_, v_task_301_, v___x_270_, v___x_297_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_inst_261_);
lean_ctor_set(v___x_305_, 0, v___x_310_);
v___x_312_ = v___x_305_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_inst_261_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_caption_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*3, v_optional_303_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_307_);
lean_ctor_set(v___x_299_, 0, v___x_312_);
v___x_314_ = v___x_299_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_307_);
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
}
}
else
{
lean_object* v_a_322_; 
v_a_322_ = lean_ctor_get(v___y_293_, 1);
lean_inc(v_a_322_);
lean_dec_ref(v___y_293_);
v_a_279_ = v_a_322_;
goto v___jp_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___boxed(lean_object* v_inst_354_, lean_object* v_x_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lake_ensureJob___redArg(v_inst_354_, v_x_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object* v_00_u03b1_364_, lean_object* v_inst_365_, lean_object* v_x_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lake_ensureJob___redArg(v_inst_365_, v_x_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___boxed(lean_object* v_00_u03b1_375_, lean_object* v_inst_376_, lean_object* v_x_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lake_ensureJob(v_00_u03b1_375_, v_inst_376_, v_x_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object* v_inst_386_, lean_object* v_caption_387_, lean_object* v_x_388_, uint8_t v_optional_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_422_; 
lean_inc_ref(v_a_394_);
v___x_397_ = l_Lake_ensureJob___redArg(v_inst_386_, v_x_388_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_a_399_ = lean_ctor_get(v___x_397_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_422_ == 0)
{
v___x_401_ = v___x_397_;
v_isShared_402_ = v_isSharedCheck_422_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_422_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_task_403_; lean_object* v_kind_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_420_; 
v_task_403_ = lean_ctor_get(v_a_398_, 0);
v_kind_404_ = lean_ctor_get(v_a_398_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_398_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_a_398_, 2);
lean_dec(v_unused_421_);
v___x_406_ = v_a_398_;
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_kind_404_);
lean_inc(v_task_403_);
lean_dec(v_a_398_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_registeredJobs_408_; lean_object* v___x_409_; lean_object* v_job_411_; 
v_registeredJobs_408_ = lean_ctor_get(v_a_394_, 3);
lean_inc(v_registeredJobs_408_);
lean_dec_ref(v_a_394_);
v___x_409_ = lean_st_ref_take(v_registeredJobs_408_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 2, v_caption_387_);
v_job_411_ = v___x_406_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_task_403_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_kind_404_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_caption_387_);
v_job_411_ = v_reuseFailAlloc_419_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
lean_ctor_set_uint8(v_job_411_, sizeof(void*)*3, v_optional_389_);
lean_inc_ref(v_job_411_);
v___x_412_ = l_Lake_Job_toOpaque___redArg(v_job_411_);
v___x_413_ = lean_array_push(v___x_409_, v___x_412_);
v___x_414_ = lean_st_ref_set(v_registeredJobs_408_, v___x_413_);
lean_dec(v_registeredJobs_408_);
v___x_415_ = l_Lake_Job_renew___redArg(v_job_411_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_415_);
v___x_417_ = v___x_401_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_399_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object* v_inst_423_, lean_object* v_caption_424_, lean_object* v_x_425_, lean_object* v_optional_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
uint8_t v_optional_boxed_434_; lean_object* v_res_435_; 
v_optional_boxed_434_ = lean_unbox(v_optional_426_);
v_res_435_ = l_Lake_withRegisterJob___redArg(v_inst_423_, v_caption_424_, v_x_425_, v_optional_boxed_434_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object* v_00_u03b1_436_, lean_object* v_inst_437_, lean_object* v_caption_438_, lean_object* v_x_439_, uint8_t v_optional_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_a_449_; lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_473_; 
lean_inc_ref(v_a_445_);
v___x_448_ = l_Lake_ensureJob___redArg(v_inst_437_, v_x_439_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_a_450_ = lean_ctor_get(v___x_448_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_473_ == 0)
{
v___x_452_ = v___x_448_;
v_isShared_453_ = v_isSharedCheck_473_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_473_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_task_454_; lean_object* v_kind_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_471_; 
v_task_454_ = lean_ctor_get(v_a_449_, 0);
v_kind_455_ = lean_ctor_get(v_a_449_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_449_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v_a_449_, 2);
lean_dec(v_unused_472_);
v___x_457_ = v_a_449_;
v_isShared_458_ = v_isSharedCheck_471_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_kind_455_);
lean_inc(v_task_454_);
lean_dec(v_a_449_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_471_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_registeredJobs_459_; lean_object* v___x_460_; lean_object* v_job_462_; 
v_registeredJobs_459_ = lean_ctor_get(v_a_445_, 3);
lean_inc(v_registeredJobs_459_);
lean_dec_ref(v_a_445_);
v___x_460_ = lean_st_ref_take(v_registeredJobs_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 2, v_caption_438_);
v_job_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_task_454_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_kind_455_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_caption_438_);
v_job_462_ = v_reuseFailAlloc_470_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
lean_ctor_set_uint8(v_job_462_, sizeof(void*)*3, v_optional_440_);
lean_inc_ref(v_job_462_);
v___x_463_ = l_Lake_Job_toOpaque___redArg(v_job_462_);
v___x_464_ = lean_array_push(v___x_460_, v___x_463_);
v___x_465_ = lean_st_ref_set(v_registeredJobs_459_, v___x_464_);
lean_dec(v_registeredJobs_459_);
v___x_466_ = l_Lake_Job_renew___redArg(v_job_462_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_466_);
v___x_468_ = v___x_452_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_a_450_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object* v_00_u03b1_474_, lean_object* v_inst_475_, lean_object* v_caption_476_, lean_object* v_x_477_, lean_object* v_optional_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
uint8_t v_optional_boxed_486_; lean_object* v_res_487_; 
v_optional_boxed_486_ = lean_unbox(v_optional_478_);
v_res_487_ = l_Lake_withRegisterJob(v_00_u03b1_474_, v_inst_475_, v_caption_476_, v_x_477_, v_optional_boxed_486_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object* v_caption_488_, lean_object* v_job_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_task_493_; lean_object* v_kind_494_; lean_object* v_caption_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_task_493_ = lean_ctor_get(v_job_489_, 0);
v_kind_494_ = lean_ctor_get(v_job_489_, 1);
v_caption_495_ = lean_ctor_get(v_job_489_, 2);
v___x_496_ = lean_string_utf8_byte_size(v_caption_495_);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_nat_dec_eq(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec_ref(v_caption_488_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_job_489_);
lean_ctor_set(v___x_499_, 1, v_a_491_);
return v___x_499_;
}
else
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_514_; 
lean_inc(v_kind_494_);
lean_inc_ref(v_task_493_);
v_isSharedCheck_514_ = !lean_is_exclusive(v_job_489_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; 
v_unused_515_ = lean_ctor_get(v_job_489_, 2);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_job_489_, 1);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_job_489_, 0);
lean_dec(v_unused_517_);
v___x_501_ = v_job_489_;
v_isShared_502_ = v_isSharedCheck_514_;
goto v_resetjp_500_;
}
else
{
lean_dec(v_job_489_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_514_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_registeredJobs_503_; lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v_job_507_; 
v_registeredJobs_503_ = lean_ctor_get(v_a_490_, 3);
v___x_504_ = lean_st_ref_take(v_registeredJobs_503_);
v___x_505_ = 0;
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 2, v_caption_488_);
v_job_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_task_493_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_kind_494_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_caption_488_);
v_job_507_ = v_reuseFailAlloc_513_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_ctor_set_uint8(v_job_507_, sizeof(void*)*3, v___x_505_);
lean_inc_ref(v_job_507_);
v___x_508_ = l_Lake_Job_toOpaque___redArg(v_job_507_);
v___x_509_ = lean_array_push(v___x_504_, v___x_508_);
v___x_510_ = lean_st_ref_set(v_registeredJobs_503_, v___x_509_);
v___x_511_ = l_Lake_Job_renew___redArg(v_job_507_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_a_491_);
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object* v_caption_518_, lean_object* v_job_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lake_maybeRegisterJob___redArg(v_caption_518_, v_job_519_, v_a_520_, v_a_521_);
lean_dec_ref(v_a_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object* v_00_u03b1_524_, lean_object* v_caption_525_, lean_object* v_job_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_task_534_; lean_object* v_kind_535_; lean_object* v_caption_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_task_534_ = lean_ctor_get(v_job_526_, 0);
v_kind_535_ = lean_ctor_get(v_job_526_, 1);
v_caption_536_ = lean_ctor_get(v_job_526_, 2);
v___x_537_ = lean_string_utf8_byte_size(v_caption_536_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_dec_eq(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_dec_ref(v_caption_525_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_job_526_);
lean_ctor_set(v___x_540_, 1, v_a_532_);
return v___x_540_;
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_555_; 
lean_inc(v_kind_535_);
lean_inc_ref(v_task_534_);
v_isSharedCheck_555_ = !lean_is_exclusive(v_job_526_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; 
v_unused_556_ = lean_ctor_get(v_job_526_, 2);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_job_526_, 1);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_job_526_, 0);
lean_dec(v_unused_558_);
v___x_542_ = v_job_526_;
v_isShared_543_ = v_isSharedCheck_555_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_job_526_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_555_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_registeredJobs_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v_job_548_; 
v_registeredJobs_544_ = lean_ctor_get(v_a_531_, 3);
v___x_545_ = lean_st_ref_take(v_registeredJobs_544_);
v___x_546_ = 0;
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 2, v_caption_525_);
v_job_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_task_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_kind_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_caption_525_);
v_job_548_ = v_reuseFailAlloc_554_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_ctor_set_uint8(v_job_548_, sizeof(void*)*3, v___x_546_);
lean_inc_ref(v_job_548_);
v___x_549_ = l_Lake_Job_toOpaque___redArg(v_job_548_);
v___x_550_ = lean_array_push(v___x_545_, v___x_549_);
v___x_551_ = lean_st_ref_set(v_registeredJobs_544_, v___x_550_);
v___x_552_ = l_Lake_Job_renew___redArg(v_job_548_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_532_);
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object* v_00_u03b1_559_, lean_object* v_caption_560_, lean_object* v_job_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lake_maybeRegisterJob(v_00_u03b1_559_, v_caption_560_, v_job_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_569_;
}
}
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Fetch(builtin);
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
res = initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Job_Register(builtin);
}
#ifdef __cplusplus
}
#endif
