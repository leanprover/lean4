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
lean_object* lean_get_set_stdout(lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ensureJob___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_ensureJob___redArg___closed__0 = (const lean_object*)&l_Lake_ensureJob___redArg___closed__0_value;
static lean_once_cell_t l_Lake_ensureJob___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ensureJob___redArg___closed__1;
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
v_registeredJobs_133_ = lean_ctor_get(v_____do__lift_132_, 4);
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
v___x_206_ = lean_panic_fn_borrowed(v___x_205_, v_msg_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object* v___x_207_, lean_object* v_x_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lake_JobResult_prependLog___redArg(v___x_207_, v_x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object* v_val_210_, lean_object* v_val_211_, lean_object* v_a_x3f_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_get_set_stdout(v_val_210_);
lean_dec_ref(v___x_215_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_get_set_stderr(v_val_211_);
lean_dec_ref(v___x_217_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___y_213_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1___boxed(lean_object* v_val_219_, lean_object* v_val_220_, lean_object* v_a_x3f_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lake_ensureJob___redArg___lam__1(v_val_219_, v_val_220_, v_a_x3f_221_, v___y_222_);
lean_dec(v_a_x3f_221_);
return v_res_224_;
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
static lean_object* _init_l_Lake_ensureJob___redArg___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__0));
v___x_247_ = l_Lake_BuildTrace_nil(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = l_ByteArray_empty;
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
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
lean_object* v_iniPos_270_; lean_object* v_a_272_; lean_object* v___y_287_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_iniPos_270_ = lean_array_get_size(v_a_268_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__2, &l_Lake_ensureJob___redArg___closed__2_once, _init_l_Lake_ensureJob___redArg___closed__2);
v___x_320_ = lean_st_mk_ref(v___x_319_);
lean_inc(v___x_320_);
v___x_321_ = l_IO_FS_Stream_ofBuffer(v___x_320_);
lean_inc_ref(v___x_321_);
v___x_322_ = lean_get_set_stdout(v___x_321_);
v___x_323_ = lean_get_set_stderr(v___x_321_);
lean_inc_ref(v_a_267_);
lean_inc(v_a_266_);
lean_inc(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
v___x_324_ = lean_apply_7(v_x_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, lean_box(0));
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_a_329_; lean_object* v___x_330_; lean_object* v___y_332_; lean_object* v_data_347_; uint8_t v___x_348_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc_n(v_a_325_, 2);
v_a_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_324_, 2);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v_a_325_);
v___x_328_ = l_Lake_ensureJob___redArg___lam__1(v___x_322_, v___x_323_, v___x_327_, v_a_326_);
lean_dec_ref_known(v___x_327_, 1);
v_a_329_ = lean_ctor_get(v___x_328_, 1);
lean_inc(v_a_329_);
lean_dec_ref(v___x_328_);
v___x_330_ = lean_st_ref_get(v___x_320_);
lean_dec(v___x_320_);
v_data_347_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_data_347_);
lean_dec(v___x_330_);
v___x_348_ = lean_string_validate_utf8(v_data_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v_data_347_);
v___x_349_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__7, &l_Lake_ensureJob___redArg___closed__7_once, _init_l_Lake_ensureJob___redArg___closed__7);
v___x_350_ = l_panic___at___00Lake_ensureJob_spec__0(v___x_349_);
v___y_332_ = v___x_350_;
goto v___jp_331_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_string_from_utf8_unchecked(v_data_347_);
v___y_332_ = v___x_351_;
goto v___jp_331_;
}
v___jp_331_:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_string_utf8_byte_size(v___y_332_);
v___x_334_ = lean_nat_dec_eq(v___x_333_, v___x_318_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_335_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__3));
v___x_336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_336_, 0, v___y_332_);
lean_ctor_set(v___x_336_, 1, v___x_318_);
lean_ctor_set(v___x_336_, 2, v___x_333_);
v___x_337_ = l_String_Slice_trimAscii(v___x_336_);
v___x_338_ = l_String_Slice_toString(v___x_337_);
lean_dec_ref(v___x_337_);
v___x_339_ = lean_string_append(v___x_335_, v___x_338_);
lean_dec_ref(v___x_338_);
v___x_340_ = 1;
v___x_341_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*1, v___x_340_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_array_push(v_a_329_, v___x_341_);
v___x_344_ = l_Lake_ensureJob___redArg___lam__2(v_a_325_, v___x_342_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v___x_343_);
lean_dec_ref(v_a_263_);
v___y_287_ = v___x_344_;
goto v___jp_286_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref(v___y_332_);
v___x_345_ = lean_box(0);
v___x_346_ = l_Lake_ensureJob___redArg___lam__2(v_a_325_, v___x_345_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_329_);
lean_dec_ref(v_a_263_);
v___y_287_ = v___x_346_;
goto v___jp_286_;
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_a_355_; 
lean_dec(v___x_320_);
lean_dec_ref(v_a_263_);
v_a_352_ = lean_ctor_get(v___x_324_, 1);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_324_, 2);
v___x_353_ = lean_box(0);
v___x_354_ = l_Lake_ensureJob___redArg___lam__1(v___x_322_, v___x_323_, v___x_353_, v_a_352_);
v_a_355_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v_a_272_ = v_a_355_;
goto v___jp_271_;
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
lean_inc_ref(v_a_272_);
v___x_273_ = l_Array_shrink___redArg(v_a_272_, v_iniPos_270_);
v___x_274_ = lean_array_get_size(v_a_272_);
v___x_275_ = l_Array_extract___redArg(v_a_272_, v_iniPos_270_, v___x_274_);
lean_dec_ref(v_a_272_);
v___x_276_ = ((lean_object*)(l_panic___at___00Lake_ensureJob_spec__0___closed__0));
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = 0;
v___x_279_ = 0;
v___x_280_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__1, &l_Lake_ensureJob___redArg___closed__1_once, _init_l_Lake_ensureJob___redArg___closed__1);
v___x_281_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_281_, 0, v___x_275_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
lean_ctor_set(v___x_281_, 2, v___x_277_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*3, v___x_278_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*3 + 1, v___x_279_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_277_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_task_pure(v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_inst_261_);
lean_ctor_set(v___x_284_, 2, v___x_276_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*3, v___x_279_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_273_);
return v___x_285_;
}
v___jp_286_:
{
if (lean_obj_tag(v___y_287_) == 0)
{
lean_object* v_a_288_; lean_object* v_a_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_a_288_ = lean_ctor_get(v___y_287_, 0);
lean_inc(v_a_288_);
v_a_289_ = lean_ctor_get(v___y_287_, 1);
v___x_290_ = lean_array_get_size(v_a_289_);
v___x_291_ = lean_nat_dec_lt(v_iniPos_270_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_a_288_);
lean_dec(v_inst_261_);
return v___y_287_;
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_a_289_);
v_isSharedCheck_314_ = !lean_is_exclusive(v___y_287_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_315_ = lean_ctor_get(v___y_287_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v___y_287_, 0);
lean_dec(v_unused_316_);
v___x_293_ = v___y_287_;
v_isShared_294_ = v_isSharedCheck_314_;
goto v_resetjp_292_;
}
else
{
lean_dec(v___y_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_314_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v_task_295_; lean_object* v_caption_296_; uint8_t v_optional_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_312_; 
v_task_295_ = lean_ctor_get(v_a_288_, 0);
v_caption_296_ = lean_ctor_get(v_a_288_, 2);
v_optional_297_ = lean_ctor_get_uint8(v_a_288_, sizeof(void*)*3);
v_isSharedCheck_312_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v_a_288_, 1);
lean_dec(v_unused_313_);
v___x_299_ = v_a_288_;
v_isShared_300_ = v_isSharedCheck_312_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_caption_296_);
lean_inc(v_task_295_);
lean_dec(v_a_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_312_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___f_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
lean_inc(v_a_289_);
v___x_301_ = l_Array_shrink___redArg(v_a_289_, v_iniPos_270_);
v___x_302_ = l_Array_extract___redArg(v_a_289_, v_iniPos_270_, v___x_290_);
lean_dec(v_a_289_);
v___f_303_ = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(v___f_303_, 0, v___x_302_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_task_map(v___f_303_, v_task_295_, v___x_304_, v___x_291_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_inst_261_);
lean_ctor_set(v___x_299_, 0, v___x_305_);
v___x_307_ = v___x_299_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_inst_261_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_caption_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*3, v_optional_297_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_301_);
lean_ctor_set(v___x_293_, 0, v___x_307_);
v___x_309_ = v___x_293_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_301_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
else
{
lean_object* v_a_317_; 
v_a_317_ = lean_ctor_get(v___y_287_, 1);
lean_inc(v_a_317_);
lean_dec_ref_known(v___y_287_, 2);
v_a_272_ = v_a_317_;
goto v___jp_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___boxed(lean_object* v_inst_356_, lean_object* v_x_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lake_ensureJob___redArg(v_inst_356_, v_x_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob(lean_object* v_00_u03b1_366_, lean_object* v_inst_367_, lean_object* v_x_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lake_ensureJob___redArg(v_inst_367_, v_x_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___boxed(lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_x_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lake_ensureJob(v_00_u03b1_377_, v_inst_378_, v_x_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg(lean_object* v_inst_388_, lean_object* v_caption_389_, lean_object* v_x_390_, uint8_t v_optional_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_424_; 
v___x_399_ = l_Lake_ensureJob___redArg(v_inst_388_, v_x_390_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_a_401_ = lean_ctor_get(v___x_399_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_424_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_424_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_424_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_task_405_; lean_object* v_kind_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_422_; 
v_task_405_ = lean_ctor_get(v_a_400_, 0);
v_kind_406_ = lean_ctor_get(v_a_400_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_a_400_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v_a_400_, 2);
lean_dec(v_unused_423_);
v___x_408_ = v_a_400_;
v_isShared_409_ = v_isSharedCheck_422_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_kind_406_);
lean_inc(v_task_405_);
lean_dec(v_a_400_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_422_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_registeredJobs_410_; lean_object* v_job_412_; 
v_registeredJobs_410_ = lean_ctor_get(v_a_396_, 4);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 2, v_caption_389_);
v_job_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_task_405_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_kind_406_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_caption_389_);
v_job_412_ = v_reuseFailAlloc_421_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_ctor_set_uint8(v_job_412_, sizeof(void*)*3, v_optional_391_);
v___x_413_ = lean_st_ref_take(v_registeredJobs_410_);
lean_inc_ref(v_job_412_);
v___x_414_ = l_Lake_Job_toOpaque___redArg(v_job_412_);
v___x_415_ = lean_array_push(v___x_413_, v___x_414_);
v___x_416_ = lean_st_ref_put(v_registeredJobs_410_, v___x_415_);
v___x_417_ = l_Lake_Job_renew___redArg(v_job_412_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_417_);
v___x_419_ = v___x_403_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_a_401_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object* v_inst_425_, lean_object* v_caption_426_, lean_object* v_x_427_, lean_object* v_optional_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
uint8_t v_optional_boxed_436_; lean_object* v_res_437_; 
v_optional_boxed_436_ = lean_unbox(v_optional_428_);
v_res_437_ = l_Lake_withRegisterJob___redArg(v_inst_425_, v_caption_426_, v_x_427_, v_optional_boxed_436_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec(v_a_431_);
lean_dec(v_a_430_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob(lean_object* v_00_u03b1_438_, lean_object* v_inst_439_, lean_object* v_caption_440_, lean_object* v_x_441_, uint8_t v_optional_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; lean_object* v_a_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_475_; 
v___x_450_ = l_Lake_ensureJob___redArg(v_inst_439_, v_x_441_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_a_452_ = lean_ctor_get(v___x_450_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_475_ == 0)
{
v___x_454_ = v___x_450_;
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_task_456_; lean_object* v_kind_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_473_; 
v_task_456_ = lean_ctor_get(v_a_451_, 0);
v_kind_457_ = lean_ctor_get(v_a_451_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v_a_451_, 2);
lean_dec(v_unused_474_);
v___x_459_ = v_a_451_;
v_isShared_460_ = v_isSharedCheck_473_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_kind_457_);
lean_inc(v_task_456_);
lean_dec(v_a_451_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_473_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_registeredJobs_461_; lean_object* v_job_463_; 
v_registeredJobs_461_ = lean_ctor_get(v_a_447_, 4);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 2, v_caption_440_);
v_job_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_task_456_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_kind_457_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_caption_440_);
v_job_463_ = v_reuseFailAlloc_472_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
lean_ctor_set_uint8(v_job_463_, sizeof(void*)*3, v_optional_442_);
v___x_464_ = lean_st_ref_take(v_registeredJobs_461_);
lean_inc_ref(v_job_463_);
v___x_465_ = l_Lake_Job_toOpaque___redArg(v_job_463_);
v___x_466_ = lean_array_push(v___x_464_, v___x_465_);
v___x_467_ = lean_st_ref_put(v_registeredJobs_461_, v___x_466_);
v___x_468_ = l_Lake_Job_renew___redArg(v_job_463_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_468_);
v___x_470_ = v___x_454_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_a_452_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object* v_00_u03b1_476_, lean_object* v_inst_477_, lean_object* v_caption_478_, lean_object* v_x_479_, lean_object* v_optional_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
uint8_t v_optional_boxed_488_; lean_object* v_res_489_; 
v_optional_boxed_488_ = lean_unbox(v_optional_480_);
v_res_489_ = l_Lake_withRegisterJob(v_00_u03b1_476_, v_inst_477_, v_caption_478_, v_x_479_, v_optional_boxed_488_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
lean_dec(v_a_482_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg(lean_object* v_caption_490_, lean_object* v_job_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_task_495_; lean_object* v_kind_496_; lean_object* v_caption_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_task_495_ = lean_ctor_get(v_job_491_, 0);
v_kind_496_ = lean_ctor_get(v_job_491_, 1);
v_caption_497_ = lean_ctor_get(v_job_491_, 2);
v___x_498_ = lean_string_utf8_byte_size(v_caption_497_);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_nat_dec_eq(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec_ref(v_caption_490_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_job_491_);
lean_ctor_set(v___x_501_, 1, v_a_493_);
return v___x_501_;
}
else
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_516_; 
lean_inc(v_kind_496_);
lean_inc_ref(v_task_495_);
v_isSharedCheck_516_ = !lean_is_exclusive(v_job_491_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; lean_object* v_unused_518_; lean_object* v_unused_519_; 
v_unused_517_ = lean_ctor_get(v_job_491_, 2);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_job_491_, 1);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_job_491_, 0);
lean_dec(v_unused_519_);
v___x_503_ = v_job_491_;
v_isShared_504_ = v_isSharedCheck_516_;
goto v_resetjp_502_;
}
else
{
lean_dec(v_job_491_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_516_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_registeredJobs_505_; uint8_t v___x_506_; lean_object* v_job_508_; 
v_registeredJobs_505_ = lean_ctor_get(v_a_492_, 4);
v___x_506_ = 0;
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 2, v_caption_490_);
v_job_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_task_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_kind_496_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_caption_490_);
v_job_508_ = v_reuseFailAlloc_515_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_ctor_set_uint8(v_job_508_, sizeof(void*)*3, v___x_506_);
v___x_509_ = lean_st_ref_take(v_registeredJobs_505_);
lean_inc_ref(v_job_508_);
v___x_510_ = l_Lake_Job_toOpaque___redArg(v_job_508_);
v___x_511_ = lean_array_push(v___x_509_, v___x_510_);
v___x_512_ = lean_st_ref_put(v_registeredJobs_505_, v___x_511_);
v___x_513_ = l_Lake_Job_renew___redArg(v_job_508_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_a_493_);
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object* v_caption_520_, lean_object* v_job_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lake_maybeRegisterJob___redArg(v_caption_520_, v_job_521_, v_a_522_, v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob(lean_object* v_00_u03b1_526_, lean_object* v_caption_527_, lean_object* v_job_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_task_536_; lean_object* v_kind_537_; lean_object* v_caption_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_task_536_ = lean_ctor_get(v_job_528_, 0);
v_kind_537_ = lean_ctor_get(v_job_528_, 1);
v_caption_538_ = lean_ctor_get(v_job_528_, 2);
v___x_539_ = lean_string_utf8_byte_size(v_caption_538_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_nat_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_dec_ref(v_caption_527_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_job_528_);
lean_ctor_set(v___x_542_, 1, v_a_534_);
return v___x_542_;
}
else
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_557_; 
lean_inc(v_kind_537_);
lean_inc_ref(v_task_536_);
v_isSharedCheck_557_ = !lean_is_exclusive(v_job_528_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; lean_object* v_unused_560_; 
v_unused_558_ = lean_ctor_get(v_job_528_, 2);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_job_528_, 1);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_job_528_, 0);
lean_dec(v_unused_560_);
v___x_544_ = v_job_528_;
v_isShared_545_ = v_isSharedCheck_557_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_job_528_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_557_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_registeredJobs_546_; uint8_t v___x_547_; lean_object* v_job_549_; 
v_registeredJobs_546_ = lean_ctor_get(v_a_533_, 4);
v___x_547_ = 0;
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 2, v_caption_527_);
v_job_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_task_536_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_kind_537_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_caption_527_);
v_job_549_ = v_reuseFailAlloc_556_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_ctor_set_uint8(v_job_549_, sizeof(void*)*3, v___x_547_);
v___x_550_ = lean_st_ref_take(v_registeredJobs_546_);
lean_inc_ref(v_job_549_);
v___x_551_ = l_Lake_Job_toOpaque___redArg(v_job_549_);
v___x_552_ = lean_array_push(v___x_550_, v___x_551_);
v___x_553_ = lean_st_ref_put(v_registeredJobs_546_, v___x_552_);
v___x_554_ = l_Lake_Job_renew___redArg(v_job_549_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_a_534_);
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object* v_00_u03b1_561_, lean_object* v_caption_562_, lean_object* v_job_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lake_maybeRegisterJob(v_00_u03b1_561_, v_caption_562_, v_job_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_571_;
}
}
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
