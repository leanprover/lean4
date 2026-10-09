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
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 3, 3);
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
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*3 + 2, v___x_17_);
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
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 3, 3);
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
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*3 + 2, v___x_48_);
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
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 3, 3);
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
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 2, v___x_82_);
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
lean_object* l_Lake_registerJob___redArg(lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_caption_140_, lean_object* v_job_141_, uint8_t v_optional_142_){
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
LEAN_EXPORT void l_Lake_registerJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_137_ = stack[0].m_obj;
lean_object* v_inst_138_ = stack[1].m_obj;
lean_object* v_inst_139_ = stack[2].m_obj;
lean_object* v_caption_140_ = stack[3].m_obj;
lean_object* v_job_141_ = stack[4].m_obj;
uint8_t v_optional_142_ = stack[5].m_num;
lean_object* v_res_160_;
v_res_160_ = l_Lake_registerJob___redArg(v_inst_137_, v_inst_138_, v_inst_139_, v_caption_140_, v_job_141_, v_optional_142_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_Lake_registerJob___redArg___boxed(lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_caption_164_, lean_object* v_job_165_, lean_object* v_optional_166_){
_start:
{
uint8_t v_optional_boxed_167_; lean_object* v_res_168_; 
v_optional_boxed_167_ = lean_unbox(v_optional_166_);
v_res_168_ = l_Lake_registerJob___redArg(v_inst_161_, v_inst_162_, v_inst_163_, v_caption_164_, v_job_165_, v_optional_boxed_167_);
return v_res_168_;
}
}
lean_object* l_Lake_registerJob(lean_object* v_m_169_, lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_caption_174_, lean_object* v_job_175_, uint8_t v_optional_176_){
_start:
{
lean_object* v_toApplicative_177_; lean_object* v_task_178_; lean_object* v_kind_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_192_; 
v_toApplicative_177_ = lean_ctor_get(v_inst_171_, 0);
lean_inc_ref(v_toApplicative_177_);
v_task_178_ = lean_ctor_get(v_job_175_, 0);
v_kind_179_ = lean_ctor_get(v_job_175_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_job_175_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v_job_175_, 2);
lean_dec(v_unused_193_);
v___x_181_ = v_job_175_;
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_kind_179_);
lean_inc(v_task_178_);
lean_dec(v_job_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_toBind_183_; lean_object* v_toPure_184_; lean_object* v_job_186_; 
v_toBind_183_ = lean_ctor_get(v_inst_171_, 1);
lean_inc(v_toBind_183_);
lean_dec_ref(v_inst_171_);
v_toPure_184_ = lean_ctor_get(v_toApplicative_177_, 1);
lean_inc(v_toPure_184_);
lean_dec_ref(v_toApplicative_177_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 2, v_caption_174_);
v_job_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_task_178_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_kind_179_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_caption_174_);
v_job_186_ = v_reuseFailAlloc_191_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___x_190_; 
lean_ctor_set_uint8(v_job_186_, sizeof(void*)*3, v_optional_176_);
lean_inc_ref(v_job_186_);
v___f_187_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__0), 2, 1);
lean_closure_set(v___f_187_, 0, v_job_186_);
v___f_188_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__1), 3, 2);
lean_closure_set(v___f_188_, 0, v_job_186_);
lean_closure_set(v___f_188_, 1, v_toPure_184_);
lean_inc(v_toBind_183_);
v___f_189_ = lean_alloc_closure((void*)(l_Lake_registerJob___redArg___lam__2), 5, 4);
lean_closure_set(v___f_189_, 0, v___f_187_);
lean_closure_set(v___f_189_, 1, v_inst_172_);
lean_closure_set(v___f_189_, 2, v_toBind_183_);
lean_closure_set(v___f_189_, 3, v___f_188_);
v___x_190_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v_inst_173_, v___f_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT void l_Lake_registerJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_171_ = stack[2].m_obj;
lean_object* v_inst_172_ = stack[3].m_obj;
lean_object* v_inst_173_ = stack[4].m_obj;
lean_object* v_caption_174_ = stack[5].m_obj;
lean_object* v_job_175_ = stack[6].m_obj;
uint8_t v_optional_176_ = stack[7].m_num;
lean_object* v_res_194_;
v_res_194_ = l_Lake_registerJob(lean_box(0), lean_box(0), v_inst_171_, v_inst_172_, v_inst_173_, v_caption_174_, v_job_175_, v_optional_176_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lake_registerJob___boxed(lean_object* v_m_195_, lean_object* v_00_u03b1_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_caption_200_, lean_object* v_job_201_, lean_object* v_optional_202_){
_start:
{
uint8_t v_optional_boxed_203_; lean_object* v_res_204_; 
v_optional_boxed_203_ = lean_unbox(v_optional_202_);
v_res_204_ = l_Lake_registerJob(v_m_195_, v_00_u03b1_196_, v_inst_197_, v_inst_198_, v_inst_199_, v_caption_200_, v_job_201_, v_optional_boxed_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_ensureJob_spec__0(lean_object* v_msg_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_panic___at___00Lake_ensureJob_spec__0___closed__0));
v___x_208_ = lean_panic_fn_borrowed(v___x_207_, v_msg_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__0(lean_object* v___x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lake_JobResult_prependLog___redArg(v___x_209_, v_x_210_);
return v___x_211_;
}
}
lean_object* l_Lake_ensureJob___redArg___lam__1(lean_object* v_val_212_, lean_object* v_val_213_, lean_object* v_a_x3f_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_217_ = lean_get_set_stdout(v_val_212_);
lean_dec_ref(v___x_217_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_get_set_stderr(v_val_213_);
lean_dec_ref(v___x_219_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___y_215_);
return v___x_220_;
}
}
LEAN_EXPORT void l_Lake_ensureJob___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_212_ = stack[0].m_obj;
lean_object* v_val_213_ = stack[1].m_obj;
lean_object* v_a_x3f_214_ = stack[2].m_obj;
lean_object* v___y_215_ = stack[3].m_obj;
lean_object* v_res_221_;
v_res_221_ = l_Lake_ensureJob___redArg___lam__1(v_val_212_, v_val_213_, v_a_x3f_214_, v___y_215_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__1___boxed(lean_object* v_val_222_, lean_object* v_val_223_, lean_object* v_a_x3f_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lake_ensureJob___redArg___lam__1(v_val_222_, v_val_223_, v_a_x3f_224_, v___y_225_);
lean_dec(v_a_x3f_224_);
return v_res_227_;
}
}
lean_object* l_Lake_ensureJob___redArg___lam__2(lean_object* v_a_228_, lean_object* v_____r_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_a_228_);
lean_ctor_set(v___x_237_, 1, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT void l_Lake_ensureJob___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_228_ = stack[0].m_obj;
lean_object* v_____r_229_ = stack[1].m_obj;
lean_object* v___y_230_ = stack[2].m_obj;
lean_object* v___y_231_ = stack[3].m_obj;
lean_object* v___y_232_ = stack[4].m_obj;
lean_object* v___y_233_ = stack[5].m_obj;
lean_object* v___y_234_ = stack[6].m_obj;
lean_object* v___y_235_ = stack[7].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lake_ensureJob___redArg___lam__2(v_a_228_, v_____r_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___lam__2___boxed(lean_object* v_a_239_, lean_object* v_____r_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lake_ensureJob___redArg___lam__2(v_a_239_, v_____r_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_248_;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__0));
v___x_251_ = l_Lake_BuildTrace_nil(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = l_ByteArray_empty;
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lake_ensureJob___redArg___closed__7(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__6));
v___x_260_ = lean_unsigned_to_nat(46u);
v___x_261_ = lean_unsigned_to_nat(193u);
v___x_262_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__5));
v___x_263_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__4));
v___x_264_ = l_mkPanicMessageWithDecl(v___x_263_, v___x_262_, v___x_261_, v___x_260_, v___x_259_);
return v___x_264_;
}
}
lean_object* l_Lake_ensureJob___redArg(lean_object* v_inst_265_, lean_object* v_x_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_iniPos_274_; lean_object* v_a_276_; lean_object* v___y_291_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_iniPos_274_ = lean_array_get_size(v_a_272_);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__2, &l_Lake_ensureJob___redArg___closed__2_once, _init_l_Lake_ensureJob___redArg___closed__2);
v___x_324_ = lean_st_mk_ref(v___x_323_);
lean_inc(v___x_324_);
v___x_325_ = l_IO_FS_Stream_ofBuffer(v___x_324_);
lean_inc_ref(v___x_325_);
v___x_326_ = lean_get_set_stdout(v___x_325_);
v___x_327_ = lean_get_set_stderr(v___x_325_);
lean_inc_ref(v_a_271_);
lean_inc(v_a_270_);
lean_inc(v_a_269_);
lean_inc(v_a_268_);
lean_inc_ref(v_a_267_);
v___x_328_ = lean_apply_7(v_x_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, lean_box(0));
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___y_336_; lean_object* v_data_351_; uint8_t v___x_352_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_n(v_a_329_, 2);
v_a_330_ = lean_ctor_get(v___x_328_, 1);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_328_, 2);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v_a_329_);
v___x_332_ = l_Lake_ensureJob___redArg___lam__1(v___x_326_, v___x_327_, v___x_331_, v_a_330_);
lean_dec_ref_known(v___x_331_, 1);
v_a_333_ = lean_ctor_get(v___x_332_, 1);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_st_ref_get(v___x_324_);
lean_dec(v___x_324_);
v_data_351_ = lean_ctor_get(v___x_334_, 0);
lean_inc_ref(v_data_351_);
lean_dec(v___x_334_);
v___x_352_ = lean_string_validate_utf8(v_data_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec_ref(v_data_351_);
v___x_353_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__7, &l_Lake_ensureJob___redArg___closed__7_once, _init_l_Lake_ensureJob___redArg___closed__7);
v___x_354_ = l_panic___at___00Lake_ensureJob_spec__0(v___x_353_);
v___y_336_ = v___x_354_;
goto v___jp_335_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_string_from_utf8_unchecked(v_data_351_);
v___y_336_ = v___x_355_;
goto v___jp_335_;
}
v___jp_335_:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_string_utf8_byte_size(v___y_336_);
v___x_338_ = lean_nat_dec_eq(v___x_337_, v___x_322_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_339_ = ((lean_object*)(l_Lake_ensureJob___redArg___closed__3));
v___x_340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_340_, 0, v___y_336_);
lean_ctor_set(v___x_340_, 1, v___x_322_);
lean_ctor_set(v___x_340_, 2, v___x_337_);
v___x_341_ = l_String_Slice_trimAscii(v___x_340_);
v___x_342_ = l_String_Slice_toString(v___x_341_);
lean_dec_ref(v___x_341_);
v___x_343_ = lean_string_append(v___x_339_, v___x_342_);
lean_dec_ref(v___x_342_);
v___x_344_ = 1;
v___x_345_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*1, v___x_344_);
v___x_346_ = lean_box(0);
v___x_347_ = lean_array_push(v_a_333_, v___x_345_);
v___x_348_ = l_Lake_ensureJob___redArg___lam__2(v_a_329_, v___x_346_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v___x_347_);
lean_dec_ref(v_a_267_);
v___y_291_ = v___x_348_;
goto v___jp_290_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v___y_336_);
v___x_349_ = lean_box(0);
v___x_350_ = l_Lake_ensureJob___redArg___lam__2(v_a_329_, v___x_349_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_333_);
lean_dec_ref(v_a_267_);
v___y_291_ = v___x_350_;
goto v___jp_290_;
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_a_359_; 
lean_dec(v___x_324_);
lean_dec_ref(v_a_267_);
v_a_356_ = lean_ctor_get(v___x_328_, 1);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_328_, 2);
v___x_357_ = lean_box(0);
v___x_358_ = l_Lake_ensureJob___redArg___lam__1(v___x_326_, v___x_327_, v___x_357_, v_a_356_);
v_a_359_ = lean_ctor_get(v___x_358_, 1);
lean_inc(v_a_359_);
lean_dec_ref(v___x_358_);
v_a_276_ = v_a_359_;
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
lean_inc_ref(v_a_276_);
v___x_277_ = l_Array_shrink___redArg(v_a_276_, v_iniPos_274_);
v___x_278_ = lean_array_get_size(v_a_276_);
v___x_279_ = l_Array_extract___redArg(v_a_276_, v_iniPos_274_, v___x_278_);
lean_dec_ref(v_a_276_);
v___x_280_ = ((lean_object*)(l_panic___at___00Lake_ensureJob_spec__0___closed__0));
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = 0;
v___x_283_ = 0;
v___x_284_ = lean_obj_once(&l_Lake_ensureJob___redArg___closed__1, &l_Lake_ensureJob___redArg___closed__1_once, _init_l_Lake_ensureJob___redArg___closed__1);
v___x_285_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_285_, 0, v___x_279_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_ctor_set(v___x_285_, 2, v___x_281_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*3, v___x_282_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*3 + 1, v___x_283_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*3 + 2, v___x_283_);
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_281_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_task_pure(v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_inst_265_);
lean_ctor_set(v___x_288_, 2, v___x_280_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*3, v___x_283_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_277_);
return v___x_289_;
}
v___jp_290_:
{
if (lean_obj_tag(v___y_291_) == 0)
{
lean_object* v_a_292_; lean_object* v_a_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_a_292_ = lean_ctor_get(v___y_291_, 0);
lean_inc(v_a_292_);
v_a_293_ = lean_ctor_get(v___y_291_, 1);
v___x_294_ = lean_array_get_size(v_a_293_);
v___x_295_ = lean_nat_dec_lt(v_iniPos_274_, v___x_294_);
if (v___x_295_ == 0)
{
lean_dec(v_a_292_);
lean_dec(v_inst_265_);
return v___y_291_;
}
else
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_318_; 
lean_inc(v_a_293_);
v_isSharedCheck_318_ = !lean_is_exclusive(v___y_291_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; lean_object* v_unused_320_; 
v_unused_319_ = lean_ctor_get(v___y_291_, 1);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v___y_291_, 0);
lean_dec(v_unused_320_);
v___x_297_ = v___y_291_;
v_isShared_298_ = v_isSharedCheck_318_;
goto v_resetjp_296_;
}
else
{
lean_dec(v___y_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_318_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_task_299_; lean_object* v_caption_300_; uint8_t v_optional_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_316_; 
v_task_299_ = lean_ctor_get(v_a_292_, 0);
v_caption_300_ = lean_ctor_get(v_a_292_, 2);
v_optional_301_ = lean_ctor_get_uint8(v_a_292_, sizeof(void*)*3);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v_a_292_, 1);
lean_dec(v_unused_317_);
v___x_303_ = v_a_292_;
v_isShared_304_ = v_isSharedCheck_316_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_caption_300_);
lean_inc(v_task_299_);
lean_dec(v_a_292_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_316_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
lean_inc(v_a_293_);
v___x_305_ = l_Array_shrink___redArg(v_a_293_, v_iniPos_274_);
v___x_306_ = l_Array_extract___redArg(v_a_293_, v_iniPos_274_, v___x_294_);
lean_dec(v_a_293_);
v___f_307_ = lean_alloc_closure((void*)(l_Lake_ensureJob___redArg___lam__0), 2, 1);
lean_closure_set(v___f_307_, 0, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_task_map(v___f_307_, v_task_299_, v___x_308_, v___x_295_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_inst_265_);
lean_ctor_set(v___x_303_, 0, v___x_309_);
v___x_311_ = v___x_303_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_inst_265_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_caption_300_);
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*3, v_optional_301_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_305_);
lean_ctor_set(v___x_297_, 0, v___x_311_);
v___x_313_ = v___x_297_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_305_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
else
{
lean_object* v_a_321_; 
v_a_321_ = lean_ctor_get(v___y_291_, 1);
lean_inc(v_a_321_);
lean_dec_ref_known(v___y_291_, 2);
v_a_276_ = v_a_321_;
goto v___jp_275_;
}
}
}
}
LEAN_EXPORT void l_Lake_ensureJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_265_ = stack[0].m_obj;
lean_object* v_x_266_ = stack[1].m_obj;
lean_object* v_a_267_ = stack[2].m_obj;
lean_object* v_a_268_ = stack[3].m_obj;
lean_object* v_a_269_ = stack[4].m_obj;
lean_object* v_a_270_ = stack[5].m_obj;
lean_object* v_a_271_ = stack[6].m_obj;
lean_object* v_a_272_ = stack[7].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lake_ensureJob___redArg(v_inst_265_, v_x_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___redArg___boxed(lean_object* v_inst_361_, lean_object* v_x_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lake_ensureJob___redArg(v_inst_361_, v_x_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec(v_a_365_);
lean_dec(v_a_364_);
return v_res_370_;
}
}
lean_object* l_Lake_ensureJob(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_x_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lake_ensureJob___redArg(v_inst_372_, v_x_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT void l_Lake_ensureJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_372_ = stack[1].m_obj;
lean_object* v_x_373_ = stack[2].m_obj;
lean_object* v_a_374_ = stack[3].m_obj;
lean_object* v_a_375_ = stack[4].m_obj;
lean_object* v_a_376_ = stack[5].m_obj;
lean_object* v_a_377_ = stack[6].m_obj;
lean_object* v_a_378_ = stack[7].m_obj;
lean_object* v_a_379_ = stack[8].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lake_ensureJob(lean_box(0), v_inst_372_, v_x_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___boxed(lean_object* v_00_u03b1_383_, lean_object* v_inst_384_, lean_object* v_x_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lake_ensureJob(v_00_u03b1_383_, v_inst_384_, v_x_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
return v_res_393_;
}
}
lean_object* l_Lake_withRegisterJob___redArg(lean_object* v_inst_394_, lean_object* v_caption_395_, lean_object* v_x_396_, uint8_t v_optional_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_430_; 
v___x_405_ = l_Lake_ensureJob___redArg(v_inst_394_, v_x_396_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_a_407_ = lean_ctor_get(v___x_405_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_430_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_430_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_430_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_task_411_; lean_object* v_kind_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_428_; 
v_task_411_ = lean_ctor_get(v_a_406_, 0);
v_kind_412_ = lean_ctor_get(v_a_406_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v_a_406_, 2);
lean_dec(v_unused_429_);
v___x_414_ = v_a_406_;
v_isShared_415_ = v_isSharedCheck_428_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_kind_412_);
lean_inc(v_task_411_);
lean_dec(v_a_406_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_428_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_registeredJobs_416_; lean_object* v_job_418_; 
v_registeredJobs_416_ = lean_ctor_get(v_a_402_, 4);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 2, v_caption_395_);
v_job_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_task_411_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_kind_412_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_caption_395_);
v_job_418_ = v_reuseFailAlloc_427_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_ctor_set_uint8(v_job_418_, sizeof(void*)*3, v_optional_397_);
v___x_419_ = lean_st_ref_take(v_registeredJobs_416_);
lean_inc_ref(v_job_418_);
v___x_420_ = l_Lake_Job_toOpaque___redArg(v_job_418_);
v___x_421_ = lean_array_push(v___x_419_, v___x_420_);
v___x_422_ = lean_st_ref_put(v_registeredJobs_416_, v___x_421_);
v___x_423_ = l_Lake_Job_renew___redArg(v_job_418_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_423_);
v___x_425_ = v___x_409_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_a_407_);
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
}
LEAN_EXPORT void l_Lake_withRegisterJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_394_ = stack[0].m_obj;
lean_object* v_caption_395_ = stack[1].m_obj;
lean_object* v_x_396_ = stack[2].m_obj;
uint8_t v_optional_397_ = stack[3].m_num;
lean_object* v_a_398_ = stack[4].m_obj;
lean_object* v_a_399_ = stack[5].m_obj;
lean_object* v_a_400_ = stack[6].m_obj;
lean_object* v_a_401_ = stack[7].m_obj;
lean_object* v_a_402_ = stack[8].m_obj;
lean_object* v_a_403_ = stack[9].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_Lake_withRegisterJob___redArg(v_inst_394_, v_caption_395_, v_x_396_, v_optional_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___redArg___boxed(lean_object* v_inst_432_, lean_object* v_caption_433_, lean_object* v_x_434_, lean_object* v_optional_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
uint8_t v_optional_boxed_443_; lean_object* v_res_444_; 
v_optional_boxed_443_ = lean_unbox(v_optional_435_);
v_res_444_ = l_Lake_withRegisterJob___redArg(v_inst_432_, v_caption_433_, v_x_434_, v_optional_boxed_443_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec(v_a_438_);
lean_dec(v_a_437_);
return v_res_444_;
}
}
lean_object* l_Lake_withRegisterJob(lean_object* v_00_u03b1_445_, lean_object* v_inst_446_, lean_object* v_caption_447_, lean_object* v_x_448_, uint8_t v_optional_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; lean_object* v_a_458_; lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_482_; 
v___x_457_ = l_Lake_ensureJob___redArg(v_inst_446_, v_x_448_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_a_459_ = lean_ctor_get(v___x_457_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_482_ == 0)
{
v___x_461_ = v___x_457_;
v_isShared_462_ = v_isSharedCheck_482_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_482_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v_task_463_; lean_object* v_kind_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_480_; 
v_task_463_ = lean_ctor_get(v_a_458_, 0);
v_kind_464_ = lean_ctor_get(v_a_458_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_458_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_a_458_, 2);
lean_dec(v_unused_481_);
v___x_466_ = v_a_458_;
v_isShared_467_ = v_isSharedCheck_480_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_kind_464_);
lean_inc(v_task_463_);
lean_dec(v_a_458_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_480_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_registeredJobs_468_; lean_object* v_job_470_; 
v_registeredJobs_468_ = lean_ctor_get(v_a_454_, 4);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 2, v_caption_447_);
v_job_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_task_463_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_kind_464_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_caption_447_);
v_job_470_ = v_reuseFailAlloc_479_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
lean_ctor_set_uint8(v_job_470_, sizeof(void*)*3, v_optional_449_);
v___x_471_ = lean_st_ref_take(v_registeredJobs_468_);
lean_inc_ref(v_job_470_);
v___x_472_ = l_Lake_Job_toOpaque___redArg(v_job_470_);
v___x_473_ = lean_array_push(v___x_471_, v___x_472_);
v___x_474_ = lean_st_ref_put(v_registeredJobs_468_, v___x_473_);
v___x_475_ = l_Lake_Job_renew___redArg(v_job_470_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_475_);
v___x_477_ = v___x_461_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_a_459_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_withRegisterJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_446_ = stack[1].m_obj;
lean_object* v_caption_447_ = stack[2].m_obj;
lean_object* v_x_448_ = stack[3].m_obj;
uint8_t v_optional_449_ = stack[4].m_num;
lean_object* v_a_450_ = stack[5].m_obj;
lean_object* v_a_451_ = stack[6].m_obj;
lean_object* v_a_452_ = stack[7].m_obj;
lean_object* v_a_453_ = stack[8].m_obj;
lean_object* v_a_454_ = stack[9].m_obj;
lean_object* v_a_455_ = stack[10].m_obj;
lean_object* v_res_483_;
v_res_483_ = l_Lake_withRegisterJob(lean_box(0), v_inst_446_, v_caption_447_, v_x_448_, v_optional_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___boxed(lean_object* v_00_u03b1_484_, lean_object* v_inst_485_, lean_object* v_caption_486_, lean_object* v_x_487_, lean_object* v_optional_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
uint8_t v_optional_boxed_496_; lean_object* v_res_497_; 
v_optional_boxed_496_ = lean_unbox(v_optional_488_);
v_res_497_ = l_Lake_withRegisterJob(v_00_u03b1_484_, v_inst_485_, v_caption_486_, v_x_487_, v_optional_boxed_496_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec(v_a_491_);
lean_dec(v_a_490_);
return v_res_497_;
}
}
lean_object* l_Lake_maybeRegisterJob___redArg(lean_object* v_caption_498_, lean_object* v_job_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_task_503_; lean_object* v_kind_504_; lean_object* v_caption_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_task_503_ = lean_ctor_get(v_job_499_, 0);
v_kind_504_ = lean_ctor_get(v_job_499_, 1);
v_caption_505_ = lean_ctor_get(v_job_499_, 2);
v___x_506_ = lean_string_utf8_byte_size(v_caption_505_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_nat_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v_caption_498_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_job_499_);
lean_ctor_set(v___x_509_, 1, v_a_501_);
return v___x_509_;
}
else
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_524_; 
lean_inc(v_kind_504_);
lean_inc_ref(v_task_503_);
v_isSharedCheck_524_ = !lean_is_exclusive(v_job_499_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_525_ = lean_ctor_get(v_job_499_, 2);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_job_499_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_job_499_, 0);
lean_dec(v_unused_527_);
v___x_511_ = v_job_499_;
v_isShared_512_ = v_isSharedCheck_524_;
goto v_resetjp_510_;
}
else
{
lean_dec(v_job_499_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_524_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_registeredJobs_513_; uint8_t v___x_514_; lean_object* v_job_516_; 
v_registeredJobs_513_ = lean_ctor_get(v_a_500_, 4);
v___x_514_ = 0;
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 2, v_caption_498_);
v_job_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_task_503_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_kind_504_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_caption_498_);
v_job_516_ = v_reuseFailAlloc_523_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_ctor_set_uint8(v_job_516_, sizeof(void*)*3, v___x_514_);
v___x_517_ = lean_st_ref_take(v_registeredJobs_513_);
lean_inc_ref(v_job_516_);
v___x_518_ = l_Lake_Job_toOpaque___redArg(v_job_516_);
v___x_519_ = lean_array_push(v___x_517_, v___x_518_);
v___x_520_ = lean_st_ref_put(v_registeredJobs_513_, v___x_519_);
v___x_521_ = l_Lake_Job_renew___redArg(v_job_516_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_a_501_);
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_maybeRegisterJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_498_ = stack[0].m_obj;
lean_object* v_job_499_ = stack[1].m_obj;
lean_object* v_a_500_ = stack[2].m_obj;
lean_object* v_a_501_ = stack[3].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_Lake_maybeRegisterJob___redArg(v_caption_498_, v_job_499_, v_a_500_, v_a_501_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___redArg___boxed(lean_object* v_caption_529_, lean_object* v_job_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lake_maybeRegisterJob___redArg(v_caption_529_, v_job_530_, v_a_531_, v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_534_;
}
}
lean_object* l_Lake_maybeRegisterJob(lean_object* v_00_u03b1_535_, lean_object* v_caption_536_, lean_object* v_job_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_task_545_; lean_object* v_kind_546_; lean_object* v_caption_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_task_545_ = lean_ctor_get(v_job_537_, 0);
v_kind_546_ = lean_ctor_get(v_job_537_, 1);
v_caption_547_ = lean_ctor_get(v_job_537_, 2);
v___x_548_ = lean_string_utf8_byte_size(v_caption_547_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_nat_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec_ref(v_caption_536_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_job_537_);
lean_ctor_set(v___x_551_, 1, v_a_543_);
return v___x_551_;
}
else
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_566_; 
lean_inc(v_kind_546_);
lean_inc_ref(v_task_545_);
v_isSharedCheck_566_ = !lean_is_exclusive(v_job_537_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_567_ = lean_ctor_get(v_job_537_, 2);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_job_537_, 1);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_job_537_, 0);
lean_dec(v_unused_569_);
v___x_553_ = v_job_537_;
v_isShared_554_ = v_isSharedCheck_566_;
goto v_resetjp_552_;
}
else
{
lean_dec(v_job_537_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_566_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_registeredJobs_555_; uint8_t v___x_556_; lean_object* v_job_558_; 
v_registeredJobs_555_ = lean_ctor_get(v_a_542_, 4);
v___x_556_ = 0;
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v_caption_536_);
v_job_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_task_545_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_kind_546_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_caption_536_);
v_job_558_ = v_reuseFailAlloc_565_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_ctor_set_uint8(v_job_558_, sizeof(void*)*3, v___x_556_);
v___x_559_ = lean_st_ref_take(v_registeredJobs_555_);
lean_inc_ref(v_job_558_);
v___x_560_ = l_Lake_Job_toOpaque___redArg(v_job_558_);
v___x_561_ = lean_array_push(v___x_559_, v___x_560_);
v___x_562_ = lean_st_ref_put(v_registeredJobs_555_, v___x_561_);
v___x_563_ = l_Lake_Job_renew___redArg(v_job_558_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_a_543_);
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_maybeRegisterJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_536_ = stack[1].m_obj;
lean_object* v_job_537_ = stack[2].m_obj;
lean_object* v_a_538_ = stack[3].m_obj;
lean_object* v_a_539_ = stack[4].m_obj;
lean_object* v_a_540_ = stack[5].m_obj;
lean_object* v_a_541_ = stack[6].m_obj;
lean_object* v_a_542_ = stack[7].m_obj;
lean_object* v_a_543_ = stack[8].m_obj;
lean_object* v_res_570_;
v_res_570_ = l_Lake_maybeRegisterJob(lean_box(0), v_caption_536_, v_job_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lake_maybeRegisterJob___boxed(lean_object* v_00_u03b1_571_, lean_object* v_caption_572_, lean_object* v_job_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lake_maybeRegisterJob(v_00_u03b1_571_, v_caption_572_, v_job_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_581_;
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
