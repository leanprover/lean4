// Lean compiler output
// Module: Std.Time.Zoned
// Imports: public import Std.Time.Zoned.DateTime public import Std.Time.Zoned.ZoneRules public import Std.Time.Zoned.ZonedDateTime public import Std.Time.Zoned.Database
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
extern lean_object* l_Std_Time_PlainTime_midnight;
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_get_current_time();
lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_now___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_now___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now();
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now();
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now();
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_ofPlainDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofPlainDate___closed__0;
static lean_once_cell_t l_Std_Time_DateTime_ofPlainDate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofPlainDate___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now();
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDate___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate(lean_object*, lean_object*);
static const lean_array_object l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0_value;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Std_Time_PlainDateTime_now___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1000000000u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_get_current_time();
if (lean_obj_tag(v___x_4_) == 0)
{
lean_object* v_a_5_; lean_object* v___x_6_; 
v_a_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_a_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_6_) == 0)
{
lean_object* v_a_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_39_; 
v_a_7_ = lean_ctor_get(v___x_6_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_39_ == 0)
{
v___x_9_ = v___x_6_;
v_isShared_10_ = v_isSharedCheck_39_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_a_7_);
lean_dec(v___x_6_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_39_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___y_12_; lean_object* v_initialLocalTimeType_34_; lean_object* v_transitions_35_; lean_object* v___x_36_; 
v_initialLocalTimeType_34_ = lean_ctor_get(v_a_7_, 0);
lean_inc_ref(v_initialLocalTimeType_34_);
v_transitions_35_ = lean_ctor_get(v_a_7_, 1);
lean_inc_ref(v_transitions_35_);
lean_dec(v_a_7_);
lean_inc(v_a_5_);
v___x_36_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_35_, v_a_5_);
lean_dec_ref(v_transitions_35_);
if (lean_obj_tag(v___x_36_) == 0)
{
v___y_12_ = v_initialLocalTimeType_34_;
goto v___jp_11_;
}
else
{
lean_object* v_val_37_; lean_object* v_localTimeType_38_; 
lean_dec_ref(v_initialLocalTimeType_34_);
v_val_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_val_37_);
lean_dec_ref(v___x_36_);
v_localTimeType_38_ = lean_ctor_get(v_val_37_, 1);
lean_inc_ref(v_localTimeType_38_);
lean_dec(v_val_37_);
v___y_12_ = v_localTimeType_38_;
goto v___jp_11_;
}
v___jp_11_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_second_15_; lean_object* v_nano_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_second_22_; lean_object* v_nano_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_13_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_a_5_);
v___x_14_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_13_);
v_second_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_second_15_);
v_nano_16_ = lean_ctor_get(v___x_14_, 1);
lean_inc(v_nano_16_);
lean_dec_ref(v___x_14_);
v___x_17_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_12_);
lean_dec_ref(v___y_12_);
v___x_18_ = l_Std_Time_TimeZone_toSeconds(v___x_17_);
lean_dec_ref(v___x_17_);
v___x_19_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_20_ = lean_int_mul(v___x_18_, v___x_19_);
lean_dec(v___x_18_);
v___x_21_ = l_Std_Time_Duration_ofNanoseconds(v___x_20_);
lean_dec(v___x_20_);
v_second_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_second_22_);
v_nano_23_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_nano_23_);
lean_dec_ref(v___x_21_);
v___x_24_ = lean_int_mul(v_second_15_, v___x_19_);
lean_dec(v_second_15_);
v___x_25_ = lean_int_add(v___x_24_, v_nano_16_);
lean_dec(v_nano_16_);
lean_dec(v___x_24_);
v___x_26_ = lean_int_mul(v_second_22_, v___x_19_);
lean_dec(v_second_22_);
v___x_27_ = lean_int_add(v___x_26_, v_nano_23_);
lean_dec(v_nano_23_);
lean_dec(v___x_26_);
v___x_28_ = lean_int_add(v___x_25_, v___x_27_);
lean_dec(v___x_27_);
lean_dec(v___x_25_);
v___x_29_ = l_Std_Time_Duration_ofNanoseconds(v___x_28_);
lean_dec(v___x_28_);
v___x_30_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_29_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 0, v___x_30_);
v___x_32_ = v___x_9_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
lean_dec(v_a_5_);
v_a_40_ = lean_ctor_get(v___x_6_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_6_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_6_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
v_a_48_ = lean_ctor_get(v___x_4_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_4_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_4_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now___boxed(lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Time_PlainDateTime_now();
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now(){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_get_current_time();
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref(v___x_59_);
v___x_61_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_95_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_95_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_95_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_95_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___y_67_; lean_object* v_initialLocalTimeType_90_; lean_object* v_transitions_91_; lean_object* v___x_92_; 
v_initialLocalTimeType_90_ = lean_ctor_get(v_a_62_, 0);
lean_inc_ref(v_initialLocalTimeType_90_);
v_transitions_91_ = lean_ctor_get(v_a_62_, 1);
lean_inc_ref(v_transitions_91_);
lean_dec(v_a_62_);
lean_inc(v_a_60_);
v___x_92_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_91_, v_a_60_);
lean_dec_ref(v_transitions_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
v___y_67_ = v_initialLocalTimeType_90_;
goto v___jp_66_;
}
else
{
lean_object* v_val_93_; lean_object* v_localTimeType_94_; 
lean_dec_ref(v_initialLocalTimeType_90_);
v_val_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_val_93_);
lean_dec_ref(v___x_92_);
v_localTimeType_94_ = lean_ctor_get(v_val_93_, 1);
lean_inc_ref(v_localTimeType_94_);
lean_dec(v_val_93_);
v___y_67_ = v_localTimeType_94_;
goto v___jp_66_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_second_70_; lean_object* v_nano_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_second_77_; lean_object* v_nano_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_date_86_; lean_object* v___x_88_; 
v___x_68_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_a_60_);
v___x_69_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_68_);
v_second_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_second_70_);
v_nano_71_ = lean_ctor_get(v___x_69_, 1);
lean_inc(v_nano_71_);
lean_dec_ref(v___x_69_);
v___x_72_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_67_);
lean_dec_ref(v___y_67_);
v___x_73_ = l_Std_Time_TimeZone_toSeconds(v___x_72_);
lean_dec_ref(v___x_72_);
v___x_74_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_75_ = lean_int_mul(v___x_73_, v___x_74_);
lean_dec(v___x_73_);
v___x_76_ = l_Std_Time_Duration_ofNanoseconds(v___x_75_);
lean_dec(v___x_75_);
v_second_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_second_77_);
v_nano_78_ = lean_ctor_get(v___x_76_, 1);
lean_inc(v_nano_78_);
lean_dec_ref(v___x_76_);
v___x_79_ = lean_int_mul(v_second_70_, v___x_74_);
lean_dec(v_second_70_);
v___x_80_ = lean_int_add(v___x_79_, v_nano_71_);
lean_dec(v_nano_71_);
lean_dec(v___x_79_);
v___x_81_ = lean_int_mul(v_second_77_, v___x_74_);
lean_dec(v_second_77_);
v___x_82_ = lean_int_add(v___x_81_, v_nano_78_);
lean_dec(v_nano_78_);
lean_dec(v___x_81_);
v___x_83_ = lean_int_add(v___x_80_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_80_);
v___x_84_ = l_Std_Time_Duration_ofNanoseconds(v___x_83_);
lean_dec(v___x_83_);
v___x_85_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_84_);
v_date_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_date_86_);
lean_dec_ref(v___x_85_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v_date_86_);
v___x_88_ = v___x_64_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_date_86_);
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
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec(v_a_60_);
v_a_96_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_61_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_61_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_104_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_59_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_59_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now___boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Time_PlainDate_now();
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now(){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_get_current_time();
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref(v___x_115_);
v___x_117_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_151_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_151_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_151_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_151_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___y_123_; lean_object* v_initialLocalTimeType_146_; lean_object* v_transitions_147_; lean_object* v___x_148_; 
v_initialLocalTimeType_146_ = lean_ctor_get(v_a_118_, 0);
lean_inc_ref(v_initialLocalTimeType_146_);
v_transitions_147_ = lean_ctor_get(v_a_118_, 1);
lean_inc_ref(v_transitions_147_);
lean_dec(v_a_118_);
lean_inc(v_a_116_);
v___x_148_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_147_, v_a_116_);
lean_dec_ref(v_transitions_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
v___y_123_ = v_initialLocalTimeType_146_;
goto v___jp_122_;
}
else
{
lean_object* v_val_149_; lean_object* v_localTimeType_150_; 
lean_dec_ref(v_initialLocalTimeType_146_);
v_val_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_val_149_);
lean_dec_ref(v___x_148_);
v_localTimeType_150_ = lean_ctor_get(v_val_149_, 1);
lean_inc_ref(v_localTimeType_150_);
lean_dec(v_val_149_);
v___y_123_ = v_localTimeType_150_;
goto v___jp_122_;
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v_second_126_; lean_object* v_nano_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v_second_133_; lean_object* v_nano_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_time_142_; lean_object* v___x_144_; 
v___x_124_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_a_116_);
v___x_125_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_124_);
v_second_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_second_126_);
v_nano_127_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_nano_127_);
lean_dec_ref(v___x_125_);
v___x_128_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_123_);
lean_dec_ref(v___y_123_);
v___x_129_ = l_Std_Time_TimeZone_toSeconds(v___x_128_);
lean_dec_ref(v___x_128_);
v___x_130_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_131_ = lean_int_mul(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
v___x_132_ = l_Std_Time_Duration_ofNanoseconds(v___x_131_);
lean_dec(v___x_131_);
v_second_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_second_133_);
v_nano_134_ = lean_ctor_get(v___x_132_, 1);
lean_inc(v_nano_134_);
lean_dec_ref(v___x_132_);
v___x_135_ = lean_int_mul(v_second_126_, v___x_130_);
lean_dec(v_second_126_);
v___x_136_ = lean_int_add(v___x_135_, v_nano_127_);
lean_dec(v_nano_127_);
lean_dec(v___x_135_);
v___x_137_ = lean_int_mul(v_second_133_, v___x_130_);
lean_dec(v_second_133_);
v___x_138_ = lean_int_add(v___x_137_, v_nano_134_);
lean_dec(v_nano_134_);
lean_dec(v___x_137_);
v___x_139_ = lean_int_add(v___x_136_, v___x_138_);
lean_dec(v___x_138_);
lean_dec(v___x_136_);
v___x_140_ = l_Std_Time_Duration_ofNanoseconds(v___x_139_);
lean_dec(v___x_139_);
v___x_141_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_140_);
v_time_142_ = lean_ctor_get(v___x_141_, 1);
lean_inc_ref(v_time_142_);
lean_dec_ref(v___x_141_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v_time_142_);
v___x_144_ = v___x_120_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_time_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_dec(v_a_116_);
v_a_152_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_117_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_117_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_115_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_115_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now___boxed(lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_Time_PlainTime_now();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0(lean_object* v___x_170_, lean_object* v_tz_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_second_175_; lean_object* v_nano_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_second_181_; lean_object* v_nano_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_173_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_170_);
v___x_174_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_173_);
v_second_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_second_175_);
v_nano_176_ = lean_ctor_get(v___x_174_, 1);
lean_inc(v_nano_176_);
lean_dec_ref(v___x_174_);
v___x_177_ = l_Std_Time_TimeZone_toSeconds(v_tz_171_);
v___x_178_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_179_ = lean_int_mul(v___x_177_, v___x_178_);
lean_dec(v___x_177_);
v___x_180_ = l_Std_Time_Duration_ofNanoseconds(v___x_179_);
lean_dec(v___x_179_);
v_second_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_second_181_);
v_nano_182_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_nano_182_);
lean_dec_ref(v___x_180_);
v___x_183_ = lean_int_mul(v_second_175_, v___x_178_);
lean_dec(v_second_175_);
v___x_184_ = lean_int_add(v___x_183_, v_nano_176_);
lean_dec(v_nano_176_);
lean_dec(v___x_183_);
v___x_185_ = lean_int_mul(v_second_181_, v___x_178_);
lean_dec(v_second_181_);
v___x_186_ = lean_int_add(v___x_185_, v_nano_182_);
lean_dec(v_nano_182_);
lean_dec(v___x_185_);
v___x_187_ = lean_int_add(v___x_184_, v___x_186_);
lean_dec(v___x_186_);
lean_dec(v___x_184_);
v___x_188_ = l_Std_Time_Duration_ofNanoseconds(v___x_187_);
lean_dec(v___x_187_);
v___x_189_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0___boxed(lean_object* v___x_190_, lean_object* v_tz_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Time_DateTime_ofPlainDate___lam__0(v___x_190_, v_tz_191_, v_x_192_);
lean_dec_ref(v_tz_191_);
return v_res_193_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofPlainDate___closed__0(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(86400u);
v___x_195_ = lean_nat_to_int(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofPlainDate___closed__1(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_nat_to_int(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate(lean_object* v_pd_198_, lean_object* v_tz_199_){
_start:
{
lean_object* v_days_200_; lean_object* v___x_201_; lean_object* v_secs_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_days_200_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_pd_198_);
v___x_201_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDate___closed__0, &l_Std_Time_DateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDate___closed__0);
v_secs_202_ = lean_int_mul(v_days_200_, v___x_201_);
lean_dec(v_days_200_);
v___x_203_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDate___closed__1, &l_Std_Time_DateTime_ofPlainDate___closed__1_once, _init_l_Std_Time_DateTime_ofPlainDate___closed__1);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_secs_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
lean_inc_ref(v___x_204_);
v___f_205_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDate___lam__0___boxed), 3, 2);
lean_closure_set(v___f_205_, 0, v___x_204_);
lean_closure_set(v___f_205_, 1, v_tz_199_);
v___x_206_ = lean_mk_thunk(v___f_205_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_204_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg(lean_object* v_dt_208_){
_start:
{
lean_object* v_timestamp_209_; lean_object* v_second_210_; lean_object* v___x_211_; lean_object* v_days_212_; lean_object* v___x_213_; 
v_timestamp_209_ = lean_ctor_get(v_dt_208_, 0);
v_second_210_ = lean_ctor_get(v_timestamp_209_, 0);
v___x_211_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDate___closed__0, &l_Std_Time_DateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDate___closed__0);
v_days_212_ = lean_int_ediv(v_second_210_, v___x_211_);
v___x_213_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_days_212_);
lean_dec(v_days_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg___boxed(lean_object* v_dt_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Time_DateTime_toPlainDate___redArg(v_dt_214_);
lean_dec_ref(v_dt_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object* v_tz_216_, lean_object* v_dt_217_){
_start:
{
lean_object* v_timestamp_218_; lean_object* v_second_219_; lean_object* v___x_220_; lean_object* v_days_221_; lean_object* v___x_222_; 
v_timestamp_218_ = lean_ctor_get(v_dt_217_, 0);
v_second_219_ = lean_ctor_get(v_timestamp_218_, 0);
v___x_220_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDate___closed__0, &l_Std_Time_DateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDate___closed__0);
v_days_221_ = lean_int_ediv(v_second_219_, v___x_220_);
v___x_222_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_days_221_);
lean_dec(v_days_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object* v_tz_223_, lean_object* v_dt_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_Time_DateTime_toPlainDate(v_tz_223_, v_dt_224_);
lean_dec_ref(v_dt_224_);
lean_dec_ref(v_tz_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg(lean_object* v_dt_226_){
_start:
{
lean_object* v_date_227_; lean_object* v___x_228_; lean_object* v_time_229_; 
v_date_227_ = lean_ctor_get(v_dt_226_, 1);
v___x_228_ = lean_thunk_get_own(v_date_227_);
v_time_229_ = lean_ctor_get(v___x_228_, 1);
lean_inc_ref(v_time_229_);
lean_dec(v___x_228_);
return v_time_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg___boxed(lean_object* v_dt_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Time_DateTime_toPlainTime___redArg(v_dt_230_);
lean_dec_ref(v_dt_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object* v_tz_232_, lean_object* v_dt_233_){
_start:
{
lean_object* v_date_234_; lean_object* v___x_235_; lean_object* v_time_236_; 
v_date_234_ = lean_ctor_get(v_dt_233_, 1);
v___x_235_ = lean_thunk_get_own(v_date_234_);
v_time_236_ = lean_ctor_get(v___x_235_, 1);
lean_inc_ref(v_time_236_);
lean_dec(v___x_235_);
return v_time_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object* v_tz_237_, lean_object* v_dt_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Time_DateTime_toPlainTime(v_tz_237_, v_dt_238_);
lean_dec_ref(v_dt_238_);
lean_dec_ref(v_tz_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object* v_a_240_, lean_object* v_tz_241_, lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_second_245_; lean_object* v_nano_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_second_251_; lean_object* v_nano_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_243_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_a_240_);
v___x_244_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_243_);
v_second_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_second_245_);
v_nano_246_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_nano_246_);
lean_dec_ref(v___x_244_);
v___x_247_ = l_Std_Time_TimeZone_toSeconds(v_tz_241_);
v___x_248_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_249_ = lean_int_mul(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v___x_250_ = l_Std_Time_Duration_ofNanoseconds(v___x_249_);
lean_dec(v___x_249_);
v_second_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_second_251_);
v_nano_252_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_nano_252_);
lean_dec_ref(v___x_250_);
v___x_253_ = lean_int_mul(v_second_245_, v___x_248_);
lean_dec(v_second_245_);
v___x_254_ = lean_int_add(v___x_253_, v_nano_246_);
lean_dec(v_nano_246_);
lean_dec(v___x_253_);
v___x_255_ = lean_int_mul(v_second_251_, v___x_248_);
lean_dec(v_second_251_);
v___x_256_ = lean_int_add(v___x_255_, v_nano_252_);
lean_dec(v_nano_252_);
lean_dec(v___x_255_);
v___x_257_ = lean_int_add(v___x_254_, v___x_256_);
lean_dec(v___x_256_);
lean_dec(v___x_254_);
v___x_258_ = l_Std_Time_Duration_ofNanoseconds(v___x_257_);
lean_dec(v___x_257_);
v___x_259_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object* v_a_260_, lean_object* v_tz_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_Time_DateTime_now___lam__0(v_a_260_, v_tz_261_, v_x_262_);
lean_dec_ref(v_tz_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now(lean_object* v_tz_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_get_current_time();
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
lean_inc(v_a_267_);
v___f_271_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_271_, 0, v_a_267_);
lean_closure_set(v___f_271_, 1, v_tz_264_);
v___x_272_ = lean_mk_thunk(v___f_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_a_267_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_273_);
v___x_275_ = v___x_269_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_tz_264_);
v_a_278_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_266_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_266_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___boxed(lean_object* v_tz_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Time_DateTime_now(v_tz_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0(lean_object* v_a_289_, lean_object* v___y_290_, lean_object* v_x_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_second_294_; lean_object* v_nano_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_second_300_; lean_object* v_nano_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_292_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_a_289_);
v___x_293_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_292_);
v_second_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_second_294_);
v_nano_295_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_nano_295_);
lean_dec_ref(v___x_293_);
v___x_296_ = l_Std_Time_TimeZone_toSeconds(v___y_290_);
v___x_297_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_298_ = lean_int_mul(v___x_296_, v___x_297_);
lean_dec(v___x_296_);
v___x_299_ = l_Std_Time_Duration_ofNanoseconds(v___x_298_);
lean_dec(v___x_298_);
v_second_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_second_300_);
v_nano_301_ = lean_ctor_get(v___x_299_, 1);
lean_inc(v_nano_301_);
lean_dec_ref(v___x_299_);
v___x_302_ = lean_int_mul(v_second_294_, v___x_297_);
lean_dec(v_second_294_);
v___x_303_ = lean_int_add(v___x_302_, v_nano_295_);
lean_dec(v_nano_295_);
lean_dec(v___x_302_);
v___x_304_ = lean_int_mul(v_second_300_, v___x_297_);
lean_dec(v_second_300_);
v___x_305_ = lean_int_add(v___x_304_, v_nano_301_);
lean_dec(v_nano_301_);
lean_dec(v___x_304_);
v___x_306_ = lean_int_add(v___x_303_, v___x_305_);
lean_dec(v___x_305_);
lean_dec(v___x_303_);
v___x_307_ = l_Std_Time_Duration_ofNanoseconds(v___x_306_);
lean_dec(v___x_306_);
v___x_308_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0___boxed(lean_object* v_a_309_, lean_object* v___y_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Time_ZonedDateTime_now___lam__0(v_a_309_, v___y_310_, v_x_311_);
lean_dec_ref(v___y_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now(){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_get_current_time();
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v___x_314_);
v___x_316_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_334_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_334_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_334_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_334_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___y_322_; lean_object* v_initialLocalTimeType_329_; lean_object* v_transitions_330_; lean_object* v___x_331_; 
v_initialLocalTimeType_329_ = lean_ctor_get(v_a_317_, 0);
v_transitions_330_ = lean_ctor_get(v_a_317_, 1);
lean_inc(v_a_315_);
v___x_331_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_330_, v_a_315_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; 
lean_dec_ref(v___x_331_);
v___x_332_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_329_);
v___y_322_ = v___x_332_;
goto v___jp_321_;
}
else
{
lean_object* v_a_333_; 
v_a_333_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_331_);
v___y_322_ = v_a_333_;
goto v___jp_321_;
}
v___jp_321_:
{
lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_inc_ref(v___y_322_);
lean_inc(v_a_315_);
v___f_323_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_323_, 0, v_a_315_);
lean_closure_set(v___f_323_, 1, v___y_322_);
v___x_324_ = lean_mk_thunk(v___f_323_);
v___x_325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_a_315_);
lean_ctor_set(v___x_325_, 2, v_a_317_);
lean_ctor_set(v___x_325_, 3, v___y_322_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_325_);
v___x_327_ = v___x_319_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_a_315_);
v_a_335_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_316_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_316_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_314_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_314_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___boxed(lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_Time_ZonedDateTime_now();
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt(lean_object* v_id_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_get_current_time();
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_355_);
v___x_357_ = l_Std_Time_Database_defaultGetZoneRules(v_id_353_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_375_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_375_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_375_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_375_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___y_363_; lean_object* v_initialLocalTimeType_370_; lean_object* v_transitions_371_; lean_object* v___x_372_; 
v_initialLocalTimeType_370_ = lean_ctor_get(v_a_358_, 0);
v_transitions_371_ = lean_ctor_get(v_a_358_, 1);
lean_inc(v_a_356_);
v___x_372_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_371_, v_a_356_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
lean_dec_ref(v___x_372_);
v___x_373_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_370_);
v___y_363_ = v___x_373_;
goto v___jp_362_;
}
else
{
lean_object* v_a_374_; 
v_a_374_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_372_);
v___y_363_ = v_a_374_;
goto v___jp_362_;
}
v___jp_362_:
{
lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
lean_inc_ref(v___y_363_);
lean_inc(v_a_356_);
v___f_364_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_364_, 0, v_a_356_);
lean_closure_set(v___f_364_, 1, v___y_363_);
v___x_365_ = lean_mk_thunk(v___f_364_);
v___x_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_356_);
lean_ctor_set(v___x_366_, 2, v_a_358_);
lean_ctor_set(v___x_366_, 3, v___y_363_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_366_);
v___x_368_ = v___x_360_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_a_356_);
v_a_376_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_357_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_357_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref(v_id_353_);
v_a_384_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_355_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_355_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt___boxed(lean_object* v_id_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Time_ZonedDateTime_nowAt(v_id_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0(lean_object* v_tm_395_, lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_second_401_; lean_object* v_nano_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_second_405_; lean_object* v_nano_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_399_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_tm_395_);
v___x_400_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_399_);
v_second_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_second_401_);
v_nano_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc(v_nano_402_);
lean_dec_ref(v___x_400_);
v___x_403_ = lean_int_mul(v___x_396_, v___x_397_);
v___x_404_ = l_Std_Time_Duration_ofNanoseconds(v___x_403_);
lean_dec(v___x_403_);
v_second_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_second_405_);
v_nano_406_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_nano_406_);
lean_dec_ref(v___x_404_);
v___x_407_ = lean_int_mul(v_second_401_, v___x_397_);
lean_dec(v_second_401_);
v___x_408_ = lean_int_add(v___x_407_, v_nano_402_);
lean_dec(v_nano_402_);
lean_dec(v___x_407_);
v___x_409_ = lean_int_mul(v_second_405_, v___x_397_);
lean_dec(v_second_405_);
v___x_410_ = lean_int_add(v___x_409_, v_nano_406_);
lean_dec(v_nano_406_);
lean_dec(v___x_409_);
v___x_411_ = lean_int_add(v___x_408_, v___x_410_);
lean_dec(v___x_410_);
lean_dec(v___x_408_);
v___x_412_ = l_Std_Time_Duration_ofNanoseconds(v___x_411_);
lean_dec(v___x_411_);
v___x_413_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed(lean_object* v_tm_414_, lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v_x_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Time_ZonedDateTime_ofPlainDate___lam__0(v_tm_414_, v___x_415_, v___x_416_, v_x_417_);
lean_dec(v___x_416_);
lean_dec(v___x_415_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDate___lam__1(lean_object* v_second_419_, lean_object* v_t_420_){
_start:
{
lean_object* v_time_421_; uint8_t v___x_422_; 
v_time_421_ = lean_ctor_get(v_t_420_, 0);
v___x_422_ = lean_int_dec_le(v_second_419_, v_time_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed(lean_object* v_second_423_, lean_object* v_t_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Std_Time_ZonedDateTime_ofPlainDate___lam__1(v_second_423_, v_t_424_);
lean_dec_ref(v_t_424_);
lean_dec(v_second_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDate___closed__1, &l_Std_Time_DateTime_ofPlainDate___closed__1_once, _init_l_Std_Time_DateTime_ofPlainDate___closed__1);
v___x_428_ = lean_int_neg(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate(lean_object* v_pd_429_, lean_object* v_zr_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_tm_433_; lean_object* v___y_435_; lean_object* v_val_453_; lean_object* v_second_455_; lean_object* v_initialLocalTimeType_456_; lean_object* v_transitions_457_; lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_431_ = l_Std_Time_PlainTime_midnight;
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v_pd_429_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v_tm_433_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_432_);
v_second_455_ = lean_ctor_get(v_tm_433_, 0);
lean_inc(v_second_455_);
v_initialLocalTimeType_456_ = lean_ctor_get(v_zr_430_, 0);
v_transitions_457_ = lean_ctor_get(v_zr_430_, 1);
lean_inc(v_second_455_);
v___f_458_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(v___f_458_, 0, v_second_455_);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_458_, v_transitions_457_, v___x_459_);
if (lean_obj_tag(v___x_460_) == 1)
{
lean_object* v_val_461_; lean_object* v_next_462_; lean_object* v_time_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_last_466_; lean_object* v_localTimeType_467_; lean_object* v_gmtOffset_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_val_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref(v___x_460_);
v_next_462_ = lean_array_fget_borrowed(v_transitions_457_, v_val_461_);
v_time_463_ = lean_ctor_get(v_next_462_, 0);
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = lean_nat_sub(v_val_461_, v___x_464_);
lean_dec(v_val_461_);
v_last_466_ = lean_array_fget_borrowed(v_transitions_457_, v___x_465_);
lean_dec(v___x_465_);
v_localTimeType_467_ = lean_ctor_get(v_last_466_, 1);
v_gmtOffset_468_ = lean_ctor_get(v_localTimeType_467_, 0);
v___x_469_ = lean_nat_abs(v_gmtOffset_468_);
v___x_470_ = lean_nat_to_int(v___x_469_);
v___x_471_ = lean_int_sub(v_time_463_, v___x_470_);
lean_dec(v___x_470_);
v___x_472_ = lean_int_dec_lt(v_second_455_, v___x_471_);
lean_dec(v___x_471_);
lean_dec(v_second_455_);
if (v___x_472_ == 0)
{
lean_inc(v_next_462_);
v_val_453_ = v_next_462_;
goto v___jp_452_;
}
else
{
lean_inc(v_last_466_);
v_val_453_ = v_last_466_;
goto v___jp_452_;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
lean_dec(v___x_460_);
lean_dec(v_second_455_);
v___x_473_ = lean_array_get_size(v_transitions_457_);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_sub(v___x_473_, v___x_474_);
v___x_476_ = lean_nat_dec_lt(v___x_475_, v___x_473_);
if (v___x_476_ == 0)
{
lean_dec(v___x_475_);
lean_inc_ref(v_initialLocalTimeType_456_);
v___y_435_ = v_initialLocalTimeType_456_;
goto v___jp_434_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = lean_array_fget_borrowed(v_transitions_457_, v___x_475_);
lean_dec(v___x_475_);
lean_inc(v___x_477_);
v_val_453_ = v___x_477_;
goto v___jp_452_;
}
}
v___jp_434_:
{
lean_object* v_second_436_; lean_object* v_nano_437_; lean_object* v_tz_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_tm_448_; lean_object* v___f_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_second_436_ = lean_ctor_get(v_tm_433_, 0);
lean_inc(v_second_436_);
v_nano_437_ = lean_ctor_get(v_tm_433_, 1);
lean_inc(v_nano_437_);
lean_dec_ref(v_tm_433_);
v_tz_438_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_435_);
lean_dec_ref(v___y_435_);
v___x_439_ = l_Std_Time_TimeZone_toSeconds(v_tz_438_);
v___x_440_ = lean_int_neg(v___x_439_);
v___x_441_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDate___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0);
v___x_442_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_443_ = lean_int_mul(v_second_436_, v___x_442_);
lean_dec(v_second_436_);
v___x_444_ = lean_int_add(v___x_443_, v_nano_437_);
lean_dec(v_nano_437_);
lean_dec(v___x_443_);
v___x_445_ = lean_int_mul(v___x_440_, v___x_442_);
lean_dec(v___x_440_);
v___x_446_ = lean_int_add(v___x_445_, v___x_441_);
lean_dec(v___x_445_);
v___x_447_ = lean_int_add(v___x_444_, v___x_446_);
lean_dec(v___x_446_);
lean_dec(v___x_444_);
v_tm_448_ = l_Std_Time_Duration_ofNanoseconds(v___x_447_);
lean_dec(v___x_447_);
lean_inc_ref(v_tm_448_);
v___f_449_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed), 4, 3);
lean_closure_set(v___f_449_, 0, v_tm_448_);
lean_closure_set(v___f_449_, 1, v___x_439_);
lean_closure_set(v___f_449_, 2, v___x_442_);
v___x_450_ = lean_mk_thunk(v___f_449_);
v___x_451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v_tm_448_);
lean_ctor_set(v___x_451_, 2, v_zr_430_);
lean_ctor_set(v___x_451_, 3, v_tz_438_);
return v___x_451_;
}
v___jp_452_:
{
lean_object* v_localTimeType_454_; 
v_localTimeType_454_ = lean_ctor_get(v_val_453_, 1);
lean_inc_ref(v_localTimeType_454_);
lean_dec_ref(v_val_453_);
v___y_435_ = v_localTimeType_454_;
goto v___jp_434_;
}
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0));
v___x_481_ = lean_array_get_size(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1);
v___x_484_ = lean_nat_sub(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static uint8_t _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__1);
v___x_486_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2);
v___x_487_ = lean_nat_dec_lt(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__2);
v___x_489_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0));
v___x_490_ = lean_array_fget(v___x_489_, v___x_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone(lean_object* v_pd_491_, lean_object* v_zr_492_){
_start:
{
lean_object* v_offset_493_; lean_object* v_name_494_; lean_object* v_abbreviation_495_; uint8_t v_isDST_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v_tm_499_; lean_object* v_second_500_; uint8_t v___x_501_; uint8_t v___x_502_; lean_object* v_ltt_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___y_508_; lean_object* v_val_526_; lean_object* v___f_528_; lean_object* v___x_529_; 
v_offset_493_ = lean_ctor_get(v_zr_492_, 0);
v_name_494_ = lean_ctor_get(v_zr_492_, 1);
v_abbreviation_495_ = lean_ctor_get(v_zr_492_, 2);
v_isDST_496_ = lean_ctor_get_uint8(v_zr_492_, sizeof(void*)*3);
v___x_497_ = l_Std_Time_PlainTime_midnight;
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_pd_491_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v_tm_499_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_498_);
v_second_500_ = lean_ctor_get(v_tm_499_, 0);
lean_inc(v_second_500_);
v___x_501_ = 0;
v___x_502_ = 1;
lean_inc_ref(v_name_494_);
lean_inc_ref(v_abbreviation_495_);
lean_inc(v_offset_493_);
v_ltt_503_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_503_, 0, v_offset_493_);
lean_ctor_set(v_ltt_503_, 1, v_abbreviation_495_);
lean_ctor_set(v_ltt_503_, 2, v_name_494_);
lean_ctor_set_uint8(v_ltt_503_, sizeof(void*)*3, v_isDST_496_);
lean_ctor_set_uint8(v_ltt_503_, sizeof(void*)*3 + 1, v___x_501_);
lean_ctor_set_uint8(v_ltt_503_, sizeof(void*)*3 + 2, v___x_502_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0));
lean_inc_ref(v_ltt_503_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_ltt_503_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_inc(v_second_500_);
v___f_528_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(v___f_528_, 0, v_second_500_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_528_, v___x_505_, v___x_504_);
if (lean_obj_tag(v___x_529_) == 1)
{
lean_object* v_val_530_; lean_object* v_next_531_; lean_object* v_time_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_last_535_; lean_object* v_localTimeType_536_; lean_object* v_gmtOffset_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
lean_dec_ref(v_ltt_503_);
v_val_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_val_530_);
lean_dec_ref(v___x_529_);
v_next_531_ = lean_array_fget(v___x_505_, v_val_530_);
v_time_532_ = lean_ctor_get(v_next_531_, 0);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_sub(v_val_530_, v___x_533_);
lean_dec(v_val_530_);
v_last_535_ = lean_array_fget(v___x_505_, v___x_534_);
lean_dec(v___x_534_);
v_localTimeType_536_ = lean_ctor_get(v_last_535_, 1);
v_gmtOffset_537_ = lean_ctor_get(v_localTimeType_536_, 0);
v___x_538_ = lean_nat_abs(v_gmtOffset_537_);
v___x_539_ = lean_nat_to_int(v___x_538_);
v___x_540_ = lean_int_sub(v_time_532_, v___x_539_);
lean_dec(v___x_539_);
v___x_541_ = lean_int_dec_lt(v_second_500_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v_second_500_);
if (v___x_541_ == 0)
{
lean_dec(v_last_535_);
v_val_526_ = v_next_531_;
goto v___jp_525_;
}
else
{
lean_dec(v_next_531_);
v_val_526_ = v_last_535_;
goto v___jp_525_;
}
}
else
{
uint8_t v___x_542_; 
lean_dec(v___x_529_);
lean_dec(v_second_500_);
v___x_542_ = lean_uint8_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3);
if (v___x_542_ == 0)
{
v___y_508_ = v_ltt_503_;
goto v___jp_507_;
}
else
{
lean_object* v___x_543_; 
lean_dec_ref(v_ltt_503_);
v___x_543_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4);
v_val_526_ = v___x_543_;
goto v___jp_525_;
}
}
v___jp_507_:
{
lean_object* v_second_509_; lean_object* v_nano_510_; lean_object* v_tz_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_tm_521_; lean_object* v___f_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_second_509_ = lean_ctor_get(v_tm_499_, 0);
lean_inc(v_second_509_);
v_nano_510_ = lean_ctor_get(v_tm_499_, 1);
lean_inc(v_nano_510_);
lean_dec_ref(v_tm_499_);
v_tz_511_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_508_);
lean_dec_ref(v___y_508_);
v___x_512_ = l_Std_Time_TimeZone_toSeconds(v_tz_511_);
v___x_513_ = lean_int_neg(v___x_512_);
v___x_514_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDate___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0);
v___x_515_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_516_ = lean_int_mul(v_second_509_, v___x_515_);
lean_dec(v_second_509_);
v___x_517_ = lean_int_add(v___x_516_, v_nano_510_);
lean_dec(v_nano_510_);
lean_dec(v___x_516_);
v___x_518_ = lean_int_mul(v___x_513_, v___x_515_);
lean_dec(v___x_513_);
v___x_519_ = lean_int_add(v___x_518_, v___x_514_);
lean_dec(v___x_518_);
v___x_520_ = lean_int_add(v___x_517_, v___x_519_);
lean_dec(v___x_519_);
lean_dec(v___x_517_);
v_tm_521_ = l_Std_Time_Duration_ofNanoseconds(v___x_520_);
lean_dec(v___x_520_);
lean_inc_ref(v_tm_521_);
v___f_522_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed), 4, 3);
lean_closure_set(v___f_522_, 0, v_tm_521_);
lean_closure_set(v___f_522_, 1, v___x_512_);
lean_closure_set(v___f_522_, 2, v___x_515_);
v___x_523_ = lean_mk_thunk(v___f_522_);
v___x_524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v_tm_521_);
lean_ctor_set(v___x_524_, 2, v___x_506_);
lean_ctor_set(v___x_524_, 3, v_tz_511_);
return v___x_524_;
}
v___jp_525_:
{
lean_object* v_localTimeType_527_; 
v_localTimeType_527_ = lean_ctor_get(v_val_526_, 1);
lean_inc_ref(v_localTimeType_527_);
lean_dec_ref(v_val_526_);
v___y_508_ = v_localTimeType_527_;
goto v___jp_507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___boxed(lean_object* v_pd_544_, lean_object* v_zr_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Time_ZonedDateTime_ofPlainDateWithZone(v_pd_544_, v_zr_545_);
lean_dec_ref(v_zr_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate(lean_object* v_dt_547_){
_start:
{
lean_object* v_date_548_; lean_object* v___x_549_; lean_object* v_date_550_; 
v_date_548_ = lean_ctor_get(v_dt_547_, 0);
v___x_549_ = lean_thunk_get_own(v_date_548_);
v_date_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_date_550_);
lean_dec(v___x_549_);
return v_date_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate___boxed(lean_object* v_dt_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Time_ZonedDateTime_toPlainDate(v_dt_551_);
lean_dec_ref(v_dt_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime(lean_object* v_dt_553_){
_start:
{
lean_object* v_date_554_; lean_object* v___x_555_; lean_object* v_time_556_; 
v_date_554_ = lean_ctor_get(v_dt_553_, 0);
v___x_555_ = lean_thunk_get_own(v_date_554_);
v_time_556_ = lean_ctor_get(v___x_555_, 1);
lean_inc_ref(v_time_556_);
lean_dec(v___x_555_);
return v_time_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime___boxed(lean_object* v_dt_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Time_ZonedDateTime_toPlainTime(v_dt_557_);
lean_dec_ref(v_dt_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of(lean_object* v_pdt_559_, lean_object* v_id_560_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_Time_Database_defaultGetZoneRules(v_id_560_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_615_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_615_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_615_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_615_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_tm_567_; lean_object* v___y_569_; lean_object* v_val_590_; lean_object* v_second_592_; lean_object* v_initialLocalTimeType_593_; lean_object* v_transitions_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_tm_567_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_559_);
v_second_592_ = lean_ctor_get(v_tm_567_, 0);
lean_inc(v_second_592_);
v_initialLocalTimeType_593_ = lean_ctor_get(v_a_563_, 0);
v_transitions_594_ = lean_ctor_get(v_a_563_, 1);
lean_inc(v_second_592_);
v___f_595_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(v___f_595_, 0, v_second_592_);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_595_, v_transitions_594_, v___x_596_);
if (lean_obj_tag(v___x_597_) == 1)
{
lean_object* v_val_598_; lean_object* v_next_599_; lean_object* v_time_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_last_603_; lean_object* v_localTimeType_604_; lean_object* v_gmtOffset_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_val_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_val_598_);
lean_dec_ref(v___x_597_);
v_next_599_ = lean_array_fget_borrowed(v_transitions_594_, v_val_598_);
v_time_600_ = lean_ctor_get(v_next_599_, 0);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_sub(v_val_598_, v___x_601_);
lean_dec(v_val_598_);
v_last_603_ = lean_array_fget_borrowed(v_transitions_594_, v___x_602_);
lean_dec(v___x_602_);
v_localTimeType_604_ = lean_ctor_get(v_last_603_, 1);
v_gmtOffset_605_ = lean_ctor_get(v_localTimeType_604_, 0);
v___x_606_ = lean_nat_abs(v_gmtOffset_605_);
v___x_607_ = lean_nat_to_int(v___x_606_);
v___x_608_ = lean_int_sub(v_time_600_, v___x_607_);
lean_dec(v___x_607_);
v___x_609_ = lean_int_dec_lt(v_second_592_, v___x_608_);
lean_dec(v___x_608_);
lean_dec(v_second_592_);
if (v___x_609_ == 0)
{
lean_inc(v_next_599_);
v_val_590_ = v_next_599_;
goto v___jp_589_;
}
else
{
lean_inc(v_last_603_);
v_val_590_ = v_last_603_;
goto v___jp_589_;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
lean_dec(v___x_597_);
lean_dec(v_second_592_);
v___x_610_ = lean_array_get_size(v_transitions_594_);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_sub(v___x_610_, v___x_611_);
v___x_613_ = lean_nat_dec_lt(v___x_612_, v___x_610_);
if (v___x_613_ == 0)
{
lean_dec(v___x_612_);
lean_inc_ref(v_initialLocalTimeType_593_);
v___y_569_ = v_initialLocalTimeType_593_;
goto v___jp_568_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_array_fget_borrowed(v_transitions_594_, v___x_612_);
lean_dec(v___x_612_);
lean_inc(v___x_614_);
v_val_590_ = v___x_614_;
goto v___jp_589_;
}
}
v___jp_568_:
{
lean_object* v_second_570_; lean_object* v_nano_571_; lean_object* v_tz_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_tm_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v_second_570_ = lean_ctor_get(v_tm_567_, 0);
lean_inc(v_second_570_);
v_nano_571_ = lean_ctor_get(v_tm_567_, 1);
lean_inc(v_nano_571_);
lean_dec_ref(v_tm_567_);
v_tz_572_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_569_);
lean_dec_ref(v___y_569_);
v___x_573_ = l_Std_Time_TimeZone_toSeconds(v_tz_572_);
v___x_574_ = lean_int_neg(v___x_573_);
v___x_575_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDate___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0);
v___x_576_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_577_ = lean_int_mul(v_second_570_, v___x_576_);
lean_dec(v_second_570_);
v___x_578_ = lean_int_add(v___x_577_, v_nano_571_);
lean_dec(v_nano_571_);
lean_dec(v___x_577_);
v___x_579_ = lean_int_mul(v___x_574_, v___x_576_);
lean_dec(v___x_574_);
v___x_580_ = lean_int_add(v___x_579_, v___x_575_);
lean_dec(v___x_579_);
v___x_581_ = lean_int_add(v___x_578_, v___x_580_);
lean_dec(v___x_580_);
lean_dec(v___x_578_);
v_tm_582_ = l_Std_Time_Duration_ofNanoseconds(v___x_581_);
lean_dec(v___x_581_);
lean_inc_ref(v_tm_582_);
v___f_583_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed), 4, 3);
lean_closure_set(v___f_583_, 0, v_tm_582_);
lean_closure_set(v___f_583_, 1, v___x_573_);
lean_closure_set(v___f_583_, 2, v___x_576_);
v___x_584_ = lean_mk_thunk(v___f_583_);
v___x_585_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_tm_582_);
lean_ctor_set(v___x_585_, 2, v_a_563_);
lean_ctor_set(v___x_585_, 3, v_tz_572_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_585_);
v___x_587_ = v___x_565_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
v___jp_589_:
{
lean_object* v_localTimeType_591_; 
v_localTimeType_591_ = lean_ctor_get(v_val_590_, 1);
lean_inc_ref(v_localTimeType_591_);
lean_dec_ref(v_val_590_);
v___y_569_ = v_localTimeType_591_;
goto v___jp_568_;
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_pdt_559_);
v_a_616_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_562_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_562_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of___boxed(lean_object* v_pdt_624_, lean_object* v_id_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Time_ZonedDateTime_of(v_pdt_624_, v_id_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object* v_pdt_628_, lean_object* v_zr_629_){
_start:
{
lean_object* v_tm_630_; lean_object* v___y_632_; lean_object* v_val_647_; lean_object* v_second_649_; lean_object* v_initialLocalTimeType_650_; lean_object* v_transitions_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_tm_630_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_628_);
v_second_649_ = lean_ctor_get(v_tm_630_, 0);
lean_inc(v_second_649_);
v_initialLocalTimeType_650_ = lean_ctor_get(v_zr_629_, 0);
lean_inc_ref(v_initialLocalTimeType_650_);
v_transitions_651_ = lean_ctor_get(v_zr_629_, 1);
lean_inc_ref(v_transitions_651_);
lean_dec_ref(v_zr_629_);
lean_inc(v_second_649_);
v___f_652_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(v___f_652_, 0, v_second_649_);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_652_, v_transitions_651_, v___x_653_);
if (lean_obj_tag(v___x_654_) == 1)
{
lean_object* v_val_655_; lean_object* v_next_656_; lean_object* v_time_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_last_660_; lean_object* v_localTimeType_661_; lean_object* v_gmtOffset_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
lean_dec_ref(v_initialLocalTimeType_650_);
v_val_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v___x_654_);
v_next_656_ = lean_array_fget(v_transitions_651_, v_val_655_);
v_time_657_ = lean_ctor_get(v_next_656_, 0);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_nat_sub(v_val_655_, v___x_658_);
lean_dec(v_val_655_);
v_last_660_ = lean_array_fget(v_transitions_651_, v___x_659_);
lean_dec(v___x_659_);
lean_dec_ref(v_transitions_651_);
v_localTimeType_661_ = lean_ctor_get(v_last_660_, 1);
v_gmtOffset_662_ = lean_ctor_get(v_localTimeType_661_, 0);
v___x_663_ = lean_nat_abs(v_gmtOffset_662_);
v___x_664_ = lean_nat_to_int(v___x_663_);
v___x_665_ = lean_int_sub(v_time_657_, v___x_664_);
lean_dec(v___x_664_);
v___x_666_ = lean_int_dec_lt(v_second_649_, v___x_665_);
lean_dec(v___x_665_);
lean_dec(v_second_649_);
if (v___x_666_ == 0)
{
lean_dec(v_last_660_);
v_val_647_ = v_next_656_;
goto v___jp_646_;
}
else
{
lean_dec(v_next_656_);
v_val_647_ = v_last_660_;
goto v___jp_646_;
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
lean_dec(v___x_654_);
lean_dec(v_second_649_);
v___x_667_ = lean_array_get_size(v_transitions_651_);
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_nat_sub(v___x_667_, v___x_668_);
v___x_670_ = lean_nat_dec_lt(v___x_669_, v___x_667_);
if (v___x_670_ == 0)
{
lean_dec(v___x_669_);
lean_dec_ref(v_transitions_651_);
v___y_632_ = v_initialLocalTimeType_650_;
goto v___jp_631_;
}
else
{
lean_object* v___x_671_; 
lean_dec_ref(v_initialLocalTimeType_650_);
v___x_671_ = lean_array_fget(v_transitions_651_, v___x_669_);
lean_dec(v___x_669_);
lean_dec_ref(v_transitions_651_);
v_val_647_ = v___x_671_;
goto v___jp_646_;
}
}
v___jp_631_:
{
lean_object* v_second_633_; lean_object* v_nano_634_; lean_object* v_tz_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_tm_645_; 
v_second_633_ = lean_ctor_get(v_tm_630_, 0);
lean_inc(v_second_633_);
v_nano_634_ = lean_ctor_get(v_tm_630_, 1);
lean_inc(v_nano_634_);
lean_dec_ref(v_tm_630_);
v_tz_635_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_632_);
lean_dec_ref(v___y_632_);
v___x_636_ = l_Std_Time_TimeZone_toSeconds(v_tz_635_);
lean_dec_ref(v_tz_635_);
v___x_637_ = lean_int_neg(v___x_636_);
lean_dec(v___x_636_);
v___x_638_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDate___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0);
v___x_639_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_640_ = lean_int_mul(v_second_633_, v___x_639_);
lean_dec(v_second_633_);
v___x_641_ = lean_int_add(v___x_640_, v_nano_634_);
lean_dec(v_nano_634_);
lean_dec(v___x_640_);
v___x_642_ = lean_int_mul(v___x_637_, v___x_639_);
lean_dec(v___x_637_);
v___x_643_ = lean_int_add(v___x_642_, v___x_638_);
lean_dec(v___x_642_);
v___x_644_ = lean_int_add(v___x_641_, v___x_643_);
lean_dec(v___x_643_);
lean_dec(v___x_641_);
v_tm_645_ = l_Std_Time_Duration_ofNanoseconds(v___x_644_);
lean_dec(v___x_644_);
return v_tm_645_;
}
v___jp_646_:
{
lean_object* v_localTimeType_648_; 
v_localTimeType_648_ = lean_ctor_get(v_val_647_, 1);
lean_inc_ref(v_localTimeType_648_);
lean_dec_ref(v_val_647_);
v___y_632_ = v_localTimeType_648_;
goto v___jp_631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object* v_pdt_672_, lean_object* v_tz_673_){
_start:
{
lean_object* v_tm_674_; lean_object* v_second_675_; lean_object* v___x_676_; lean_object* v___y_678_; lean_object* v_val_693_; lean_object* v___x_695_; lean_object* v___f_696_; lean_object* v___x_697_; 
v_tm_674_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_672_);
v_second_675_ = lean_ctor_get(v_tm_674_, 0);
lean_inc(v_second_675_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_695_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0));
lean_inc(v_second_675_);
v___f_696_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(v___f_696_, 0, v_second_675_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_696_, v___x_695_, v___x_676_);
if (lean_obj_tag(v___x_697_) == 1)
{
lean_object* v_val_698_; lean_object* v_next_699_; lean_object* v_time_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_last_703_; lean_object* v_localTimeType_704_; lean_object* v_gmtOffset_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_val_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v___x_697_);
v_next_699_ = lean_array_fget(v___x_695_, v_val_698_);
v_time_700_ = lean_ctor_get(v_next_699_, 0);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_sub(v_val_698_, v___x_701_);
lean_dec(v_val_698_);
v_last_703_ = lean_array_fget(v___x_695_, v___x_702_);
lean_dec(v___x_702_);
v_localTimeType_704_ = lean_ctor_get(v_last_703_, 1);
v_gmtOffset_705_ = lean_ctor_get(v_localTimeType_704_, 0);
v___x_706_ = lean_nat_abs(v_gmtOffset_705_);
v___x_707_ = lean_nat_to_int(v___x_706_);
v___x_708_ = lean_int_sub(v_time_700_, v___x_707_);
lean_dec(v___x_707_);
v___x_709_ = lean_int_dec_lt(v_second_675_, v___x_708_);
lean_dec(v___x_708_);
lean_dec(v_second_675_);
if (v___x_709_ == 0)
{
lean_dec(v_last_703_);
v_val_693_ = v_next_699_;
goto v___jp_692_;
}
else
{
lean_dec(v_next_699_);
v_val_693_ = v_last_703_;
goto v___jp_692_;
}
}
else
{
uint8_t v___x_710_; 
lean_dec(v___x_697_);
lean_dec(v_second_675_);
v___x_710_ = lean_uint8_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3);
if (v___x_710_ == 0)
{
lean_object* v_offset_711_; lean_object* v_name_712_; lean_object* v_abbreviation_713_; uint8_t v_isDST_714_; uint8_t v___x_715_; uint8_t v___x_716_; lean_object* v_ltt_717_; 
v_offset_711_ = lean_ctor_get(v_tz_673_, 0);
v_name_712_ = lean_ctor_get(v_tz_673_, 1);
v_abbreviation_713_ = lean_ctor_get(v_tz_673_, 2);
v_isDST_714_ = lean_ctor_get_uint8(v_tz_673_, sizeof(void*)*3);
v___x_715_ = 0;
v___x_716_ = 1;
lean_inc_ref(v_name_712_);
lean_inc_ref(v_abbreviation_713_);
lean_inc(v_offset_711_);
v_ltt_717_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_717_, 0, v_offset_711_);
lean_ctor_set(v_ltt_717_, 1, v_abbreviation_713_);
lean_ctor_set(v_ltt_717_, 2, v_name_712_);
lean_ctor_set_uint8(v_ltt_717_, sizeof(void*)*3, v_isDST_714_);
lean_ctor_set_uint8(v_ltt_717_, sizeof(void*)*3 + 1, v___x_715_);
lean_ctor_set_uint8(v_ltt_717_, sizeof(void*)*3 + 2, v___x_716_);
v___y_678_ = v_ltt_717_;
goto v___jp_677_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4);
v_val_693_ = v___x_718_;
goto v___jp_692_;
}
}
v___jp_677_:
{
lean_object* v_second_679_; lean_object* v_nano_680_; lean_object* v_tz_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_tm_691_; 
v_second_679_ = lean_ctor_get(v_tm_674_, 0);
lean_inc(v_second_679_);
v_nano_680_ = lean_ctor_get(v_tm_674_, 1);
lean_inc(v_nano_680_);
lean_dec_ref(v_tm_674_);
v_tz_681_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_678_);
lean_dec_ref(v___y_678_);
v___x_682_ = l_Std_Time_TimeZone_toSeconds(v_tz_681_);
lean_dec_ref(v_tz_681_);
v___x_683_ = lean_int_neg(v___x_682_);
lean_dec(v___x_682_);
v___x_684_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDate___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0);
v___x_685_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_686_ = lean_int_mul(v_second_679_, v___x_685_);
lean_dec(v_second_679_);
v___x_687_ = lean_int_add(v___x_686_, v_nano_680_);
lean_dec(v_nano_680_);
lean_dec(v___x_686_);
v___x_688_ = lean_int_mul(v___x_683_, v___x_685_);
lean_dec(v___x_683_);
v___x_689_ = lean_int_add(v___x_688_, v___x_684_);
lean_dec(v___x_688_);
v___x_690_ = lean_int_add(v___x_687_, v___x_689_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
v_tm_691_ = l_Std_Time_Duration_ofNanoseconds(v___x_690_);
lean_dec(v___x_690_);
return v_tm_691_;
}
v___jp_692_:
{
lean_object* v_localTimeType_694_; 
v_localTimeType_694_ = lean_ctor_get(v_val_693_, 1);
lean_inc_ref(v_localTimeType_694_);
lean_dec_ref(v_val_693_);
v___y_678_ = v_localTimeType_694_;
goto v___jp_677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object* v_pdt_719_, lean_object* v_tz_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_Time_PlainDateTime_toTimestampWithZone(v_pdt_719_, v_tz_720_);
lean_dec_ref(v_tz_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object* v_dt_722_, lean_object* v_zr_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_tm_726_; lean_object* v___y_728_; lean_object* v_val_743_; lean_object* v_second_745_; lean_object* v_initialLocalTimeType_746_; lean_object* v_transitions_747_; lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_724_ = l_Std_Time_PlainTime_midnight;
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_dt_722_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v_tm_726_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_725_);
v_second_745_ = lean_ctor_get(v_tm_726_, 0);
lean_inc(v_second_745_);
v_initialLocalTimeType_746_ = lean_ctor_get(v_zr_723_, 0);
lean_inc_ref(v_initialLocalTimeType_746_);
v_transitions_747_ = lean_ctor_get(v_zr_723_, 1);
lean_inc_ref(v_transitions_747_);
lean_dec_ref(v_zr_723_);
lean_inc(v_second_745_);
v___f_748_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(v___f_748_, 0, v_second_745_);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_748_, v_transitions_747_, v___x_749_);
if (lean_obj_tag(v___x_750_) == 1)
{
lean_object* v_val_751_; lean_object* v_next_752_; lean_object* v_time_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_last_756_; lean_object* v_localTimeType_757_; lean_object* v_gmtOffset_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
lean_dec_ref(v_initialLocalTimeType_746_);
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec_ref(v___x_750_);
v_next_752_ = lean_array_fget(v_transitions_747_, v_val_751_);
v_time_753_ = lean_ctor_get(v_next_752_, 0);
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_sub(v_val_751_, v___x_754_);
lean_dec(v_val_751_);
v_last_756_ = lean_array_fget(v_transitions_747_, v___x_755_);
lean_dec(v___x_755_);
lean_dec_ref(v_transitions_747_);
v_localTimeType_757_ = lean_ctor_get(v_last_756_, 1);
v_gmtOffset_758_ = lean_ctor_get(v_localTimeType_757_, 0);
v___x_759_ = lean_nat_abs(v_gmtOffset_758_);
v___x_760_ = lean_nat_to_int(v___x_759_);
v___x_761_ = lean_int_sub(v_time_753_, v___x_760_);
lean_dec(v___x_760_);
v___x_762_ = lean_int_dec_lt(v_second_745_, v___x_761_);
lean_dec(v___x_761_);
lean_dec(v_second_745_);
if (v___x_762_ == 0)
{
lean_dec(v_last_756_);
v_val_743_ = v_next_752_;
goto v___jp_742_;
}
else
{
lean_dec(v_next_752_);
v_val_743_ = v_last_756_;
goto v___jp_742_;
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
lean_dec(v___x_750_);
lean_dec(v_second_745_);
v___x_763_ = lean_array_get_size(v_transitions_747_);
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_sub(v___x_763_, v___x_764_);
v___x_766_ = lean_nat_dec_lt(v___x_765_, v___x_763_);
if (v___x_766_ == 0)
{
lean_dec(v___x_765_);
lean_dec_ref(v_transitions_747_);
v___y_728_ = v_initialLocalTimeType_746_;
goto v___jp_727_;
}
else
{
lean_object* v___x_767_; 
lean_dec_ref(v_initialLocalTimeType_746_);
v___x_767_ = lean_array_fget(v_transitions_747_, v___x_765_);
lean_dec(v___x_765_);
lean_dec_ref(v_transitions_747_);
v_val_743_ = v___x_767_;
goto v___jp_742_;
}
}
v___jp_727_:
{
lean_object* v_second_729_; lean_object* v_nano_730_; lean_object* v_tz_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_tm_741_; 
v_second_729_ = lean_ctor_get(v_tm_726_, 0);
lean_inc(v_second_729_);
v_nano_730_ = lean_ctor_get(v_tm_726_, 1);
lean_inc(v_nano_730_);
lean_dec_ref(v_tm_726_);
v_tz_731_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_728_);
lean_dec_ref(v___y_728_);
v___x_732_ = l_Std_Time_TimeZone_toSeconds(v_tz_731_);
lean_dec_ref(v_tz_731_);
v___x_733_ = lean_int_neg(v___x_732_);
lean_dec(v___x_732_);
v___x_734_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDate___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0);
v___x_735_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_736_ = lean_int_mul(v_second_729_, v___x_735_);
lean_dec(v_second_729_);
v___x_737_ = lean_int_add(v___x_736_, v_nano_730_);
lean_dec(v_nano_730_);
lean_dec(v___x_736_);
v___x_738_ = lean_int_mul(v___x_733_, v___x_735_);
lean_dec(v___x_733_);
v___x_739_ = lean_int_add(v___x_738_, v___x_734_);
lean_dec(v___x_738_);
v___x_740_ = lean_int_add(v___x_737_, v___x_739_);
lean_dec(v___x_739_);
lean_dec(v___x_737_);
v_tm_741_ = l_Std_Time_Duration_ofNanoseconds(v___x_740_);
lean_dec(v___x_740_);
return v_tm_741_;
}
v___jp_742_:
{
lean_object* v_localTimeType_744_; 
v_localTimeType_744_ = lean_ctor_get(v_val_743_, 1);
lean_inc_ref(v_localTimeType_744_);
lean_dec_ref(v_val_743_);
v___y_728_ = v_localTimeType_744_;
goto v___jp_727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object* v_dt_768_, lean_object* v_tz_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_tm_772_; lean_object* v_second_773_; lean_object* v___x_774_; lean_object* v___y_776_; lean_object* v_val_791_; lean_object* v___x_793_; lean_object* v___f_794_; lean_object* v___x_795_; 
v___x_770_ = l_Std_Time_PlainTime_midnight;
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_dt_768_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v_tm_772_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_771_);
v_second_773_ = lean_ctor_get(v_tm_772_, 0);
lean_inc(v_second_773_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_793_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__0));
lean_inc(v_second_773_);
v___f_794_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(v___f_794_, 0, v_second_773_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_794_, v___x_793_, v___x_774_);
if (lean_obj_tag(v___x_795_) == 1)
{
lean_object* v_val_796_; lean_object* v_next_797_; lean_object* v_time_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v_last_801_; lean_object* v_localTimeType_802_; lean_object* v_gmtOffset_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_val_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_val_796_);
lean_dec_ref(v___x_795_);
v_next_797_ = lean_array_fget(v___x_793_, v_val_796_);
v_time_798_ = lean_ctor_get(v_next_797_, 0);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_sub(v_val_796_, v___x_799_);
lean_dec(v_val_796_);
v_last_801_ = lean_array_fget(v___x_793_, v___x_800_);
lean_dec(v___x_800_);
v_localTimeType_802_ = lean_ctor_get(v_last_801_, 1);
v_gmtOffset_803_ = lean_ctor_get(v_localTimeType_802_, 0);
v___x_804_ = lean_nat_abs(v_gmtOffset_803_);
v___x_805_ = lean_nat_to_int(v___x_804_);
v___x_806_ = lean_int_sub(v_time_798_, v___x_805_);
lean_dec(v___x_805_);
v___x_807_ = lean_int_dec_lt(v_second_773_, v___x_806_);
lean_dec(v___x_806_);
lean_dec(v_second_773_);
if (v___x_807_ == 0)
{
lean_dec(v_last_801_);
v_val_791_ = v_next_797_;
goto v___jp_790_;
}
else
{
lean_dec(v_next_797_);
v_val_791_ = v_last_801_;
goto v___jp_790_;
}
}
else
{
uint8_t v___x_808_; 
lean_dec(v___x_795_);
lean_dec(v_second_773_);
v___x_808_ = lean_uint8_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__3);
if (v___x_808_ == 0)
{
lean_object* v_offset_809_; lean_object* v_name_810_; lean_object* v_abbreviation_811_; uint8_t v_isDST_812_; uint8_t v___x_813_; uint8_t v___x_814_; lean_object* v_ltt_815_; 
v_offset_809_ = lean_ctor_get(v_tz_769_, 0);
v_name_810_ = lean_ctor_get(v_tz_769_, 1);
v_abbreviation_811_ = lean_ctor_get(v_tz_769_, 2);
v_isDST_812_ = lean_ctor_get_uint8(v_tz_769_, sizeof(void*)*3);
v___x_813_ = 0;
v___x_814_ = 1;
lean_inc_ref(v_name_810_);
lean_inc_ref(v_abbreviation_811_);
lean_inc(v_offset_809_);
v_ltt_815_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_815_, 0, v_offset_809_);
lean_ctor_set(v_ltt_815_, 1, v_abbreviation_811_);
lean_ctor_set(v_ltt_815_, 2, v_name_810_);
lean_ctor_set_uint8(v_ltt_815_, sizeof(void*)*3, v_isDST_812_);
lean_ctor_set_uint8(v_ltt_815_, sizeof(void*)*3 + 1, v___x_813_);
lean_ctor_set_uint8(v_ltt_815_, sizeof(void*)*3 + 2, v___x_814_);
v___y_776_ = v_ltt_815_;
goto v___jp_775_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4, &l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateWithZone___closed__4);
v_val_791_ = v___x_816_;
goto v___jp_790_;
}
}
v___jp_775_:
{
lean_object* v_second_777_; lean_object* v_nano_778_; lean_object* v_tz_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_tm_789_; 
v_second_777_ = lean_ctor_get(v_tm_772_, 0);
lean_inc(v_second_777_);
v_nano_778_ = lean_ctor_get(v_tm_772_, 1);
lean_inc(v_nano_778_);
lean_dec_ref(v_tm_772_);
v_tz_779_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_776_);
lean_dec_ref(v___y_776_);
v___x_780_ = l_Std_Time_TimeZone_toSeconds(v_tz_779_);
lean_dec_ref(v_tz_779_);
v___x_781_ = lean_int_neg(v___x_780_);
lean_dec(v___x_780_);
v___x_782_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDate___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDate___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDate___closed__0);
v___x_783_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_784_ = lean_int_mul(v_second_777_, v___x_783_);
lean_dec(v_second_777_);
v___x_785_ = lean_int_add(v___x_784_, v_nano_778_);
lean_dec(v_nano_778_);
lean_dec(v___x_784_);
v___x_786_ = lean_int_mul(v___x_781_, v___x_783_);
lean_dec(v___x_781_);
v___x_787_ = lean_int_add(v___x_786_, v___x_782_);
lean_dec(v___x_786_);
v___x_788_ = lean_int_add(v___x_785_, v___x_787_);
lean_dec(v___x_787_);
lean_dec(v___x_785_);
v_tm_789_ = l_Std_Time_Duration_ofNanoseconds(v___x_788_);
lean_dec(v___x_788_);
return v_tm_789_;
}
v___jp_790_:
{
lean_object* v_localTimeType_792_; 
v_localTimeType_792_ = lean_ctor_get(v_val_791_, 1);
lean_inc_ref(v_localTimeType_792_);
lean_dec_ref(v_val_791_);
v___y_776_ = v_localTimeType_792_;
goto v___jp_775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object* v_dt_817_, lean_object* v_tz_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_Time_PlainDate_toTimestampWithZone(v_dt_817_, v_tz_818_);
lean_dec_ref(v_tz_818_);
return v_res_819_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_DateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_DateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned(builtin);
}
#ifdef __cplusplus
}
#endif
