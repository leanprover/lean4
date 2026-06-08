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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_get_current_time();
lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
extern lean_object* l_Std_Time_PlainTime_midnight;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_now___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_now___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_now___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_now___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now();
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now();
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now();
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_ofLocalDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofLocalDate___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofLocalDate(lean_object*, lean_object*);
static const lean_array_object l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofLocalDateWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofLocalDateWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of___lam__0___boxed(lean_object*, lean_object*);
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
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_now___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1000000000u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now(){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_get_current_time();
if (lean_obj_tag(v___x_6_) == 0)
{
lean_object* v_a_7_; lean_object* v___x_8_; 
v_a_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_a_7_);
lean_dec_ref_known(v___x_6_, 1);
v___x_8_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_36_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_36_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_36_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_36_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___y_14_; lean_object* v_initialLocalTimeType_31_; lean_object* v_transitions_32_; lean_object* v___x_33_; 
v_initialLocalTimeType_31_ = lean_ctor_get(v_a_9_, 0);
lean_inc_ref(v_initialLocalTimeType_31_);
v_transitions_32_ = lean_ctor_get(v_a_9_, 1);
lean_inc_ref(v_transitions_32_);
lean_dec(v_a_9_);
v___x_33_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_32_, v_a_7_);
lean_dec_ref(v_transitions_32_);
if (lean_obj_tag(v___x_33_) == 0)
{
v___y_14_ = v_initialLocalTimeType_31_;
goto v___jp_13_;
}
else
{
lean_object* v_val_34_; lean_object* v_localTimeType_35_; 
lean_dec_ref(v_initialLocalTimeType_31_);
v_val_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v___x_33_, 1);
v_localTimeType_35_ = lean_ctor_get(v_val_34_, 1);
lean_inc_ref(v_localTimeType_35_);
lean_dec(v_val_34_);
v___y_14_ = v_localTimeType_35_;
goto v___jp_13_;
}
v___jp_13_:
{
lean_object* v___x_15_; lean_object* v_offset_16_; lean_object* v_second_17_; lean_object* v_nano_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_15_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_14_);
lean_dec_ref(v___y_14_);
v_offset_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_offset_16_);
lean_dec_ref(v___x_15_);
v_second_17_ = lean_ctor_get(v_a_7_, 0);
lean_inc(v_second_17_);
v_nano_18_ = lean_ctor_get(v_a_7_, 1);
lean_inc(v_nano_18_);
lean_dec(v_a_7_);
v___x_19_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_20_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_21_ = lean_int_mul(v_second_17_, v___x_20_);
lean_dec(v_second_17_);
v___x_22_ = lean_int_add(v___x_21_, v_nano_18_);
lean_dec(v_nano_18_);
lean_dec(v___x_21_);
v___x_23_ = lean_int_mul(v_offset_16_, v___x_20_);
lean_dec(v_offset_16_);
v___x_24_ = lean_int_add(v___x_23_, v___x_19_);
lean_dec(v___x_23_);
v___x_25_ = lean_int_add(v___x_22_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_22_);
v___x_26_ = l_Std_Time_Duration_ofNanoseconds(v___x_25_);
lean_dec(v___x_25_);
v___x_27_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_26_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 0, v___x_27_);
v___x_29_ = v___x_11_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
lean_dec(v_a_7_);
v_a_37_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_8_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_8_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_6_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_6_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_6_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now___boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Time_PlainDateTime_now();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now(){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_get_current_time();
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
lean_dec_ref_known(v___x_56_, 1);
v___x_58_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_87_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_87_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_87_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_87_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___y_64_; lean_object* v_initialLocalTimeType_82_; lean_object* v_transitions_83_; lean_object* v___x_84_; 
v_initialLocalTimeType_82_ = lean_ctor_get(v_a_59_, 0);
lean_inc_ref(v_initialLocalTimeType_82_);
v_transitions_83_ = lean_ctor_get(v_a_59_, 1);
lean_inc_ref(v_transitions_83_);
lean_dec(v_a_59_);
v___x_84_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_83_, v_a_57_);
lean_dec_ref(v_transitions_83_);
if (lean_obj_tag(v___x_84_) == 0)
{
v___y_64_ = v_initialLocalTimeType_82_;
goto v___jp_63_;
}
else
{
lean_object* v_val_85_; lean_object* v_localTimeType_86_; 
lean_dec_ref(v_initialLocalTimeType_82_);
v_val_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_val_85_);
lean_dec_ref_known(v___x_84_, 1);
v_localTimeType_86_ = lean_ctor_get(v_val_85_, 1);
lean_inc_ref(v_localTimeType_86_);
lean_dec(v_val_85_);
v___y_64_ = v_localTimeType_86_;
goto v___jp_63_;
}
v___jp_63_:
{
lean_object* v___x_65_; lean_object* v_offset_66_; lean_object* v_second_67_; lean_object* v_nano_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_date_78_; lean_object* v___x_80_; 
v___x_65_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_64_);
lean_dec_ref(v___y_64_);
v_offset_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_offset_66_);
lean_dec_ref(v___x_65_);
v_second_67_ = lean_ctor_get(v_a_57_, 0);
lean_inc(v_second_67_);
v_nano_68_ = lean_ctor_get(v_a_57_, 1);
lean_inc(v_nano_68_);
lean_dec(v_a_57_);
v___x_69_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_70_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_71_ = lean_int_mul(v_second_67_, v___x_70_);
lean_dec(v_second_67_);
v___x_72_ = lean_int_add(v___x_71_, v_nano_68_);
lean_dec(v_nano_68_);
lean_dec(v___x_71_);
v___x_73_ = lean_int_mul(v_offset_66_, v___x_70_);
lean_dec(v_offset_66_);
v___x_74_ = lean_int_add(v___x_73_, v___x_69_);
lean_dec(v___x_73_);
v___x_75_ = lean_int_add(v___x_72_, v___x_74_);
lean_dec(v___x_74_);
lean_dec(v___x_72_);
v___x_76_ = l_Std_Time_Duration_ofNanoseconds(v___x_75_);
lean_dec(v___x_75_);
v___x_77_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_76_);
v_date_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_date_78_);
lean_dec_ref(v___x_77_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v_date_78_);
v___x_80_ = v___x_61_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_date_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
lean_dec(v_a_57_);
v_a_88_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_58_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_58_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_56_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_56_);
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
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now___boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_Time_PlainDate_now();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now(){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_get_current_time();
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_107_, 1);
v___x_109_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_138_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_138_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_138_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_138_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___y_115_; lean_object* v_initialLocalTimeType_133_; lean_object* v_transitions_134_; lean_object* v___x_135_; 
v_initialLocalTimeType_133_ = lean_ctor_get(v_a_110_, 0);
lean_inc_ref(v_initialLocalTimeType_133_);
v_transitions_134_ = lean_ctor_get(v_a_110_, 1);
lean_inc_ref(v_transitions_134_);
lean_dec(v_a_110_);
v___x_135_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_134_, v_a_108_);
lean_dec_ref(v_transitions_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
v___y_115_ = v_initialLocalTimeType_133_;
goto v___jp_114_;
}
else
{
lean_object* v_val_136_; lean_object* v_localTimeType_137_; 
lean_dec_ref(v_initialLocalTimeType_133_);
v_val_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v___x_135_, 1);
v_localTimeType_137_ = lean_ctor_get(v_val_136_, 1);
lean_inc_ref(v_localTimeType_137_);
lean_dec(v_val_136_);
v___y_115_ = v_localTimeType_137_;
goto v___jp_114_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v_offset_117_; lean_object* v_second_118_; lean_object* v_nano_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_time_129_; lean_object* v___x_131_; 
v___x_116_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_115_);
lean_dec_ref(v___y_115_);
v_offset_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_offset_117_);
lean_dec_ref(v___x_116_);
v_second_118_ = lean_ctor_get(v_a_108_, 0);
lean_inc(v_second_118_);
v_nano_119_ = lean_ctor_get(v_a_108_, 1);
lean_inc(v_nano_119_);
lean_dec(v_a_108_);
v___x_120_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_121_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_122_ = lean_int_mul(v_second_118_, v___x_121_);
lean_dec(v_second_118_);
v___x_123_ = lean_int_add(v___x_122_, v_nano_119_);
lean_dec(v_nano_119_);
lean_dec(v___x_122_);
v___x_124_ = lean_int_mul(v_offset_117_, v___x_121_);
lean_dec(v_offset_117_);
v___x_125_ = lean_int_add(v___x_124_, v___x_120_);
lean_dec(v___x_124_);
v___x_126_ = lean_int_add(v___x_123_, v___x_125_);
lean_dec(v___x_125_);
lean_dec(v___x_123_);
v___x_127_ = l_Std_Time_Duration_ofNanoseconds(v___x_126_);
lean_dec(v___x_126_);
v___x_128_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_127_);
v_time_129_ = lean_ctor_get(v___x_128_, 1);
lean_inc_ref(v_time_129_);
lean_dec_ref(v___x_128_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v_time_129_);
v___x_131_ = v___x_112_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_time_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_108_);
v_a_139_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_109_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_109_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
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
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_107_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_107_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now___boxed(lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Time_PlainTime_now();
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0(lean_object* v___x_157_, lean_object* v_x_158_){
_start:
{
lean_inc_ref(v___x_157_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0___boxed(lean_object* v___x_159_, lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Time_DateTime_ofLocalDate___lam__0(v___x_159_, v_x_160_);
lean_dec_ref(v___x_159_);
return v_res_161_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofLocalDate___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_163_ = lean_int_neg(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate(lean_object* v_pd_164_, lean_object* v_tz_165_){
_start:
{
lean_object* v_offset_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_second_170_; lean_object* v_nano_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_189_; 
v_offset_166_ = lean_ctor_get(v_tz_165_, 0);
v___x_167_ = l_Std_Time_PlainTime_midnight;
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v_pd_164_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_inc_ref(v___x_168_);
v___x_169_ = l_Std_Time_PlainDateTime_toWallTime(v___x_168_);
v_second_170_ = lean_ctor_get(v___x_169_, 0);
v_nano_171_ = lean_ctor_get(v___x_169_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_189_ == 0)
{
v___x_173_ = v___x_169_;
v_isShared_174_ = v_isSharedCheck_189_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_nano_171_);
lean_inc(v_second_170_);
lean_dec(v___x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_189_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_tm_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___f_175_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_175_, 0, v___x_168_);
v___x_176_ = lean_int_neg(v_offset_166_);
v___x_177_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_178_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_179_ = lean_int_mul(v_second_170_, v___x_178_);
lean_dec(v_second_170_);
v___x_180_ = lean_int_add(v___x_179_, v_nano_171_);
lean_dec(v_nano_171_);
lean_dec(v___x_179_);
v___x_181_ = lean_int_mul(v___x_176_, v___x_178_);
lean_dec(v___x_176_);
v___x_182_ = lean_int_add(v___x_181_, v___x_177_);
lean_dec(v___x_181_);
v___x_183_ = lean_int_add(v___x_180_, v___x_182_);
lean_dec(v___x_182_);
lean_dec(v___x_180_);
v_tm_184_ = l_Std_Time_Duration_ofNanoseconds(v___x_183_);
lean_dec(v___x_183_);
v___x_185_ = lean_mk_thunk(v___f_175_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_185_);
lean_ctor_set(v___x_173_, 0, v_tm_184_);
v___x_187_ = v___x_173_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_tm_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___boxed(lean_object* v_pd_190_, lean_object* v_tz_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Time_DateTime_ofLocalDate(v_pd_190_, v_tz_191_);
lean_dec_ref(v_tz_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg(lean_object* v_dt_193_){
_start:
{
lean_object* v_date_194_; lean_object* v___x_195_; lean_object* v_date_196_; 
v_date_194_ = lean_ctor_get(v_dt_193_, 1);
v___x_195_ = lean_thunk_get_own(v_date_194_);
v_date_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc_ref(v_date_196_);
lean_dec(v___x_195_);
return v_date_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg___boxed(lean_object* v_dt_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_DateTime_toPlainDate___redArg(v_dt_197_);
lean_dec_ref(v_dt_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object* v_tz_199_, lean_object* v_dt_200_){
_start:
{
lean_object* v_date_201_; lean_object* v___x_202_; lean_object* v_date_203_; 
v_date_201_ = lean_ctor_get(v_dt_200_, 1);
v___x_202_ = lean_thunk_get_own(v_date_201_);
v_date_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc_ref(v_date_203_);
lean_dec(v___x_202_);
return v_date_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object* v_tz_204_, lean_object* v_dt_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Time_DateTime_toPlainDate(v_tz_204_, v_dt_205_);
lean_dec_ref(v_dt_205_);
lean_dec_ref(v_tz_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg(lean_object* v_dt_207_){
_start:
{
lean_object* v_date_208_; lean_object* v___x_209_; lean_object* v_time_210_; 
v_date_208_ = lean_ctor_get(v_dt_207_, 1);
v___x_209_ = lean_thunk_get_own(v_date_208_);
v_time_210_ = lean_ctor_get(v___x_209_, 1);
lean_inc_ref(v_time_210_);
lean_dec(v___x_209_);
return v_time_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg___boxed(lean_object* v_dt_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Time_DateTime_toPlainTime___redArg(v_dt_211_);
lean_dec_ref(v_dt_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object* v_tz_213_, lean_object* v_dt_214_){
_start:
{
lean_object* v_date_215_; lean_object* v___x_216_; lean_object* v_time_217_; 
v_date_215_ = lean_ctor_get(v_dt_214_, 1);
v___x_216_ = lean_thunk_get_own(v_date_215_);
v_time_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_time_217_);
lean_dec(v___x_216_);
return v_time_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object* v_tz_218_, lean_object* v_dt_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Time_DateTime_toPlainTime(v_tz_218_, v_dt_219_);
lean_dec_ref(v_dt_219_);
lean_dec_ref(v_tz_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object* v_tz_221_, lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_offset_224_; lean_object* v_second_225_; lean_object* v_nano_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_offset_224_ = lean_ctor_get(v_tz_221_, 0);
v_second_225_ = lean_ctor_get(v_a_222_, 0);
v_nano_226_ = lean_ctor_get(v_a_222_, 1);
v___x_227_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_228_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_229_ = lean_int_mul(v_second_225_, v___x_228_);
v___x_230_ = lean_int_add(v___x_229_, v_nano_226_);
lean_dec(v___x_229_);
v___x_231_ = lean_int_mul(v_offset_224_, v___x_228_);
v___x_232_ = lean_int_add(v___x_231_, v___x_227_);
lean_dec(v___x_231_);
v___x_233_ = lean_int_add(v___x_230_, v___x_232_);
lean_dec(v___x_232_);
lean_dec(v___x_230_);
v___x_234_ = l_Std_Time_Duration_ofNanoseconds(v___x_233_);
lean_dec(v___x_233_);
v___x_235_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object* v_tz_236_, lean_object* v_a_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Time_DateTime_now___lam__0(v_tz_236_, v_a_237_, v_x_238_);
lean_dec_ref(v_a_237_);
lean_dec_ref(v_tz_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now(lean_object* v_tz_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_get_current_time();
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_253_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_253_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_inc(v_a_243_);
v___f_247_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_247_, 0, v_tz_240_);
lean_closure_set(v___f_247_, 1, v_a_243_);
v___x_248_ = lean_mk_thunk(v___f_247_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_a_243_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_249_);
v___x_251_ = v___x_245_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_tz_240_);
v_a_254_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_242_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_242_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___boxed(lean_object* v_tz_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Time_DateTime_now(v_tz_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0(lean_object* v___y_265_, lean_object* v_a_266_, lean_object* v_x_267_){
_start:
{
lean_object* v_offset_268_; lean_object* v_second_269_; lean_object* v_nano_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_offset_268_ = lean_ctor_get(v___y_265_, 0);
v_second_269_ = lean_ctor_get(v_a_266_, 0);
v_nano_270_ = lean_ctor_get(v_a_266_, 1);
v___x_271_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_272_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_273_ = lean_int_mul(v_second_269_, v___x_272_);
v___x_274_ = lean_int_add(v___x_273_, v_nano_270_);
lean_dec(v___x_273_);
v___x_275_ = lean_int_mul(v_offset_268_, v___x_272_);
v___x_276_ = lean_int_add(v___x_275_, v___x_271_);
lean_dec(v___x_275_);
v___x_277_ = lean_int_add(v___x_274_, v___x_276_);
lean_dec(v___x_276_);
lean_dec(v___x_274_);
v___x_278_ = l_Std_Time_Duration_ofNanoseconds(v___x_277_);
lean_dec(v___x_277_);
v___x_279_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0___boxed(lean_object* v___y_280_, lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Time_ZonedDateTime_now___lam__0(v___y_280_, v_a_281_, v_x_282_);
lean_dec_ref(v_a_281_);
lean_dec_ref(v___y_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now(){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_get_current_time();
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_305_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_305_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_305_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_305_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___y_293_; lean_object* v_initialLocalTimeType_300_; lean_object* v_transitions_301_; lean_object* v___x_302_; 
v_initialLocalTimeType_300_ = lean_ctor_get(v_a_288_, 0);
v_transitions_301_ = lean_ctor_get(v_a_288_, 1);
v___x_302_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_301_, v_a_286_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
lean_dec_ref_known(v___x_302_, 1);
v___x_303_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_300_);
v___y_293_ = v___x_303_;
goto v___jp_292_;
}
else
{
lean_object* v_a_304_; 
v_a_304_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_302_, 1);
v___y_293_ = v_a_304_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
lean_inc(v_a_286_);
lean_inc_ref(v___y_293_);
v___f_294_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_294_, 0, v___y_293_);
lean_closure_set(v___f_294_, 1, v_a_286_);
v___x_295_ = lean_mk_thunk(v___f_294_);
v___x_296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_a_286_);
lean_ctor_set(v___x_296_, 2, v_a_288_);
lean_ctor_set(v___x_296_, 3, v___y_293_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_296_);
v___x_298_ = v___x_290_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_a_286_);
v_a_306_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_287_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_287_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_285_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_285_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___boxed(lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_Time_ZonedDateTime_now();
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt(lean_object* v_id_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_get_current_time();
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = l_Std_Time_Database_defaultGetZoneRules(v_id_324_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_346_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_346_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_346_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_346_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___y_334_; lean_object* v_initialLocalTimeType_341_; lean_object* v_transitions_342_; lean_object* v___x_343_; 
v_initialLocalTimeType_341_ = lean_ctor_get(v_a_329_, 0);
v_transitions_342_ = lean_ctor_get(v_a_329_, 1);
v___x_343_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_342_, v_a_327_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
lean_dec_ref_known(v___x_343_, 1);
v___x_344_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_341_);
v___y_334_ = v___x_344_;
goto v___jp_333_;
}
else
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_343_, 1);
v___y_334_ = v_a_345_;
goto v___jp_333_;
}
v___jp_333_:
{
lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
lean_inc(v_a_327_);
lean_inc_ref(v___y_334_);
v___f_335_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_335_, 0, v___y_334_);
lean_closure_set(v___f_335_, 1, v_a_327_);
v___x_336_ = lean_mk_thunk(v___f_335_);
v___x_337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_a_327_);
lean_ctor_set(v___x_337_, 2, v_a_329_);
lean_ctor_set(v___x_337_, 3, v___y_334_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_337_);
v___x_339_ = v___x_331_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_327_);
v_a_347_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_328_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_328_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_id_324_);
v_a_355_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_326_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_326_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt___boxed(lean_object* v_id_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Time_ZonedDateTime_nowAt(v_id_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofLocalDate(lean_object* v_pd_366_, lean_object* v_zr_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_wt_370_; lean_object* v_ltt_371_; lean_object* v_tz_372_; lean_object* v_offset_373_; lean_object* v_second_374_; lean_object* v_nano_375_; lean_object* v___f_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_368_ = l_Std_Time_PlainTime_midnight;
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_pd_366_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
lean_inc_ref(v___x_369_);
v_wt_370_ = l_Std_Time_PlainDateTime_toWallTime(v___x_369_);
lean_inc_ref(v_zr_367_);
v_ltt_371_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_367_, v_wt_370_);
v_tz_372_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_371_);
lean_dec_ref(v_ltt_371_);
v_offset_373_ = lean_ctor_get(v_tz_372_, 0);
lean_inc(v_offset_373_);
v_second_374_ = lean_ctor_get(v_wt_370_, 0);
lean_inc(v_second_374_);
v_nano_375_ = lean_ctor_get(v_wt_370_, 1);
lean_inc(v_nano_375_);
lean_dec_ref(v_wt_370_);
v___f_376_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_376_, 0, v___x_369_);
v___x_377_ = lean_mk_thunk(v___f_376_);
v___x_378_ = lean_int_neg(v_offset_373_);
lean_dec(v_offset_373_);
v___x_379_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_380_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_381_ = lean_int_mul(v_second_374_, v___x_380_);
lean_dec(v_second_374_);
v___x_382_ = lean_int_add(v___x_381_, v_nano_375_);
lean_dec(v_nano_375_);
lean_dec(v___x_381_);
v___x_383_ = lean_int_mul(v___x_378_, v___x_380_);
lean_dec(v___x_378_);
v___x_384_ = lean_int_add(v___x_383_, v___x_379_);
lean_dec(v___x_383_);
v___x_385_ = lean_int_add(v___x_382_, v___x_384_);
lean_dec(v___x_384_);
lean_dec(v___x_382_);
v___x_386_ = l_Std_Time_Duration_ofNanoseconds(v___x_385_);
lean_dec(v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_387_, 0, v___x_377_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
lean_ctor_set(v___x_387_, 2, v_zr_367_);
lean_ctor_set(v___x_387_, 3, v_tz_372_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofLocalDateWithZone(lean_object* v_pd_390_, lean_object* v_zr_391_){
_start:
{
lean_object* v_offset_392_; lean_object* v_name_393_; lean_object* v_abbreviation_394_; uint8_t v_isDST_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; uint8_t v___x_399_; lean_object* v_ltt_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_wt_403_; lean_object* v_ltt_404_; lean_object* v_tz_405_; lean_object* v_offset_406_; lean_object* v_second_407_; lean_object* v_nano_408_; lean_object* v___f_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_offset_392_ = lean_ctor_get(v_zr_391_, 0);
v_name_393_ = lean_ctor_get(v_zr_391_, 1);
v_abbreviation_394_ = lean_ctor_get(v_zr_391_, 2);
v_isDST_395_ = lean_ctor_get_uint8(v_zr_391_, sizeof(void*)*3);
v___x_396_ = l_Std_Time_PlainTime_midnight;
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_pd_390_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = 0;
v___x_399_ = 1;
lean_inc_ref(v_name_393_);
lean_inc_ref(v_abbreviation_394_);
lean_inc(v_offset_392_);
v_ltt_400_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_400_, 0, v_offset_392_);
lean_ctor_set(v_ltt_400_, 1, v_abbreviation_394_);
lean_ctor_set(v_ltt_400_, 2, v_name_393_);
lean_ctor_set_uint8(v_ltt_400_, sizeof(void*)*3, v_isDST_395_);
lean_ctor_set_uint8(v_ltt_400_, sizeof(void*)*3 + 1, v___x_398_);
lean_ctor_set_uint8(v_ltt_400_, sizeof(void*)*3 + 2, v___x_399_);
v___x_401_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0));
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_ltt_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
lean_inc_ref(v___x_397_);
v_wt_403_ = l_Std_Time_PlainDateTime_toWallTime(v___x_397_);
lean_inc_ref(v___x_402_);
v_ltt_404_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_402_, v_wt_403_);
v_tz_405_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_404_);
lean_dec_ref(v_ltt_404_);
v_offset_406_ = lean_ctor_get(v_tz_405_, 0);
lean_inc(v_offset_406_);
v_second_407_ = lean_ctor_get(v_wt_403_, 0);
lean_inc(v_second_407_);
v_nano_408_ = lean_ctor_get(v_wt_403_, 1);
lean_inc(v_nano_408_);
lean_dec_ref(v_wt_403_);
v___f_409_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_409_, 0, v___x_397_);
v___x_410_ = lean_mk_thunk(v___f_409_);
v___x_411_ = lean_int_neg(v_offset_406_);
lean_dec(v_offset_406_);
v___x_412_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_413_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_414_ = lean_int_mul(v_second_407_, v___x_413_);
lean_dec(v_second_407_);
v___x_415_ = lean_int_add(v___x_414_, v_nano_408_);
lean_dec(v_nano_408_);
lean_dec(v___x_414_);
v___x_416_ = lean_int_mul(v___x_411_, v___x_413_);
lean_dec(v___x_411_);
v___x_417_ = lean_int_add(v___x_416_, v___x_412_);
lean_dec(v___x_416_);
v___x_418_ = lean_int_add(v___x_415_, v___x_417_);
lean_dec(v___x_417_);
lean_dec(v___x_415_);
v___x_419_ = l_Std_Time_Duration_ofNanoseconds(v___x_418_);
lean_dec(v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_420_, 0, v___x_410_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
lean_ctor_set(v___x_420_, 2, v___x_402_);
lean_ctor_set(v___x_420_, 3, v_tz_405_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofLocalDateWithZone___boxed(lean_object* v_pd_421_, lean_object* v_zr_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Time_ZonedDateTime_ofLocalDateWithZone(v_pd_421_, v_zr_422_);
lean_dec_ref(v_zr_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate(lean_object* v_dt_424_){
_start:
{
lean_object* v_date_425_; lean_object* v___x_426_; lean_object* v_date_427_; 
v_date_425_ = lean_ctor_get(v_dt_424_, 0);
v___x_426_ = lean_thunk_get_own(v_date_425_);
v_date_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_date_427_);
lean_dec(v___x_426_);
return v_date_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate___boxed(lean_object* v_dt_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_Time_ZonedDateTime_toPlainDate(v_dt_428_);
lean_dec_ref(v_dt_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime(lean_object* v_dt_430_){
_start:
{
lean_object* v_date_431_; lean_object* v___x_432_; lean_object* v_time_433_; 
v_date_431_ = lean_ctor_get(v_dt_430_, 0);
v___x_432_ = lean_thunk_get_own(v_date_431_);
v_time_433_ = lean_ctor_get(v___x_432_, 1);
lean_inc_ref(v_time_433_);
lean_dec(v___x_432_);
return v_time_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime___boxed(lean_object* v_dt_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_Time_ZonedDateTime_toPlainTime(v_dt_434_);
lean_dec_ref(v_dt_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of___lam__0(lean_object* v_pdt_436_, lean_object* v_x_437_){
_start:
{
lean_inc_ref(v_pdt_436_);
return v_pdt_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of___lam__0___boxed(lean_object* v_pdt_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_Time_ZonedDateTime_of___lam__0(v_pdt_438_, v_x_439_);
lean_dec_ref(v_pdt_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of(lean_object* v_pdt_441_, lean_object* v_id_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_Time_Database_defaultGetZoneRules(v_id_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_470_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_470_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_470_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_470_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_wt_449_; lean_object* v_ltt_450_; lean_object* v_tz_451_; lean_object* v_offset_452_; lean_object* v_second_453_; lean_object* v_nano_454_; lean_object* v___f_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
lean_inc_ref(v_pdt_441_);
v_wt_449_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_441_);
lean_inc(v_a_445_);
v_ltt_450_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_a_445_, v_wt_449_);
v_tz_451_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_450_);
lean_dec_ref(v_ltt_450_);
v_offset_452_ = lean_ctor_get(v_tz_451_, 0);
lean_inc(v_offset_452_);
v_second_453_ = lean_ctor_get(v_wt_449_, 0);
lean_inc(v_second_453_);
v_nano_454_ = lean_ctor_get(v_wt_449_, 1);
lean_inc(v_nano_454_);
lean_dec_ref(v_wt_449_);
v___f_455_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_of___lam__0___boxed), 2, 1);
lean_closure_set(v___f_455_, 0, v_pdt_441_);
v___x_456_ = lean_mk_thunk(v___f_455_);
v___x_457_ = lean_int_neg(v_offset_452_);
lean_dec(v_offset_452_);
v___x_458_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_459_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_460_ = lean_int_mul(v_second_453_, v___x_459_);
lean_dec(v_second_453_);
v___x_461_ = lean_int_add(v___x_460_, v_nano_454_);
lean_dec(v_nano_454_);
lean_dec(v___x_460_);
v___x_462_ = lean_int_mul(v___x_457_, v___x_459_);
lean_dec(v___x_457_);
v___x_463_ = lean_int_add(v___x_462_, v___x_458_);
lean_dec(v___x_462_);
v___x_464_ = lean_int_add(v___x_461_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_461_);
v___x_465_ = l_Std_Time_Duration_ofNanoseconds(v___x_464_);
lean_dec(v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_466_, 0, v___x_456_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
lean_ctor_set(v___x_466_, 2, v_a_445_);
lean_ctor_set(v___x_466_, 3, v_tz_451_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_466_);
v___x_468_ = v___x_447_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_pdt_441_);
v_a_471_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_444_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_444_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of___boxed(lean_object* v_pdt_479_, lean_object* v_id_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Time_ZonedDateTime_of(v_pdt_479_, v_id_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object* v_pdt_483_, lean_object* v_zr_484_){
_start:
{
lean_object* v_wt_485_; lean_object* v_ltt_486_; lean_object* v_tz_487_; lean_object* v_offset_488_; lean_object* v_second_489_; lean_object* v_nano_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_wt_485_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_483_);
v_ltt_486_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_484_, v_wt_485_);
v_tz_487_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_486_);
lean_dec_ref(v_ltt_486_);
v_offset_488_ = lean_ctor_get(v_tz_487_, 0);
lean_inc(v_offset_488_);
lean_dec_ref(v_tz_487_);
v_second_489_ = lean_ctor_get(v_wt_485_, 0);
lean_inc(v_second_489_);
v_nano_490_ = lean_ctor_get(v_wt_485_, 1);
lean_inc(v_nano_490_);
lean_dec_ref(v_wt_485_);
v___x_491_ = lean_int_neg(v_offset_488_);
lean_dec(v_offset_488_);
v___x_492_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_493_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_494_ = lean_int_mul(v_second_489_, v___x_493_);
lean_dec(v_second_489_);
v___x_495_ = lean_int_add(v___x_494_, v_nano_490_);
lean_dec(v_nano_490_);
lean_dec(v___x_494_);
v___x_496_ = lean_int_mul(v___x_491_, v___x_493_);
lean_dec(v___x_491_);
v___x_497_ = lean_int_add(v___x_496_, v___x_492_);
lean_dec(v___x_496_);
v___x_498_ = lean_int_add(v___x_495_, v___x_497_);
lean_dec(v___x_497_);
lean_dec(v___x_495_);
v___x_499_ = l_Std_Time_Duration_ofNanoseconds(v___x_498_);
lean_dec(v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object* v_pdt_500_, lean_object* v_tz_501_){
_start:
{
lean_object* v_offset_502_; lean_object* v_name_503_; lean_object* v_abbreviation_504_; uint8_t v_isDST_505_; uint8_t v___x_506_; uint8_t v___x_507_; lean_object* v_ltt_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_wt_511_; lean_object* v_ltt_512_; lean_object* v_tz_513_; lean_object* v_offset_514_; lean_object* v_second_515_; lean_object* v_nano_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_offset_502_ = lean_ctor_get(v_tz_501_, 0);
v_name_503_ = lean_ctor_get(v_tz_501_, 1);
v_abbreviation_504_ = lean_ctor_get(v_tz_501_, 2);
v_isDST_505_ = lean_ctor_get_uint8(v_tz_501_, sizeof(void*)*3);
v___x_506_ = 0;
v___x_507_ = 1;
lean_inc_ref(v_name_503_);
lean_inc_ref(v_abbreviation_504_);
lean_inc(v_offset_502_);
v_ltt_508_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_508_, 0, v_offset_502_);
lean_ctor_set(v_ltt_508_, 1, v_abbreviation_504_);
lean_ctor_set(v_ltt_508_, 2, v_name_503_);
lean_ctor_set_uint8(v_ltt_508_, sizeof(void*)*3, v_isDST_505_);
lean_ctor_set_uint8(v_ltt_508_, sizeof(void*)*3 + 1, v___x_506_);
lean_ctor_set_uint8(v_ltt_508_, sizeof(void*)*3 + 2, v___x_507_);
v___x_509_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0));
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_ltt_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v_wt_511_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_500_);
v_ltt_512_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_510_, v_wt_511_);
v_tz_513_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_512_);
lean_dec_ref(v_ltt_512_);
v_offset_514_ = lean_ctor_get(v_tz_513_, 0);
lean_inc(v_offset_514_);
lean_dec_ref(v_tz_513_);
v_second_515_ = lean_ctor_get(v_wt_511_, 0);
lean_inc(v_second_515_);
v_nano_516_ = lean_ctor_get(v_wt_511_, 1);
lean_inc(v_nano_516_);
lean_dec_ref(v_wt_511_);
v___x_517_ = lean_int_neg(v_offset_514_);
lean_dec(v_offset_514_);
v___x_518_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_519_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_520_ = lean_int_mul(v_second_515_, v___x_519_);
lean_dec(v_second_515_);
v___x_521_ = lean_int_add(v___x_520_, v_nano_516_);
lean_dec(v_nano_516_);
lean_dec(v___x_520_);
v___x_522_ = lean_int_mul(v___x_517_, v___x_519_);
lean_dec(v___x_517_);
v___x_523_ = lean_int_add(v___x_522_, v___x_518_);
lean_dec(v___x_522_);
v___x_524_ = lean_int_add(v___x_521_, v___x_523_);
lean_dec(v___x_523_);
lean_dec(v___x_521_);
v___x_525_ = l_Std_Time_Duration_ofNanoseconds(v___x_524_);
lean_dec(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object* v_pdt_526_, lean_object* v_tz_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_PlainDateTime_toTimestampWithZone(v_pdt_526_, v_tz_527_);
lean_dec_ref(v_tz_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object* v_dt_529_, lean_object* v_zr_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_wt_533_; lean_object* v_ltt_534_; lean_object* v_tz_535_; lean_object* v_offset_536_; lean_object* v_second_537_; lean_object* v_nano_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_531_ = l_Std_Time_PlainTime_midnight;
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_dt_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v_wt_533_ = l_Std_Time_PlainDateTime_toWallTime(v___x_532_);
v_ltt_534_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_530_, v_wt_533_);
v_tz_535_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_534_);
lean_dec_ref(v_ltt_534_);
v_offset_536_ = lean_ctor_get(v_tz_535_, 0);
lean_inc(v_offset_536_);
lean_dec_ref(v_tz_535_);
v_second_537_ = lean_ctor_get(v_wt_533_, 0);
lean_inc(v_second_537_);
v_nano_538_ = lean_ctor_get(v_wt_533_, 1);
lean_inc(v_nano_538_);
lean_dec_ref(v_wt_533_);
v___x_539_ = lean_int_neg(v_offset_536_);
lean_dec(v_offset_536_);
v___x_540_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_541_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_542_ = lean_int_mul(v_second_537_, v___x_541_);
lean_dec(v_second_537_);
v___x_543_ = lean_int_add(v___x_542_, v_nano_538_);
lean_dec(v_nano_538_);
lean_dec(v___x_542_);
v___x_544_ = lean_int_mul(v___x_539_, v___x_541_);
lean_dec(v___x_539_);
v___x_545_ = lean_int_add(v___x_544_, v___x_540_);
lean_dec(v___x_544_);
v___x_546_ = lean_int_add(v___x_543_, v___x_545_);
lean_dec(v___x_545_);
lean_dec(v___x_543_);
v___x_547_ = l_Std_Time_Duration_ofNanoseconds(v___x_546_);
lean_dec(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object* v_dt_548_, lean_object* v_tz_549_){
_start:
{
lean_object* v_offset_550_; lean_object* v_name_551_; lean_object* v_abbreviation_552_; uint8_t v_isDST_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; uint8_t v___x_557_; lean_object* v_ltt_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_wt_561_; lean_object* v_ltt_562_; lean_object* v_tz_563_; lean_object* v_offset_564_; lean_object* v_second_565_; lean_object* v_nano_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_offset_550_ = lean_ctor_get(v_tz_549_, 0);
v_name_551_ = lean_ctor_get(v_tz_549_, 1);
v_abbreviation_552_ = lean_ctor_get(v_tz_549_, 2);
v_isDST_553_ = lean_ctor_get_uint8(v_tz_549_, sizeof(void*)*3);
v___x_554_ = l_Std_Time_PlainTime_midnight;
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_dt_548_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = 0;
v___x_557_ = 1;
lean_inc_ref(v_name_551_);
lean_inc_ref(v_abbreviation_552_);
lean_inc(v_offset_550_);
v_ltt_558_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_558_, 0, v_offset_550_);
lean_ctor_set(v_ltt_558_, 1, v_abbreviation_552_);
lean_ctor_set(v_ltt_558_, 2, v_name_551_);
lean_ctor_set_uint8(v_ltt_558_, sizeof(void*)*3, v_isDST_553_);
lean_ctor_set_uint8(v_ltt_558_, sizeof(void*)*3 + 1, v___x_556_);
lean_ctor_set_uint8(v_ltt_558_, sizeof(void*)*3 + 2, v___x_557_);
v___x_559_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0));
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_ltt_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v_wt_561_ = l_Std_Time_PlainDateTime_toWallTime(v___x_555_);
v_ltt_562_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_560_, v_wt_561_);
v_tz_563_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_562_);
lean_dec_ref(v_ltt_562_);
v_offset_564_ = lean_ctor_get(v_tz_563_, 0);
lean_inc(v_offset_564_);
lean_dec_ref(v_tz_563_);
v_second_565_ = lean_ctor_get(v_wt_561_, 0);
lean_inc(v_second_565_);
v_nano_566_ = lean_ctor_get(v_wt_561_, 1);
lean_inc(v_nano_566_);
lean_dec_ref(v_wt_561_);
v___x_567_ = lean_int_neg(v_offset_564_);
lean_dec(v_offset_564_);
v___x_568_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_569_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_570_ = lean_int_mul(v_second_565_, v___x_569_);
lean_dec(v_second_565_);
v___x_571_ = lean_int_add(v___x_570_, v_nano_566_);
lean_dec(v_nano_566_);
lean_dec(v___x_570_);
v___x_572_ = lean_int_mul(v___x_567_, v___x_569_);
lean_dec(v___x_567_);
v___x_573_ = lean_int_add(v___x_572_, v___x_568_);
lean_dec(v___x_572_);
v___x_574_ = lean_int_add(v___x_571_, v___x_573_);
lean_dec(v___x_573_);
lean_dec(v___x_571_);
v___x_575_ = l_Std_Time_Duration_ofNanoseconds(v___x_574_);
lean_dec(v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object* v_dt_576_, lean_object* v_tz_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_Time_PlainDate_toTimestampWithZone(v_dt_576_, v_tz_577_);
lean_dec_ref(v_tz_577_);
return v_res_578_;
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
