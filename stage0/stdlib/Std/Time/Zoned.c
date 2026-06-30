// Lean compiler output
// Module: Std.Time.Zoned
// Imports: public import Std.Time.Zoned.ZoneRules public import Std.Time.Zoned.Database public import Std.Time.DateTime
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
lean_object* lean_get_current_time();
lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now();
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nowAt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nowAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_ofLocalDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofLocalDate___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate(lean_object*, lean_object*);
static const lean_array_object l_Std_Time_DateTime_ofLocalDateWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_DateTime_ofLocalDateWithZone___closed__0 = (const lean_object*)&l_Std_Time_DateTime_ofLocalDateWithZone___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object* v___y_157_, lean_object* v_a_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_offset_160_; lean_object* v_second_161_; lean_object* v_nano_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_offset_160_ = lean_ctor_get(v___y_157_, 0);
v_second_161_ = lean_ctor_get(v_a_158_, 0);
v_nano_162_ = lean_ctor_get(v_a_158_, 1);
v___x_163_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_164_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_165_ = lean_int_mul(v_second_161_, v___x_164_);
v___x_166_ = lean_int_add(v___x_165_, v_nano_162_);
lean_dec(v___x_165_);
v___x_167_ = lean_int_mul(v_offset_160_, v___x_164_);
v___x_168_ = lean_int_add(v___x_167_, v___x_163_);
lean_dec(v___x_167_);
v___x_169_ = lean_int_add(v___x_166_, v___x_168_);
lean_dec(v___x_168_);
lean_dec(v___x_166_);
v___x_170_ = l_Std_Time_Duration_ofNanoseconds(v___x_169_);
lean_dec(v___x_169_);
v___x_171_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object* v___y_172_, lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Time_DateTime_now___lam__0(v___y_172_, v_a_173_, v_x_174_);
lean_dec_ref(v_a_173_);
lean_dec_ref(v___y_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now(){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_get_current_time();
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_197_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_197_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_197_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_197_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___y_185_; lean_object* v_initialLocalTimeType_192_; lean_object* v_transitions_193_; lean_object* v___x_194_; 
v_initialLocalTimeType_192_ = lean_ctor_get(v_a_180_, 0);
v_transitions_193_ = lean_ctor_get(v_a_180_, 1);
v___x_194_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_193_, v_a_178_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v___x_195_; 
lean_dec_ref_known(v___x_194_, 1);
v___x_195_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_192_);
v___y_185_ = v___x_195_;
goto v___jp_184_;
}
else
{
lean_object* v_a_196_; 
v_a_196_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_194_, 1);
v___y_185_ = v_a_196_;
goto v___jp_184_;
}
v___jp_184_:
{
lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_a_178_);
lean_inc_ref(v___y_185_);
v___f_186_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_186_, 0, v___y_185_);
lean_closure_set(v___f_186_, 1, v_a_178_);
v___x_187_ = lean_mk_thunk(v___f_186_);
v___x_188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_178_);
lean_ctor_set(v___x_188_, 2, v_a_180_);
lean_ctor_set(v___x_188_, 3, v___y_185_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_188_);
v___x_190_ = v___x_182_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_a_178_);
v_a_198_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_179_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_179_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_177_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_177_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Time_DateTime_now();
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nowAt(lean_object* v_id_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_get_current_time();
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = l_Std_Time_Database_defaultGetZoneRules(v_id_216_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_238_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_238_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_238_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_238_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___y_226_; lean_object* v_initialLocalTimeType_233_; lean_object* v_transitions_234_; lean_object* v___x_235_; 
v_initialLocalTimeType_233_ = lean_ctor_get(v_a_221_, 0);
v_transitions_234_ = lean_ctor_get(v_a_221_, 1);
v___x_235_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_234_, v_a_219_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; 
lean_dec_ref_known(v___x_235_, 1);
v___x_236_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_233_);
v___y_226_ = v___x_236_;
goto v___jp_225_;
}
else
{
lean_object* v_a_237_; 
v_a_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_235_, 1);
v___y_226_ = v_a_237_;
goto v___jp_225_;
}
v___jp_225_:
{
lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
lean_inc(v_a_219_);
lean_inc_ref(v___y_226_);
v___f_227_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_227_, 0, v___y_226_);
lean_closure_set(v___f_227_, 1, v_a_219_);
v___x_228_ = lean_mk_thunk(v___f_227_);
v___x_229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_219_);
lean_ctor_set(v___x_229_, 2, v_a_221_);
lean_ctor_set(v___x_229_, 3, v___y_226_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_229_);
v___x_231_ = v___x_223_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_a_219_);
v_a_239_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_220_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_220_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v_id_216_);
v_a_247_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_218_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_218_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nowAt___boxed(lean_object* v_id_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Time_DateTime_nowAt(v_id_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0(lean_object* v___x_258_, lean_object* v_x_259_){
_start:
{
lean_inc_ref(v___x_258_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0___boxed(lean_object* v___x_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Time_DateTime_ofLocalDate___lam__0(v___x_260_, v_x_261_);
lean_dec_ref(v___x_260_);
return v_res_262_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofLocalDate___closed__0(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_264_ = lean_int_neg(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate(lean_object* v_pd_265_, lean_object* v_zr_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_wt_269_; lean_object* v_ltt_270_; lean_object* v_tz_271_; lean_object* v_offset_272_; lean_object* v_second_273_; lean_object* v_nano_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_267_ = l_Std_Time_PlainTime_midnight;
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_pd_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
lean_inc_ref(v___x_268_);
v_wt_269_ = l_Std_Time_PlainDateTime_toWallTime(v___x_268_);
lean_inc_ref(v_zr_266_);
v_ltt_270_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_266_, v_wt_269_);
v_tz_271_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_270_);
lean_dec_ref(v_ltt_270_);
v_offset_272_ = lean_ctor_get(v_tz_271_, 0);
lean_inc(v_offset_272_);
v_second_273_ = lean_ctor_get(v_wt_269_, 0);
lean_inc(v_second_273_);
v_nano_274_ = lean_ctor_get(v_wt_269_, 1);
lean_inc(v_nano_274_);
lean_dec_ref(v_wt_269_);
v___f_275_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_275_, 0, v___x_268_);
v___x_276_ = lean_mk_thunk(v___f_275_);
v___x_277_ = lean_int_neg(v_offset_272_);
lean_dec(v_offset_272_);
v___x_278_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_279_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_280_ = lean_int_mul(v_second_273_, v___x_279_);
lean_dec(v_second_273_);
v___x_281_ = lean_int_add(v___x_280_, v_nano_274_);
lean_dec(v_nano_274_);
lean_dec(v___x_280_);
v___x_282_ = lean_int_mul(v___x_277_, v___x_279_);
lean_dec(v___x_277_);
v___x_283_ = lean_int_add(v___x_282_, v___x_278_);
lean_dec(v___x_282_);
v___x_284_ = lean_int_add(v___x_281_, v___x_283_);
lean_dec(v___x_283_);
lean_dec(v___x_281_);
v___x_285_ = l_Std_Time_Duration_ofNanoseconds(v___x_284_);
lean_dec(v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_286_, 0, v___x_276_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_ctor_set(v___x_286_, 2, v_zr_266_);
lean_ctor_set(v___x_286_, 3, v_tz_271_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone(lean_object* v_pd_289_, lean_object* v_zr_290_){
_start:
{
lean_object* v_offset_291_; lean_object* v_name_292_; lean_object* v_abbreviation_293_; uint8_t v_isDST_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; uint8_t v___x_298_; lean_object* v_ltt_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_wt_302_; lean_object* v_ltt_303_; lean_object* v_tz_304_; lean_object* v_offset_305_; lean_object* v_second_306_; lean_object* v_nano_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_offset_291_ = lean_ctor_get(v_zr_290_, 0);
v_name_292_ = lean_ctor_get(v_zr_290_, 1);
v_abbreviation_293_ = lean_ctor_get(v_zr_290_, 2);
v_isDST_294_ = lean_ctor_get_uint8(v_zr_290_, sizeof(void*)*3);
v___x_295_ = l_Std_Time_PlainTime_midnight;
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_pd_289_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = 0;
v___x_298_ = 1;
lean_inc_ref(v_name_292_);
lean_inc_ref(v_abbreviation_293_);
lean_inc(v_offset_291_);
v_ltt_299_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_299_, 0, v_offset_291_);
lean_ctor_set(v_ltt_299_, 1, v_abbreviation_293_);
lean_ctor_set(v_ltt_299_, 2, v_name_292_);
lean_ctor_set_uint8(v_ltt_299_, sizeof(void*)*3, v_isDST_294_);
lean_ctor_set_uint8(v_ltt_299_, sizeof(void*)*3 + 1, v___x_297_);
lean_ctor_set_uint8(v_ltt_299_, sizeof(void*)*3 + 2, v___x_298_);
v___x_300_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_ltt_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
lean_inc_ref(v___x_296_);
v_wt_302_ = l_Std_Time_PlainDateTime_toWallTime(v___x_296_);
lean_inc_ref(v___x_301_);
v_ltt_303_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_301_, v_wt_302_);
v_tz_304_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_303_);
lean_dec_ref(v_ltt_303_);
v_offset_305_ = lean_ctor_get(v_tz_304_, 0);
lean_inc(v_offset_305_);
v_second_306_ = lean_ctor_get(v_wt_302_, 0);
lean_inc(v_second_306_);
v_nano_307_ = lean_ctor_get(v_wt_302_, 1);
lean_inc(v_nano_307_);
lean_dec_ref(v_wt_302_);
v___f_308_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_308_, 0, v___x_296_);
v___x_309_ = lean_mk_thunk(v___f_308_);
v___x_310_ = lean_int_neg(v_offset_305_);
lean_dec(v_offset_305_);
v___x_311_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_312_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_313_ = lean_int_mul(v_second_306_, v___x_312_);
lean_dec(v_second_306_);
v___x_314_ = lean_int_add(v___x_313_, v_nano_307_);
lean_dec(v_nano_307_);
lean_dec(v___x_313_);
v___x_315_ = lean_int_mul(v___x_310_, v___x_312_);
lean_dec(v___x_310_);
v___x_316_ = lean_int_add(v___x_315_, v___x_311_);
lean_dec(v___x_315_);
v___x_317_ = lean_int_add(v___x_314_, v___x_316_);
lean_dec(v___x_316_);
lean_dec(v___x_314_);
v___x_318_ = l_Std_Time_Duration_ofNanoseconds(v___x_317_);
lean_dec(v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_319_, 0, v___x_309_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___x_301_);
lean_ctor_set(v___x_319_, 3, v_tz_304_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone___boxed(lean_object* v_pd_320_, lean_object* v_zr_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Time_DateTime_ofLocalDateWithZone(v_pd_320_, v_zr_321_);
lean_dec_ref(v_zr_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object* v_dt_323_){
_start:
{
lean_object* v_date_324_; lean_object* v___x_325_; lean_object* v_date_326_; 
v_date_324_ = lean_ctor_get(v_dt_323_, 0);
v___x_325_ = lean_thunk_get_own(v_date_324_);
v_date_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_date_326_);
lean_dec(v___x_325_);
return v_date_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object* v_dt_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_Time_DateTime_toPlainDate(v_dt_327_);
lean_dec_ref(v_dt_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object* v_dt_329_){
_start:
{
lean_object* v_date_330_; lean_object* v___x_331_; lean_object* v_time_332_; 
v_date_330_ = lean_ctor_get(v_dt_329_, 0);
v___x_331_ = lean_thunk_get_own(v_date_330_);
v_time_332_ = lean_ctor_get(v___x_331_, 1);
lean_inc_ref(v_time_332_);
lean_dec(v___x_331_);
return v_time_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object* v_dt_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_Time_DateTime_toPlainTime(v_dt_333_);
lean_dec_ref(v_dt_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0(lean_object* v_pdt_335_, lean_object* v_x_336_){
_start:
{
lean_inc_ref(v_pdt_335_);
return v_pdt_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0___boxed(lean_object* v_pdt_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_Time_DateTime_of___lam__0(v_pdt_337_, v_x_338_);
lean_dec_ref(v_pdt_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of(lean_object* v_pdt_340_, lean_object* v_id_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_Time_Database_defaultGetZoneRules(v_id_341_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_369_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_369_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_369_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_369_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_wt_348_; lean_object* v_ltt_349_; lean_object* v_tz_350_; lean_object* v_offset_351_; lean_object* v_second_352_; lean_object* v_nano_353_; lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
lean_inc_ref(v_pdt_340_);
v_wt_348_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_340_);
lean_inc(v_a_344_);
v_ltt_349_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_a_344_, v_wt_348_);
v_tz_350_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_349_);
lean_dec_ref(v_ltt_349_);
v_offset_351_ = lean_ctor_get(v_tz_350_, 0);
lean_inc(v_offset_351_);
v_second_352_ = lean_ctor_get(v_wt_348_, 0);
lean_inc(v_second_352_);
v_nano_353_ = lean_ctor_get(v_wt_348_, 1);
lean_inc(v_nano_353_);
lean_dec_ref(v_wt_348_);
v___f_354_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_of___lam__0___boxed), 2, 1);
lean_closure_set(v___f_354_, 0, v_pdt_340_);
v___x_355_ = lean_mk_thunk(v___f_354_);
v___x_356_ = lean_int_neg(v_offset_351_);
lean_dec(v_offset_351_);
v___x_357_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_358_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_359_ = lean_int_mul(v_second_352_, v___x_358_);
lean_dec(v_second_352_);
v___x_360_ = lean_int_add(v___x_359_, v_nano_353_);
lean_dec(v_nano_353_);
lean_dec(v___x_359_);
v___x_361_ = lean_int_mul(v___x_356_, v___x_358_);
lean_dec(v___x_356_);
v___x_362_ = lean_int_add(v___x_361_, v___x_357_);
lean_dec(v___x_361_);
v___x_363_ = lean_int_add(v___x_360_, v___x_362_);
lean_dec(v___x_362_);
lean_dec(v___x_360_);
v___x_364_ = l_Std_Time_Duration_ofNanoseconds(v___x_363_);
lean_dec(v___x_363_);
v___x_365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_365_, 0, v___x_355_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
lean_ctor_set(v___x_365_, 2, v_a_344_);
lean_ctor_set(v___x_365_, 3, v_tz_350_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_365_);
v___x_367_ = v___x_346_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_pdt_340_);
v_a_370_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_343_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_343_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___boxed(lean_object* v_pdt_378_, lean_object* v_id_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Time_DateTime_of(v_pdt_378_, v_id_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object* v_pdt_382_, lean_object* v_zr_383_){
_start:
{
lean_object* v_wt_384_; lean_object* v_ltt_385_; lean_object* v_tz_386_; lean_object* v_offset_387_; lean_object* v_second_388_; lean_object* v_nano_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_wt_384_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_382_);
v_ltt_385_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_383_, v_wt_384_);
v_tz_386_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_385_);
lean_dec_ref(v_ltt_385_);
v_offset_387_ = lean_ctor_get(v_tz_386_, 0);
lean_inc(v_offset_387_);
lean_dec_ref(v_tz_386_);
v_second_388_ = lean_ctor_get(v_wt_384_, 0);
lean_inc(v_second_388_);
v_nano_389_ = lean_ctor_get(v_wt_384_, 1);
lean_inc(v_nano_389_);
lean_dec_ref(v_wt_384_);
v___x_390_ = lean_int_neg(v_offset_387_);
lean_dec(v_offset_387_);
v___x_391_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_392_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_393_ = lean_int_mul(v_second_388_, v___x_392_);
lean_dec(v_second_388_);
v___x_394_ = lean_int_add(v___x_393_, v_nano_389_);
lean_dec(v_nano_389_);
lean_dec(v___x_393_);
v___x_395_ = lean_int_mul(v___x_390_, v___x_392_);
lean_dec(v___x_390_);
v___x_396_ = lean_int_add(v___x_395_, v___x_391_);
lean_dec(v___x_395_);
v___x_397_ = lean_int_add(v___x_394_, v___x_396_);
lean_dec(v___x_396_);
lean_dec(v___x_394_);
v___x_398_ = l_Std_Time_Duration_ofNanoseconds(v___x_397_);
lean_dec(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object* v_pdt_399_, lean_object* v_tz_400_){
_start:
{
lean_object* v_offset_401_; lean_object* v_name_402_; lean_object* v_abbreviation_403_; uint8_t v_isDST_404_; uint8_t v___x_405_; uint8_t v___x_406_; lean_object* v_ltt_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_wt_410_; lean_object* v_ltt_411_; lean_object* v_tz_412_; lean_object* v_offset_413_; lean_object* v_second_414_; lean_object* v_nano_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_offset_401_ = lean_ctor_get(v_tz_400_, 0);
v_name_402_ = lean_ctor_get(v_tz_400_, 1);
v_abbreviation_403_ = lean_ctor_get(v_tz_400_, 2);
v_isDST_404_ = lean_ctor_get_uint8(v_tz_400_, sizeof(void*)*3);
v___x_405_ = 0;
v___x_406_ = 1;
lean_inc_ref(v_name_402_);
lean_inc_ref(v_abbreviation_403_);
lean_inc(v_offset_401_);
v_ltt_407_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_407_, 0, v_offset_401_);
lean_ctor_set(v_ltt_407_, 1, v_abbreviation_403_);
lean_ctor_set(v_ltt_407_, 2, v_name_402_);
lean_ctor_set_uint8(v_ltt_407_, sizeof(void*)*3, v_isDST_404_);
lean_ctor_set_uint8(v_ltt_407_, sizeof(void*)*3 + 1, v___x_405_);
lean_ctor_set_uint8(v_ltt_407_, sizeof(void*)*3 + 2, v___x_406_);
v___x_408_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_ltt_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v_wt_410_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_399_);
v_ltt_411_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_409_, v_wt_410_);
v_tz_412_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_411_);
lean_dec_ref(v_ltt_411_);
v_offset_413_ = lean_ctor_get(v_tz_412_, 0);
lean_inc(v_offset_413_);
lean_dec_ref(v_tz_412_);
v_second_414_ = lean_ctor_get(v_wt_410_, 0);
lean_inc(v_second_414_);
v_nano_415_ = lean_ctor_get(v_wt_410_, 1);
lean_inc(v_nano_415_);
lean_dec_ref(v_wt_410_);
v___x_416_ = lean_int_neg(v_offset_413_);
lean_dec(v_offset_413_);
v___x_417_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_418_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_419_ = lean_int_mul(v_second_414_, v___x_418_);
lean_dec(v_second_414_);
v___x_420_ = lean_int_add(v___x_419_, v_nano_415_);
lean_dec(v_nano_415_);
lean_dec(v___x_419_);
v___x_421_ = lean_int_mul(v___x_416_, v___x_418_);
lean_dec(v___x_416_);
v___x_422_ = lean_int_add(v___x_421_, v___x_417_);
lean_dec(v___x_421_);
v___x_423_ = lean_int_add(v___x_420_, v___x_422_);
lean_dec(v___x_422_);
lean_dec(v___x_420_);
v___x_424_ = l_Std_Time_Duration_ofNanoseconds(v___x_423_);
lean_dec(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object* v_pdt_425_, lean_object* v_tz_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Time_PlainDateTime_toTimestampWithZone(v_pdt_425_, v_tz_426_);
lean_dec_ref(v_tz_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object* v_dt_428_, lean_object* v_zr_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v_wt_432_; lean_object* v_ltt_433_; lean_object* v_tz_434_; lean_object* v_offset_435_; lean_object* v_second_436_; lean_object* v_nano_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_430_ = l_Std_Time_PlainTime_midnight;
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v_dt_428_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v_wt_432_ = l_Std_Time_PlainDateTime_toWallTime(v___x_431_);
v_ltt_433_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_429_, v_wt_432_);
v_tz_434_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_433_);
lean_dec_ref(v_ltt_433_);
v_offset_435_ = lean_ctor_get(v_tz_434_, 0);
lean_inc(v_offset_435_);
lean_dec_ref(v_tz_434_);
v_second_436_ = lean_ctor_get(v_wt_432_, 0);
lean_inc(v_second_436_);
v_nano_437_ = lean_ctor_get(v_wt_432_, 1);
lean_inc(v_nano_437_);
lean_dec_ref(v_wt_432_);
v___x_438_ = lean_int_neg(v_offset_435_);
lean_dec(v_offset_435_);
v___x_439_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_440_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_441_ = lean_int_mul(v_second_436_, v___x_440_);
lean_dec(v_second_436_);
v___x_442_ = lean_int_add(v___x_441_, v_nano_437_);
lean_dec(v_nano_437_);
lean_dec(v___x_441_);
v___x_443_ = lean_int_mul(v___x_438_, v___x_440_);
lean_dec(v___x_438_);
v___x_444_ = lean_int_add(v___x_443_, v___x_439_);
lean_dec(v___x_443_);
v___x_445_ = lean_int_add(v___x_442_, v___x_444_);
lean_dec(v___x_444_);
lean_dec(v___x_442_);
v___x_446_ = l_Std_Time_Duration_ofNanoseconds(v___x_445_);
lean_dec(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object* v_dt_447_, lean_object* v_tz_448_){
_start:
{
lean_object* v_offset_449_; lean_object* v_name_450_; lean_object* v_abbreviation_451_; uint8_t v_isDST_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; lean_object* v_ltt_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_wt_460_; lean_object* v_ltt_461_; lean_object* v_tz_462_; lean_object* v_offset_463_; lean_object* v_second_464_; lean_object* v_nano_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_offset_449_ = lean_ctor_get(v_tz_448_, 0);
v_name_450_ = lean_ctor_get(v_tz_448_, 1);
v_abbreviation_451_ = lean_ctor_get(v_tz_448_, 2);
v_isDST_452_ = lean_ctor_get_uint8(v_tz_448_, sizeof(void*)*3);
v___x_453_ = l_Std_Time_PlainTime_midnight;
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_dt_447_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = 0;
v___x_456_ = 1;
lean_inc_ref(v_name_450_);
lean_inc_ref(v_abbreviation_451_);
lean_inc(v_offset_449_);
v_ltt_457_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_457_, 0, v_offset_449_);
lean_ctor_set(v_ltt_457_, 1, v_abbreviation_451_);
lean_ctor_set(v_ltt_457_, 2, v_name_450_);
lean_ctor_set_uint8(v_ltt_457_, sizeof(void*)*3, v_isDST_452_);
lean_ctor_set_uint8(v_ltt_457_, sizeof(void*)*3 + 1, v___x_455_);
lean_ctor_set_uint8(v_ltt_457_, sizeof(void*)*3 + 2, v___x_456_);
v___x_458_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_ltt_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v_wt_460_ = l_Std_Time_PlainDateTime_toWallTime(v___x_454_);
v_ltt_461_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_459_, v_wt_460_);
v_tz_462_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_461_);
lean_dec_ref(v_ltt_461_);
v_offset_463_ = lean_ctor_get(v_tz_462_, 0);
lean_inc(v_offset_463_);
lean_dec_ref(v_tz_462_);
v_second_464_ = lean_ctor_get(v_wt_460_, 0);
lean_inc(v_second_464_);
v_nano_465_ = lean_ctor_get(v_wt_460_, 1);
lean_inc(v_nano_465_);
lean_dec_ref(v_wt_460_);
v___x_466_ = lean_int_neg(v_offset_463_);
lean_dec(v_offset_463_);
v___x_467_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_468_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_469_ = lean_int_mul(v_second_464_, v___x_468_);
lean_dec(v_second_464_);
v___x_470_ = lean_int_add(v___x_469_, v_nano_465_);
lean_dec(v_nano_465_);
lean_dec(v___x_469_);
v___x_471_ = lean_int_mul(v___x_466_, v___x_468_);
lean_dec(v___x_466_);
v___x_472_ = lean_int_add(v___x_471_, v___x_467_);
lean_dec(v___x_471_);
v___x_473_ = lean_int_add(v___x_470_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v___x_470_);
v___x_474_ = l_Std_Time_Duration_ofNanoseconds(v___x_473_);
lean_dec(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object* v_dt_475_, lean_object* v_tz_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Time_PlainDate_toTimestampWithZone(v_dt_475_, v_tz_476_);
lean_dec_ref(v_tz_476_);
return v_res_477_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime(builtin);
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
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime(builtin);
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
