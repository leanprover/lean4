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
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
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
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_30_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_30_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_30_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_30_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_offset_15_; lean_object* v_second_16_; lean_object* v_nano_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_13_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_9_, v_a_7_);
v___x_14_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_13_);
lean_dec_ref(v___x_13_);
v_offset_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_offset_15_);
lean_dec_ref(v___x_14_);
v_second_16_ = lean_ctor_get(v_a_7_, 0);
lean_inc(v_second_16_);
v_nano_17_ = lean_ctor_get(v_a_7_, 1);
lean_inc(v_nano_17_);
lean_dec(v_a_7_);
v___x_18_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_19_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_20_ = lean_int_mul(v_second_16_, v___x_19_);
lean_dec(v_second_16_);
v___x_21_ = lean_int_add(v___x_20_, v_nano_17_);
lean_dec(v_nano_17_);
lean_dec(v___x_20_);
v___x_22_ = lean_int_mul(v_offset_15_, v___x_19_);
lean_dec(v_offset_15_);
v___x_23_ = lean_int_add(v___x_22_, v___x_18_);
lean_dec(v___x_22_);
v___x_24_ = lean_int_add(v___x_21_, v___x_23_);
lean_dec(v___x_23_);
lean_dec(v___x_21_);
v___x_25_ = l_Std_Time_Duration_ofNanoseconds(v___x_24_);
lean_dec(v___x_24_);
v___x_26_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_25_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 0, v___x_26_);
v___x_28_ = v___x_11_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
lean_dec(v_a_7_);
v_a_31_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_8_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_8_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_6_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_6_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_6_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now___boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Time_PlainDateTime_now();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now(){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_get_current_time();
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v___x_52_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_50_, 1);
v___x_52_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_75_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_75_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_75_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_75_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_offset_59_; lean_object* v_second_60_; lean_object* v_nano_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_date_71_; lean_object* v___x_73_; 
v___x_57_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_53_, v_a_51_);
v___x_58_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_57_);
lean_dec_ref(v___x_57_);
v_offset_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_offset_59_);
lean_dec_ref(v___x_58_);
v_second_60_ = lean_ctor_get(v_a_51_, 0);
lean_inc(v_second_60_);
v_nano_61_ = lean_ctor_get(v_a_51_, 1);
lean_inc(v_nano_61_);
lean_dec(v_a_51_);
v___x_62_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_63_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_64_ = lean_int_mul(v_second_60_, v___x_63_);
lean_dec(v_second_60_);
v___x_65_ = lean_int_add(v___x_64_, v_nano_61_);
lean_dec(v_nano_61_);
lean_dec(v___x_64_);
v___x_66_ = lean_int_mul(v_offset_59_, v___x_63_);
lean_dec(v_offset_59_);
v___x_67_ = lean_int_add(v___x_66_, v___x_62_);
lean_dec(v___x_66_);
v___x_68_ = lean_int_add(v___x_65_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_65_);
v___x_69_ = l_Std_Time_Duration_ofNanoseconds(v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_69_);
v_date_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_date_71_);
lean_dec_ref(v___x_70_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v_date_71_);
v___x_73_ = v___x_55_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_date_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec(v_a_51_);
v_a_76_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_52_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_52_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_a_84_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_50_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_50_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now___boxed(lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Time_PlainDate_now();
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now(){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_get_current_time();
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_120_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_120_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_120_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_120_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_offset_104_; lean_object* v_second_105_; lean_object* v_nano_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_time_116_; lean_object* v___x_118_; 
v___x_102_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_98_, v_a_96_);
v___x_103_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_102_);
lean_dec_ref(v___x_102_);
v_offset_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_offset_104_);
lean_dec_ref(v___x_103_);
v_second_105_ = lean_ctor_get(v_a_96_, 0);
lean_inc(v_second_105_);
v_nano_106_ = lean_ctor_get(v_a_96_, 1);
lean_inc(v_nano_106_);
lean_dec(v_a_96_);
v___x_107_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_108_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_109_ = lean_int_mul(v_second_105_, v___x_108_);
lean_dec(v_second_105_);
v___x_110_ = lean_int_add(v___x_109_, v_nano_106_);
lean_dec(v_nano_106_);
lean_dec(v___x_109_);
v___x_111_ = lean_int_mul(v_offset_104_, v___x_108_);
lean_dec(v_offset_104_);
v___x_112_ = lean_int_add(v___x_111_, v___x_107_);
lean_dec(v___x_111_);
v___x_113_ = lean_int_add(v___x_110_, v___x_112_);
lean_dec(v___x_112_);
lean_dec(v___x_110_);
v___x_114_ = l_Std_Time_Duration_ofNanoseconds(v___x_113_);
lean_dec(v___x_113_);
v___x_115_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_114_);
v_time_116_ = lean_ctor_get(v___x_115_, 1);
lean_inc_ref(v_time_116_);
lean_dec_ref(v___x_115_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v_time_116_);
v___x_118_ = v___x_100_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_time_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_a_96_);
v_a_121_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_97_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_97_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_a_129_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_95_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_95_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now___boxed(lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Time_PlainTime_now();
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object* v_tz_139_, lean_object* v_a_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_offset_142_; lean_object* v_second_143_; lean_object* v_nano_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_offset_142_ = lean_ctor_get(v_tz_139_, 0);
v_second_143_ = lean_ctor_get(v_a_140_, 0);
v_nano_144_ = lean_ctor_get(v_a_140_, 1);
v___x_145_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_146_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_147_ = lean_int_mul(v_second_143_, v___x_146_);
v___x_148_ = lean_int_add(v___x_147_, v_nano_144_);
lean_dec(v___x_147_);
v___x_149_ = lean_int_mul(v_offset_142_, v___x_146_);
v___x_150_ = lean_int_add(v___x_149_, v___x_145_);
lean_dec(v___x_149_);
v___x_151_ = lean_int_add(v___x_148_, v___x_150_);
lean_dec(v___x_150_);
lean_dec(v___x_148_);
v___x_152_ = l_Std_Time_Duration_ofNanoseconds(v___x_151_);
lean_dec(v___x_151_);
v___x_153_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object* v_tz_154_, lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Time_DateTime_now___lam__0(v_tz_154_, v_a_155_, v_x_156_);
lean_dec_ref(v_a_155_);
lean_dec_ref(v_tz_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now(){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_get_current_time();
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_161_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
v___x_161_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_173_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_173_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_tz_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_inc(v_a_162_);
v_tz_166_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_162_, v_a_160_);
lean_inc(v_a_160_);
lean_inc_ref(v_tz_166_);
v___f_167_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_167_, 0, v_tz_166_);
lean_closure_set(v___f_167_, 1, v_a_160_);
v___x_168_ = lean_mk_thunk(v___f_167_);
v___x_169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_a_160_);
lean_ctor_set(v___x_169_, 2, v_a_162_);
lean_ctor_set(v___x_169_, 3, v_tz_166_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_169_);
v___x_171_ = v___x_164_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_a_160_);
v_a_174_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_161_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_161_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_a_182_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_159_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_159_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
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
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___boxed(lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_Time_DateTime_now();
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nowAt(lean_object* v_id_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_get_current_time();
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = l_Std_Time_Database_defaultGetZoneRules(v_id_192_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_tz_201_; lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
lean_inc(v_a_197_);
v_tz_201_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_197_, v_a_195_);
lean_inc(v_a_195_);
lean_inc_ref(v_tz_201_);
v___f_202_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_202_, 0, v_tz_201_);
lean_closure_set(v___f_202_, 1, v_a_195_);
v___x_203_ = lean_mk_thunk(v___f_202_);
v___x_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_a_195_);
lean_ctor_set(v___x_204_, 2, v_a_197_);
lean_ctor_set(v___x_204_, 3, v_tz_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_204_);
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec(v_a_195_);
v_a_209_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_196_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_196_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v_id_192_);
v_a_217_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_194_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_194_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nowAt___boxed(lean_object* v_id_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Time_DateTime_nowAt(v_id_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0(lean_object* v___x_228_, lean_object* v_x_229_){
_start:
{
lean_inc_ref(v___x_228_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0___boxed(lean_object* v___x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Time_DateTime_ofLocalDate___lam__0(v___x_230_, v_x_231_);
lean_dec_ref(v___x_230_);
return v_res_232_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofLocalDate___closed__0(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_234_ = lean_int_neg(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate(lean_object* v_pd_235_, lean_object* v_zr_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_wt_239_; lean_object* v_ltt_240_; lean_object* v_tz_241_; lean_object* v_offset_242_; lean_object* v_second_243_; lean_object* v_nano_244_; lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_237_ = l_Std_Time_PlainTime_midnight;
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_pd_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
lean_inc_ref(v___x_238_);
v_wt_239_ = l_Std_Time_PlainDateTime_toWallTime(v___x_238_);
lean_inc_ref(v_zr_236_);
v_ltt_240_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_236_, v_wt_239_);
v_tz_241_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_240_);
lean_dec_ref(v_ltt_240_);
v_offset_242_ = lean_ctor_get(v_tz_241_, 0);
lean_inc(v_offset_242_);
v_second_243_ = lean_ctor_get(v_wt_239_, 0);
lean_inc(v_second_243_);
v_nano_244_ = lean_ctor_get(v_wt_239_, 1);
lean_inc(v_nano_244_);
lean_dec_ref(v_wt_239_);
v___f_245_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_245_, 0, v___x_238_);
v___x_246_ = lean_mk_thunk(v___f_245_);
v___x_247_ = lean_int_neg(v_offset_242_);
lean_dec(v_offset_242_);
v___x_248_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_249_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_250_ = lean_int_mul(v_second_243_, v___x_249_);
lean_dec(v_second_243_);
v___x_251_ = lean_int_add(v___x_250_, v_nano_244_);
lean_dec(v_nano_244_);
lean_dec(v___x_250_);
v___x_252_ = lean_int_mul(v___x_247_, v___x_249_);
lean_dec(v___x_247_);
v___x_253_ = lean_int_add(v___x_252_, v___x_248_);
lean_dec(v___x_252_);
v___x_254_ = lean_int_add(v___x_251_, v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_251_);
v___x_255_ = l_Std_Time_Duration_ofNanoseconds(v___x_254_);
lean_dec(v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_256_, 0, v___x_246_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_ctor_set(v___x_256_, 2, v_zr_236_);
lean_ctor_set(v___x_256_, 3, v_tz_241_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone(lean_object* v_pd_259_, lean_object* v_zr_260_){
_start:
{
lean_object* v_offset_261_; lean_object* v_name_262_; lean_object* v_abbreviation_263_; uint8_t v_isDST_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; uint8_t v___x_268_; lean_object* v_ltt_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_wt_273_; lean_object* v_ltt_274_; lean_object* v_tz_275_; lean_object* v_offset_276_; lean_object* v_second_277_; lean_object* v_nano_278_; lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_offset_261_ = lean_ctor_get(v_zr_260_, 0);
v_name_262_ = lean_ctor_get(v_zr_260_, 1);
v_abbreviation_263_ = lean_ctor_get(v_zr_260_, 2);
v_isDST_264_ = lean_ctor_get_uint8(v_zr_260_, sizeof(void*)*3);
v___x_265_ = l_Std_Time_PlainTime_midnight;
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_pd_259_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = 0;
v___x_268_ = 1;
lean_inc_ref(v_name_262_);
lean_inc_ref(v_abbreviation_263_);
lean_inc(v_offset_261_);
v_ltt_269_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_269_, 0, v_offset_261_);
lean_ctor_set(v_ltt_269_, 1, v_abbreviation_263_);
lean_ctor_set(v_ltt_269_, 2, v_name_262_);
lean_ctor_set_uint8(v_ltt_269_, sizeof(void*)*3, v_isDST_264_);
lean_ctor_set_uint8(v_ltt_269_, sizeof(void*)*3 + 1, v___x_267_);
lean_ctor_set_uint8(v_ltt_269_, sizeof(void*)*3 + 2, v___x_268_);
v___x_270_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_272_, 0, v_ltt_269_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
lean_inc_ref(v___x_266_);
v_wt_273_ = l_Std_Time_PlainDateTime_toWallTime(v___x_266_);
lean_inc_ref(v___x_272_);
v_ltt_274_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_272_, v_wt_273_);
v_tz_275_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_274_);
lean_dec_ref(v_ltt_274_);
v_offset_276_ = lean_ctor_get(v_tz_275_, 0);
lean_inc(v_offset_276_);
v_second_277_ = lean_ctor_get(v_wt_273_, 0);
lean_inc(v_second_277_);
v_nano_278_ = lean_ctor_get(v_wt_273_, 1);
lean_inc(v_nano_278_);
lean_dec_ref(v_wt_273_);
v___f_279_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_279_, 0, v___x_266_);
v___x_280_ = lean_mk_thunk(v___f_279_);
v___x_281_ = lean_int_neg(v_offset_276_);
lean_dec(v_offset_276_);
v___x_282_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_283_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_284_ = lean_int_mul(v_second_277_, v___x_283_);
lean_dec(v_second_277_);
v___x_285_ = lean_int_add(v___x_284_, v_nano_278_);
lean_dec(v_nano_278_);
lean_dec(v___x_284_);
v___x_286_ = lean_int_mul(v___x_281_, v___x_283_);
lean_dec(v___x_281_);
v___x_287_ = lean_int_add(v___x_286_, v___x_282_);
lean_dec(v___x_286_);
v___x_288_ = lean_int_add(v___x_285_, v___x_287_);
lean_dec(v___x_287_);
lean_dec(v___x_285_);
v___x_289_ = l_Std_Time_Duration_ofNanoseconds(v___x_288_);
lean_dec(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_290_, 0, v___x_280_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
lean_ctor_set(v___x_290_, 2, v___x_272_);
lean_ctor_set(v___x_290_, 3, v_tz_275_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone___boxed(lean_object* v_pd_291_, lean_object* v_zr_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Time_DateTime_ofLocalDateWithZone(v_pd_291_, v_zr_292_);
lean_dec_ref(v_zr_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object* v_dt_294_){
_start:
{
lean_object* v_date_295_; lean_object* v___x_296_; lean_object* v_date_297_; 
v_date_295_ = lean_ctor_get(v_dt_294_, 0);
v___x_296_ = lean_thunk_get_own(v_date_295_);
v_date_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_date_297_);
lean_dec(v___x_296_);
return v_date_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object* v_dt_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_Time_DateTime_toPlainDate(v_dt_298_);
lean_dec_ref(v_dt_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object* v_dt_300_){
_start:
{
lean_object* v_date_301_; lean_object* v___x_302_; lean_object* v_time_303_; 
v_date_301_ = lean_ctor_get(v_dt_300_, 0);
v___x_302_ = lean_thunk_get_own(v_date_301_);
v_time_303_ = lean_ctor_get(v___x_302_, 1);
lean_inc_ref(v_time_303_);
lean_dec(v___x_302_);
return v_time_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object* v_dt_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Time_DateTime_toPlainTime(v_dt_304_);
lean_dec_ref(v_dt_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0(lean_object* v_pdt_306_, lean_object* v_x_307_){
_start:
{
lean_inc_ref(v_pdt_306_);
return v_pdt_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0___boxed(lean_object* v_pdt_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Time_DateTime_of___lam__0(v_pdt_308_, v_x_309_);
lean_dec_ref(v_pdt_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of(lean_object* v_pdt_311_, lean_object* v_id_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_Time_Database_defaultGetZoneRules(v_id_312_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_340_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_340_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_340_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_340_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_wt_319_; lean_object* v_ltt_320_; lean_object* v_tz_321_; lean_object* v_offset_322_; lean_object* v_second_323_; lean_object* v_nano_324_; lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc_ref(v_pdt_311_);
v_wt_319_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_311_);
lean_inc(v_a_315_);
v_ltt_320_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_a_315_, v_wt_319_);
v_tz_321_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_320_);
lean_dec_ref(v_ltt_320_);
v_offset_322_ = lean_ctor_get(v_tz_321_, 0);
lean_inc(v_offset_322_);
v_second_323_ = lean_ctor_get(v_wt_319_, 0);
lean_inc(v_second_323_);
v_nano_324_ = lean_ctor_get(v_wt_319_, 1);
lean_inc(v_nano_324_);
lean_dec_ref(v_wt_319_);
v___f_325_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_of___lam__0___boxed), 2, 1);
lean_closure_set(v___f_325_, 0, v_pdt_311_);
v___x_326_ = lean_mk_thunk(v___f_325_);
v___x_327_ = lean_int_neg(v_offset_322_);
lean_dec(v_offset_322_);
v___x_328_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_329_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_330_ = lean_int_mul(v_second_323_, v___x_329_);
lean_dec(v_second_323_);
v___x_331_ = lean_int_add(v___x_330_, v_nano_324_);
lean_dec(v_nano_324_);
lean_dec(v___x_330_);
v___x_332_ = lean_int_mul(v___x_327_, v___x_329_);
lean_dec(v___x_327_);
v___x_333_ = lean_int_add(v___x_332_, v___x_328_);
lean_dec(v___x_332_);
v___x_334_ = lean_int_add(v___x_331_, v___x_333_);
lean_dec(v___x_333_);
lean_dec(v___x_331_);
v___x_335_ = l_Std_Time_Duration_ofNanoseconds(v___x_334_);
lean_dec(v___x_334_);
v___x_336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_336_, 0, v___x_326_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
lean_ctor_set(v___x_336_, 2, v_a_315_);
lean_ctor_set(v___x_336_, 3, v_tz_321_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_336_);
v___x_338_ = v___x_317_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec_ref(v_pdt_311_);
v_a_341_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_314_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_314_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___boxed(lean_object* v_pdt_349_, lean_object* v_id_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_Time_DateTime_of(v_pdt_349_, v_id_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object* v_pdt_353_, lean_object* v_zr_354_){
_start:
{
lean_object* v_wt_355_; lean_object* v_ltt_356_; lean_object* v_tz_357_; lean_object* v_offset_358_; lean_object* v_second_359_; lean_object* v_nano_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_wt_355_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_353_);
v_ltt_356_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_354_, v_wt_355_);
v_tz_357_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_356_);
lean_dec_ref(v_ltt_356_);
v_offset_358_ = lean_ctor_get(v_tz_357_, 0);
lean_inc(v_offset_358_);
lean_dec_ref(v_tz_357_);
v_second_359_ = lean_ctor_get(v_wt_355_, 0);
lean_inc(v_second_359_);
v_nano_360_ = lean_ctor_get(v_wt_355_, 1);
lean_inc(v_nano_360_);
lean_dec_ref(v_wt_355_);
v___x_361_ = lean_int_neg(v_offset_358_);
lean_dec(v_offset_358_);
v___x_362_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_363_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_364_ = lean_int_mul(v_second_359_, v___x_363_);
lean_dec(v_second_359_);
v___x_365_ = lean_int_add(v___x_364_, v_nano_360_);
lean_dec(v_nano_360_);
lean_dec(v___x_364_);
v___x_366_ = lean_int_mul(v___x_361_, v___x_363_);
lean_dec(v___x_361_);
v___x_367_ = lean_int_add(v___x_366_, v___x_362_);
lean_dec(v___x_366_);
v___x_368_ = lean_int_add(v___x_365_, v___x_367_);
lean_dec(v___x_367_);
lean_dec(v___x_365_);
v___x_369_ = l_Std_Time_Duration_ofNanoseconds(v___x_368_);
lean_dec(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object* v_pdt_370_, lean_object* v_tz_371_){
_start:
{
lean_object* v_offset_372_; lean_object* v_name_373_; lean_object* v_abbreviation_374_; uint8_t v_isDST_375_; uint8_t v___x_376_; uint8_t v___x_377_; lean_object* v_ltt_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_wt_382_; lean_object* v_ltt_383_; lean_object* v_tz_384_; lean_object* v_offset_385_; lean_object* v_second_386_; lean_object* v_nano_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_offset_372_ = lean_ctor_get(v_tz_371_, 0);
v_name_373_ = lean_ctor_get(v_tz_371_, 1);
v_abbreviation_374_ = lean_ctor_get(v_tz_371_, 2);
v_isDST_375_ = lean_ctor_get_uint8(v_tz_371_, sizeof(void*)*3);
v___x_376_ = 0;
v___x_377_ = 1;
lean_inc_ref(v_name_373_);
lean_inc_ref(v_abbreviation_374_);
lean_inc(v_offset_372_);
v_ltt_378_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_378_, 0, v_offset_372_);
lean_ctor_set(v_ltt_378_, 1, v_abbreviation_374_);
lean_ctor_set(v_ltt_378_, 2, v_name_373_);
lean_ctor_set_uint8(v_ltt_378_, sizeof(void*)*3, v_isDST_375_);
lean_ctor_set_uint8(v_ltt_378_, sizeof(void*)*3 + 1, v___x_376_);
lean_ctor_set_uint8(v_ltt_378_, sizeof(void*)*3 + 2, v___x_377_);
v___x_379_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v_ltt_378_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
v_wt_382_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_370_);
v_ltt_383_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_381_, v_wt_382_);
v_tz_384_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_383_);
lean_dec_ref(v_ltt_383_);
v_offset_385_ = lean_ctor_get(v_tz_384_, 0);
lean_inc(v_offset_385_);
lean_dec_ref(v_tz_384_);
v_second_386_ = lean_ctor_get(v_wt_382_, 0);
lean_inc(v_second_386_);
v_nano_387_ = lean_ctor_get(v_wt_382_, 1);
lean_inc(v_nano_387_);
lean_dec_ref(v_wt_382_);
v___x_388_ = lean_int_neg(v_offset_385_);
lean_dec(v_offset_385_);
v___x_389_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_390_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_391_ = lean_int_mul(v_second_386_, v___x_390_);
lean_dec(v_second_386_);
v___x_392_ = lean_int_add(v___x_391_, v_nano_387_);
lean_dec(v_nano_387_);
lean_dec(v___x_391_);
v___x_393_ = lean_int_mul(v___x_388_, v___x_390_);
lean_dec(v___x_388_);
v___x_394_ = lean_int_add(v___x_393_, v___x_389_);
lean_dec(v___x_393_);
v___x_395_ = lean_int_add(v___x_392_, v___x_394_);
lean_dec(v___x_394_);
lean_dec(v___x_392_);
v___x_396_ = l_Std_Time_Duration_ofNanoseconds(v___x_395_);
lean_dec(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object* v_pdt_397_, lean_object* v_tz_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Time_PlainDateTime_toTimestampWithZone(v_pdt_397_, v_tz_398_);
lean_dec_ref(v_tz_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object* v_dt_400_, lean_object* v_zr_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_wt_404_; lean_object* v_ltt_405_; lean_object* v_tz_406_; lean_object* v_offset_407_; lean_object* v_second_408_; lean_object* v_nano_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_402_ = l_Std_Time_PlainTime_midnight;
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_dt_400_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v_wt_404_ = l_Std_Time_PlainDateTime_toWallTime(v___x_403_);
v_ltt_405_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_401_, v_wt_404_);
v_tz_406_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_405_);
lean_dec_ref(v_ltt_405_);
v_offset_407_ = lean_ctor_get(v_tz_406_, 0);
lean_inc(v_offset_407_);
lean_dec_ref(v_tz_406_);
v_second_408_ = lean_ctor_get(v_wt_404_, 0);
lean_inc(v_second_408_);
v_nano_409_ = lean_ctor_get(v_wt_404_, 1);
lean_inc(v_nano_409_);
lean_dec_ref(v_wt_404_);
v___x_410_ = lean_int_neg(v_offset_407_);
lean_dec(v_offset_407_);
v___x_411_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_412_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_413_ = lean_int_mul(v_second_408_, v___x_412_);
lean_dec(v_second_408_);
v___x_414_ = lean_int_add(v___x_413_, v_nano_409_);
lean_dec(v_nano_409_);
lean_dec(v___x_413_);
v___x_415_ = lean_int_mul(v___x_410_, v___x_412_);
lean_dec(v___x_410_);
v___x_416_ = lean_int_add(v___x_415_, v___x_411_);
lean_dec(v___x_415_);
v___x_417_ = lean_int_add(v___x_414_, v___x_416_);
lean_dec(v___x_416_);
lean_dec(v___x_414_);
v___x_418_ = l_Std_Time_Duration_ofNanoseconds(v___x_417_);
lean_dec(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object* v_dt_419_, lean_object* v_tz_420_){
_start:
{
lean_object* v_offset_421_; lean_object* v_name_422_; lean_object* v_abbreviation_423_; uint8_t v_isDST_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; uint8_t v___x_428_; lean_object* v_ltt_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_wt_433_; lean_object* v_ltt_434_; lean_object* v_tz_435_; lean_object* v_offset_436_; lean_object* v_second_437_; lean_object* v_nano_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_offset_421_ = lean_ctor_get(v_tz_420_, 0);
v_name_422_ = lean_ctor_get(v_tz_420_, 1);
v_abbreviation_423_ = lean_ctor_get(v_tz_420_, 2);
v_isDST_424_ = lean_ctor_get_uint8(v_tz_420_, sizeof(void*)*3);
v___x_425_ = l_Std_Time_PlainTime_midnight;
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v_dt_419_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = 0;
v___x_428_ = 1;
lean_inc_ref(v_name_422_);
lean_inc_ref(v_abbreviation_423_);
lean_inc(v_offset_421_);
v_ltt_429_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_429_, 0, v_offset_421_);
lean_ctor_set(v_ltt_429_, 1, v_abbreviation_423_);
lean_ctor_set(v_ltt_429_, 2, v_name_422_);
lean_ctor_set_uint8(v_ltt_429_, sizeof(void*)*3, v_isDST_424_);
lean_ctor_set_uint8(v_ltt_429_, sizeof(void*)*3 + 1, v___x_427_);
lean_ctor_set_uint8(v_ltt_429_, sizeof(void*)*3 + 2, v___x_428_);
v___x_430_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_432_, 0, v_ltt_429_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
v_wt_433_ = l_Std_Time_PlainDateTime_toWallTime(v___x_426_);
v_ltt_434_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_432_, v_wt_433_);
v_tz_435_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_434_);
lean_dec_ref(v_ltt_434_);
v_offset_436_ = lean_ctor_get(v_tz_435_, 0);
lean_inc(v_offset_436_);
lean_dec_ref(v_tz_435_);
v_second_437_ = lean_ctor_get(v_wt_433_, 0);
lean_inc(v_second_437_);
v_nano_438_ = lean_ctor_get(v_wt_433_, 1);
lean_inc(v_nano_438_);
lean_dec_ref(v_wt_433_);
v___x_439_ = lean_int_neg(v_offset_436_);
lean_dec(v_offset_436_);
v___x_440_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_441_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_442_ = lean_int_mul(v_second_437_, v___x_441_);
lean_dec(v_second_437_);
v___x_443_ = lean_int_add(v___x_442_, v_nano_438_);
lean_dec(v_nano_438_);
lean_dec(v___x_442_);
v___x_444_ = lean_int_mul(v___x_439_, v___x_441_);
lean_dec(v___x_439_);
v___x_445_ = lean_int_add(v___x_444_, v___x_440_);
lean_dec(v___x_444_);
v___x_446_ = lean_int_add(v___x_443_, v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_443_);
v___x_447_ = l_Std_Time_Duration_ofNanoseconds(v___x_446_);
lean_dec(v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object* v_dt_448_, lean_object* v_tz_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Time_PlainDate_toTimestampWithZone(v_dt_448_, v_tz_449_);
lean_dec_ref(v_tz_449_);
return v_res_450_;
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
