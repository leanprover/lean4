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
lean_object* l_Std_Time_PlainDateTime_now(){
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
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_offset_15_; lean_object* v_second_16_; lean_object* v_nano_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_nanos_21_; lean_object* v___x_22_; lean_object* v_nanos_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
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
v_nanos_21_ = lean_int_add(v___x_20_, v_nano_17_);
lean_dec(v_nano_17_);
lean_dec(v___x_20_);
v___x_22_ = lean_int_mul(v_offset_15_, v___x_19_);
lean_dec(v_offset_15_);
v_nanos_23_ = lean_int_add(v___x_22_, v___x_18_);
lean_dec(v___x_22_);
v___x_24_ = lean_int_add(v_nanos_21_, v_nanos_23_);
lean_dec(v_nanos_23_);
lean_dec(v_nanos_21_);
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
LEAN_EXPORT void l_Std_Time_PlainDateTime_now_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_47_;
v_res_47_ = l_Std_Time_PlainDateTime_now();
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now___boxed(lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_Time_PlainDateTime_now();
return v_res_49_;
}
}
lean_object* l_Std_Time_PlainDate_now(){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_get_current_time();
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 1);
v___x_53_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_76_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_76_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_76_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_76_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_offset_60_; lean_object* v_second_61_; lean_object* v_nano_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_nanos_66_; lean_object* v___x_67_; lean_object* v_nanos_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_date_72_; lean_object* v___x_74_; 
v___x_58_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_54_, v_a_52_);
v___x_59_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_58_);
lean_dec_ref(v___x_58_);
v_offset_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_offset_60_);
lean_dec_ref(v___x_59_);
v_second_61_ = lean_ctor_get(v_a_52_, 0);
lean_inc(v_second_61_);
v_nano_62_ = lean_ctor_get(v_a_52_, 1);
lean_inc(v_nano_62_);
lean_dec(v_a_52_);
v___x_63_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_64_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_65_ = lean_int_mul(v_second_61_, v___x_64_);
lean_dec(v_second_61_);
v_nanos_66_ = lean_int_add(v___x_65_, v_nano_62_);
lean_dec(v_nano_62_);
lean_dec(v___x_65_);
v___x_67_ = lean_int_mul(v_offset_60_, v___x_64_);
lean_dec(v_offset_60_);
v_nanos_68_ = lean_int_add(v___x_67_, v___x_63_);
lean_dec(v___x_67_);
v___x_69_ = lean_int_add(v_nanos_66_, v_nanos_68_);
lean_dec(v_nanos_68_);
lean_dec(v_nanos_66_);
v___x_70_ = l_Std_Time_Duration_ofNanoseconds(v___x_69_);
lean_dec(v___x_69_);
v___x_71_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_70_);
v_date_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_date_72_);
lean_dec_ref(v___x_71_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v_date_72_);
v___x_74_ = v___x_56_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_date_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v_a_52_);
v_a_77_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_53_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_53_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_a_85_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_51_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_51_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_now_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_93_;
v_res_93_ = l_Std_Time_PlainDate_now();
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now___boxed(lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_Time_PlainDate_now();
return v_res_95_;
}
}
lean_object* l_Std_Time_PlainTime_now(){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_get_current_time();
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_122_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_122_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_offset_106_; lean_object* v_second_107_; lean_object* v_nano_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_nanos_112_; lean_object* v___x_113_; lean_object* v_nanos_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_time_118_; lean_object* v___x_120_; 
v___x_104_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_100_, v_a_98_);
v___x_105_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_104_);
lean_dec_ref(v___x_104_);
v_offset_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_offset_106_);
lean_dec_ref(v___x_105_);
v_second_107_ = lean_ctor_get(v_a_98_, 0);
lean_inc(v_second_107_);
v_nano_108_ = lean_ctor_get(v_a_98_, 1);
lean_inc(v_nano_108_);
lean_dec(v_a_98_);
v___x_109_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_110_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_111_ = lean_int_mul(v_second_107_, v___x_110_);
lean_dec(v_second_107_);
v_nanos_112_ = lean_int_add(v___x_111_, v_nano_108_);
lean_dec(v_nano_108_);
lean_dec(v___x_111_);
v___x_113_ = lean_int_mul(v_offset_106_, v___x_110_);
lean_dec(v_offset_106_);
v_nanos_114_ = lean_int_add(v___x_113_, v___x_109_);
lean_dec(v___x_113_);
v___x_115_ = lean_int_add(v_nanos_112_, v_nanos_114_);
lean_dec(v_nanos_114_);
lean_dec(v_nanos_112_);
v___x_116_ = l_Std_Time_Duration_ofNanoseconds(v___x_115_);
lean_dec(v___x_115_);
v___x_117_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_116_);
v_time_118_ = lean_ctor_get(v___x_117_, 1);
lean_inc_ref(v_time_118_);
lean_dec_ref(v___x_117_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_time_118_);
v___x_120_ = v___x_102_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_time_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_a_98_);
v_a_123_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_99_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_99_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_131_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_97_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_97_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_PlainTime_now_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_139_;
v_res_139_ = l_Std_Time_PlainTime_now();
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now___boxed(lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_Time_PlainTime_now();
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object* v_tz_142_, lean_object* v_a_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_offset_145_; lean_object* v_second_146_; lean_object* v_nano_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_nanos_151_; lean_object* v___x_152_; lean_object* v_nanos_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_offset_145_ = lean_ctor_get(v_tz_142_, 0);
v_second_146_ = lean_ctor_get(v_a_143_, 0);
v_nano_147_ = lean_ctor_get(v_a_143_, 1);
v___x_148_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_149_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_150_ = lean_int_mul(v_second_146_, v___x_149_);
v_nanos_151_ = lean_int_add(v___x_150_, v_nano_147_);
lean_dec(v___x_150_);
v___x_152_ = lean_int_mul(v_offset_145_, v___x_149_);
v_nanos_153_ = lean_int_add(v___x_152_, v___x_148_);
lean_dec(v___x_152_);
v___x_154_ = lean_int_add(v_nanos_151_, v_nanos_153_);
lean_dec(v_nanos_153_);
lean_dec(v_nanos_151_);
v___x_155_ = l_Std_Time_Duration_ofNanoseconds(v___x_154_);
lean_dec(v___x_154_);
v___x_156_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object* v_tz_157_, lean_object* v_a_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Time_DateTime_now___lam__0(v_tz_157_, v_a_158_, v_x_159_);
lean_dec_ref(v_a_158_);
lean_dec_ref(v_tz_157_);
return v_res_160_;
}
}
lean_object* l_Std_Time_DateTime_now(){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_get_current_time();
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_176_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_176_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_176_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_176_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_tz_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
lean_inc(v_a_165_);
v_tz_169_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_165_, v_a_163_);
lean_inc(v_a_163_);
lean_inc_ref(v_tz_169_);
v___f_170_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_170_, 0, v_tz_169_);
lean_closure_set(v___f_170_, 1, v_a_163_);
v___x_171_ = lean_mk_thunk(v___f_170_);
v___x_172_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_a_163_);
lean_ctor_set(v___x_172_, 2, v_a_165_);
lean_ctor_set(v___x_172_, 3, v_tz_169_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_172_);
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_a_163_);
v_a_177_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_164_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_164_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_162_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_162_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
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
}
LEAN_EXPORT void l_Std_Time_DateTime_now_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_193_;
v_res_193_ = l_Std_Time_DateTime_now();
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___boxed(lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Time_DateTime_now();
return v_res_195_;
}
}
lean_object* l_Std_Time_DateTime_nowAt(lean_object* v_id_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_get_current_time();
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v___x_200_ = l_Std_Time_Database_defaultGetZoneRules(v_id_196_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_212_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_212_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_tz_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
lean_inc(v_a_201_);
v_tz_205_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_a_201_, v_a_199_);
lean_inc(v_a_199_);
lean_inc_ref(v_tz_205_);
v___f_206_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(v___f_206_, 0, v_tz_205_);
lean_closure_set(v___f_206_, 1, v_a_199_);
v___x_207_ = lean_mk_thunk(v___f_206_);
v___x_208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_a_199_);
lean_ctor_set(v___x_208_, 2, v_a_201_);
lean_ctor_set(v___x_208_, 3, v_tz_205_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_208_);
v___x_210_ = v___x_203_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_199_);
v_a_213_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_200_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_200_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_id_196_);
v_a_221_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_198_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_198_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_DateTime_nowAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_196_ = stack[0].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Std_Time_DateTime_nowAt(v_id_196_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nowAt___boxed(lean_object* v_id_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Time_DateTime_nowAt(v_id_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0(lean_object* v___x_233_, lean_object* v_x_234_){
_start:
{
lean_inc_ref(v___x_233_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate___lam__0___boxed(lean_object* v___x_235_, lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Time_DateTime_ofLocalDate___lam__0(v___x_235_, v_x_236_);
lean_dec_ref(v___x_235_);
return v_res_237_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofLocalDate___closed__0(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__0, &l_Std_Time_PlainDateTime_now___closed__0_once, _init_l_Std_Time_PlainDateTime_now___closed__0);
v___x_239_ = lean_int_neg(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDate(lean_object* v_pd_240_, lean_object* v_zr_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_wt_244_; lean_object* v_ltt_245_; lean_object* v_tz_246_; lean_object* v_offset_247_; lean_object* v_second_248_; lean_object* v_nano_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_nanos_256_; lean_object* v___x_257_; lean_object* v_nanos_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_242_ = l_Std_Time_PlainTime_midnight;
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_pd_240_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_inc_ref(v___x_243_);
v_wt_244_ = l_Std_Time_PlainDateTime_toWallTime(v___x_243_);
lean_inc_ref(v_zr_241_);
v_ltt_245_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_241_, v_wt_244_);
v_tz_246_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_245_);
lean_dec_ref(v_ltt_245_);
v_offset_247_ = lean_ctor_get(v_tz_246_, 0);
v_second_248_ = lean_ctor_get(v_wt_244_, 0);
lean_inc(v_second_248_);
v_nano_249_ = lean_ctor_get(v_wt_244_, 1);
lean_inc(v_nano_249_);
lean_dec_ref(v_wt_244_);
v___f_250_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_250_, 0, v___x_243_);
v___x_251_ = lean_mk_thunk(v___f_250_);
v___x_252_ = lean_int_neg(v_offset_247_);
v___x_253_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_254_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_255_ = lean_int_mul(v_second_248_, v___x_254_);
lean_dec(v_second_248_);
v_nanos_256_ = lean_int_add(v___x_255_, v_nano_249_);
lean_dec(v_nano_249_);
lean_dec(v___x_255_);
v___x_257_ = lean_int_mul(v___x_252_, v___x_254_);
lean_dec(v___x_252_);
v_nanos_258_ = lean_int_add(v___x_257_, v___x_253_);
lean_dec(v___x_257_);
v___x_259_ = lean_int_add(v_nanos_256_, v_nanos_258_);
lean_dec(v_nanos_258_);
lean_dec(v_nanos_256_);
v___x_260_ = l_Std_Time_Duration_ofNanoseconds(v___x_259_);
lean_dec(v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_251_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_ctor_set(v___x_261_, 2, v_zr_241_);
lean_ctor_set(v___x_261_, 3, v_tz_246_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone(lean_object* v_pd_264_, lean_object* v_zr_265_){
_start:
{
lean_object* v_offset_266_; lean_object* v_name_267_; lean_object* v_abbreviation_268_; uint8_t v_isDST_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; uint8_t v___x_273_; lean_object* v_ltt_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_wt_278_; lean_object* v_ltt_279_; lean_object* v_tz_280_; lean_object* v_offset_281_; lean_object* v_second_282_; lean_object* v_nano_283_; lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_nanos_290_; lean_object* v___x_291_; lean_object* v_nanos_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_offset_266_ = lean_ctor_get(v_zr_265_, 0);
v_name_267_ = lean_ctor_get(v_zr_265_, 1);
v_abbreviation_268_ = lean_ctor_get(v_zr_265_, 2);
v_isDST_269_ = lean_ctor_get_uint8(v_zr_265_, sizeof(void*)*3);
v___x_270_ = l_Std_Time_PlainTime_midnight;
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_pd_264_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = 0;
v___x_273_ = 1;
lean_inc_ref(v_name_267_);
lean_inc_ref(v_abbreviation_268_);
lean_inc(v_offset_266_);
v_ltt_274_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_274_, 0, v_offset_266_);
lean_ctor_set(v_ltt_274_, 1, v_abbreviation_268_);
lean_ctor_set(v_ltt_274_, 2, v_name_267_);
lean_ctor_set_uint8(v_ltt_274_, sizeof(void*)*3, v_isDST_269_);
lean_ctor_set_uint8(v_ltt_274_, sizeof(void*)*3 + 1, v___x_272_);
lean_ctor_set_uint8(v_ltt_274_, sizeof(void*)*3 + 2, v___x_273_);
v___x_275_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_277_, 0, v_ltt_274_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_inc_ref(v___x_271_);
v_wt_278_ = l_Std_Time_PlainDateTime_toWallTime(v___x_271_);
lean_inc_ref(v___x_277_);
v_ltt_279_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_277_, v_wt_278_);
v_tz_280_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_279_);
lean_dec_ref(v_ltt_279_);
v_offset_281_ = lean_ctor_get(v_tz_280_, 0);
v_second_282_ = lean_ctor_get(v_wt_278_, 0);
lean_inc(v_second_282_);
v_nano_283_ = lean_ctor_get(v_wt_278_, 1);
lean_inc(v_nano_283_);
lean_dec_ref(v_wt_278_);
v___f_284_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofLocalDate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_284_, 0, v___x_271_);
v___x_285_ = lean_mk_thunk(v___f_284_);
v___x_286_ = lean_int_neg(v_offset_281_);
v___x_287_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_288_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_289_ = lean_int_mul(v_second_282_, v___x_288_);
lean_dec(v_second_282_);
v_nanos_290_ = lean_int_add(v___x_289_, v_nano_283_);
lean_dec(v_nano_283_);
lean_dec(v___x_289_);
v___x_291_ = lean_int_mul(v___x_286_, v___x_288_);
lean_dec(v___x_286_);
v_nanos_292_ = lean_int_add(v___x_291_, v___x_287_);
lean_dec(v___x_291_);
v___x_293_ = lean_int_add(v_nanos_290_, v_nanos_292_);
lean_dec(v_nanos_292_);
lean_dec(v_nanos_290_);
v___x_294_ = l_Std_Time_Duration_ofNanoseconds(v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_295_, 0, v___x_285_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_ctor_set(v___x_295_, 2, v___x_277_);
lean_ctor_set(v___x_295_, 3, v_tz_280_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofLocalDateWithZone___boxed(lean_object* v_pd_296_, lean_object* v_zr_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Time_DateTime_ofLocalDateWithZone(v_pd_296_, v_zr_297_);
lean_dec_ref(v_zr_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object* v_dt_299_){
_start:
{
lean_object* v_date_300_; lean_object* v___x_301_; lean_object* v_date_302_; 
v_date_300_ = lean_ctor_get(v_dt_299_, 0);
v___x_301_ = lean_thunk_get_own(v_date_300_);
v_date_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_date_302_);
lean_dec(v___x_301_);
return v_date_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object* v_dt_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_Time_DateTime_toPlainDate(v_dt_303_);
lean_dec_ref(v_dt_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object* v_dt_305_){
_start:
{
lean_object* v_date_306_; lean_object* v___x_307_; lean_object* v_time_308_; 
v_date_306_ = lean_ctor_get(v_dt_305_, 0);
v___x_307_ = lean_thunk_get_own(v_date_306_);
v_time_308_ = lean_ctor_get(v___x_307_, 1);
lean_inc_ref(v_time_308_);
lean_dec(v___x_307_);
return v_time_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object* v_dt_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Time_DateTime_toPlainTime(v_dt_309_);
lean_dec_ref(v_dt_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0(lean_object* v_pdt_311_, lean_object* v_x_312_){
_start:
{
lean_inc_ref(v_pdt_311_);
return v_pdt_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___lam__0___boxed(lean_object* v_pdt_313_, lean_object* v_x_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Time_DateTime_of___lam__0(v_pdt_313_, v_x_314_);
lean_dec_ref(v_pdt_313_);
return v_res_315_;
}
}
lean_object* l_Std_Time_DateTime_of(lean_object* v_pdt_316_, lean_object* v_id_317_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; 
lean_inc_ref(v_pdt_316_);
v___f_319_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_of___lam__0___boxed), 2, 1);
lean_closure_set(v___f_319_, 0, v_pdt_316_);
v___x_320_ = l_Std_Time_Database_defaultGetZoneRules(v_id_317_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_345_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_345_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_345_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_345_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_wt_325_; lean_object* v_ltt_326_; lean_object* v_tz_327_; lean_object* v_offset_328_; lean_object* v_second_329_; lean_object* v_nano_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_nanos_336_; lean_object* v___x_337_; lean_object* v_nanos_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v_wt_325_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_316_);
lean_inc(v_a_321_);
v_ltt_326_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_a_321_, v_wt_325_);
v_tz_327_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_326_);
lean_dec_ref(v_ltt_326_);
v_offset_328_ = lean_ctor_get(v_tz_327_, 0);
v_second_329_ = lean_ctor_get(v_wt_325_, 0);
lean_inc(v_second_329_);
v_nano_330_ = lean_ctor_get(v_wt_325_, 1);
lean_inc(v_nano_330_);
lean_dec_ref(v_wt_325_);
v___x_331_ = lean_mk_thunk(v___f_319_);
v___x_332_ = lean_int_neg(v_offset_328_);
v___x_333_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_334_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_335_ = lean_int_mul(v_second_329_, v___x_334_);
lean_dec(v_second_329_);
v_nanos_336_ = lean_int_add(v___x_335_, v_nano_330_);
lean_dec(v_nano_330_);
lean_dec(v___x_335_);
v___x_337_ = lean_int_mul(v___x_332_, v___x_334_);
lean_dec(v___x_332_);
v_nanos_338_ = lean_int_add(v___x_337_, v___x_333_);
lean_dec(v___x_337_);
v___x_339_ = lean_int_add(v_nanos_336_, v_nanos_338_);
lean_dec(v_nanos_338_);
lean_dec(v_nanos_336_);
v___x_340_ = l_Std_Time_Duration_ofNanoseconds(v___x_339_);
lean_dec(v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_341_, 0, v___x_331_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_ctor_set(v___x_341_, 2, v_a_321_);
lean_ctor_set(v___x_341_, 3, v_tz_327_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_341_);
v___x_343_ = v___x_323_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___f_319_);
lean_dec_ref(v_pdt_316_);
v_a_346_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_320_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_320_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_DateTime_of_0interp(lean_interpreter_value* stack)
{
lean_object* v_pdt_316_ = stack[0].m_obj;
lean_object* v_id_317_ = stack[1].m_obj;
lean_object* v_res_354_;
v_res_354_ = l_Std_Time_DateTime_of(v_pdt_316_, v_id_317_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_of___boxed(lean_object* v_pdt_355_, lean_object* v_id_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Time_DateTime_of(v_pdt_355_, v_id_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object* v_pdt_359_, lean_object* v_zr_360_){
_start:
{
lean_object* v_wt_361_; lean_object* v_ltt_362_; lean_object* v_tz_363_; lean_object* v_offset_364_; lean_object* v_second_365_; lean_object* v_nano_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_nanos_371_; lean_object* v___x_372_; lean_object* v_nanos_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_wt_361_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_359_);
v_ltt_362_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_360_, v_wt_361_);
v_tz_363_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_362_);
lean_dec_ref(v_ltt_362_);
v_offset_364_ = lean_ctor_get(v_tz_363_, 0);
lean_inc(v_offset_364_);
lean_dec_ref(v_tz_363_);
v_second_365_ = lean_ctor_get(v_wt_361_, 0);
lean_inc(v_second_365_);
v_nano_366_ = lean_ctor_get(v_wt_361_, 1);
lean_inc(v_nano_366_);
lean_dec_ref(v_wt_361_);
v___x_367_ = lean_int_neg(v_offset_364_);
lean_dec(v_offset_364_);
v___x_368_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_369_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_370_ = lean_int_mul(v_second_365_, v___x_369_);
lean_dec(v_second_365_);
v_nanos_371_ = lean_int_add(v___x_370_, v_nano_366_);
lean_dec(v_nano_366_);
lean_dec(v___x_370_);
v___x_372_ = lean_int_mul(v___x_367_, v___x_369_);
lean_dec(v___x_367_);
v_nanos_373_ = lean_int_add(v___x_372_, v___x_368_);
lean_dec(v___x_372_);
v___x_374_ = lean_int_add(v_nanos_371_, v_nanos_373_);
lean_dec(v_nanos_373_);
lean_dec(v_nanos_371_);
v___x_375_ = l_Std_Time_Duration_ofNanoseconds(v___x_374_);
lean_dec(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object* v_pdt_376_, lean_object* v_tz_377_){
_start:
{
lean_object* v_offset_378_; lean_object* v_name_379_; lean_object* v_abbreviation_380_; uint8_t v_isDST_381_; uint8_t v___x_382_; uint8_t v___x_383_; lean_object* v_ltt_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_wt_388_; lean_object* v_ltt_389_; lean_object* v_tz_390_; lean_object* v_offset_391_; lean_object* v_second_392_; lean_object* v_nano_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_nanos_398_; lean_object* v___x_399_; lean_object* v_nanos_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_offset_378_ = lean_ctor_get(v_tz_377_, 0);
v_name_379_ = lean_ctor_get(v_tz_377_, 1);
v_abbreviation_380_ = lean_ctor_get(v_tz_377_, 2);
v_isDST_381_ = lean_ctor_get_uint8(v_tz_377_, sizeof(void*)*3);
v___x_382_ = 0;
v___x_383_ = 1;
lean_inc_ref(v_name_379_);
lean_inc_ref(v_abbreviation_380_);
lean_inc(v_offset_378_);
v_ltt_384_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_384_, 0, v_offset_378_);
lean_ctor_set(v_ltt_384_, 1, v_abbreviation_380_);
lean_ctor_set(v_ltt_384_, 2, v_name_379_);
lean_ctor_set_uint8(v_ltt_384_, sizeof(void*)*3, v_isDST_381_);
lean_ctor_set_uint8(v_ltt_384_, sizeof(void*)*3 + 1, v___x_382_);
lean_ctor_set_uint8(v_ltt_384_, sizeof(void*)*3 + 2, v___x_383_);
v___x_385_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_386_ = lean_box(0);
v___x_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_387_, 0, v_ltt_384_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
lean_ctor_set(v___x_387_, 2, v___x_386_);
v_wt_388_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_376_);
v_ltt_389_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_387_, v_wt_388_);
v_tz_390_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_389_);
lean_dec_ref(v_ltt_389_);
v_offset_391_ = lean_ctor_get(v_tz_390_, 0);
lean_inc(v_offset_391_);
lean_dec_ref(v_tz_390_);
v_second_392_ = lean_ctor_get(v_wt_388_, 0);
lean_inc(v_second_392_);
v_nano_393_ = lean_ctor_get(v_wt_388_, 1);
lean_inc(v_nano_393_);
lean_dec_ref(v_wt_388_);
v___x_394_ = lean_int_neg(v_offset_391_);
lean_dec(v_offset_391_);
v___x_395_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_396_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_397_ = lean_int_mul(v_second_392_, v___x_396_);
lean_dec(v_second_392_);
v_nanos_398_ = lean_int_add(v___x_397_, v_nano_393_);
lean_dec(v_nano_393_);
lean_dec(v___x_397_);
v___x_399_ = lean_int_mul(v___x_394_, v___x_396_);
lean_dec(v___x_394_);
v_nanos_400_ = lean_int_add(v___x_399_, v___x_395_);
lean_dec(v___x_399_);
v___x_401_ = lean_int_add(v_nanos_398_, v_nanos_400_);
lean_dec(v_nanos_400_);
lean_dec(v_nanos_398_);
v___x_402_ = l_Std_Time_Duration_ofNanoseconds(v___x_401_);
lean_dec(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object* v_pdt_403_, lean_object* v_tz_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Time_PlainDateTime_toTimestampWithZone(v_pdt_403_, v_tz_404_);
lean_dec_ref(v_tz_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object* v_dt_406_, lean_object* v_zr_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_wt_410_; lean_object* v_ltt_411_; lean_object* v_tz_412_; lean_object* v_offset_413_; lean_object* v_second_414_; lean_object* v_nano_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_nanos_420_; lean_object* v___x_421_; lean_object* v_nanos_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_408_ = l_Std_Time_PlainTime_midnight;
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_dt_406_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v_wt_410_ = l_Std_Time_PlainDateTime_toWallTime(v___x_409_);
v_ltt_411_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_407_, v_wt_410_);
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
v_nanos_420_ = lean_int_add(v___x_419_, v_nano_415_);
lean_dec(v_nano_415_);
lean_dec(v___x_419_);
v___x_421_ = lean_int_mul(v___x_416_, v___x_418_);
lean_dec(v___x_416_);
v_nanos_422_ = lean_int_add(v___x_421_, v___x_417_);
lean_dec(v___x_421_);
v___x_423_ = lean_int_add(v_nanos_420_, v_nanos_422_);
lean_dec(v_nanos_422_);
lean_dec(v_nanos_420_);
v___x_424_ = l_Std_Time_Duration_ofNanoseconds(v___x_423_);
lean_dec(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object* v_dt_425_, lean_object* v_tz_426_){
_start:
{
lean_object* v_offset_427_; lean_object* v_name_428_; lean_object* v_abbreviation_429_; uint8_t v_isDST_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; uint8_t v___x_434_; lean_object* v_ltt_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_wt_439_; lean_object* v_ltt_440_; lean_object* v_tz_441_; lean_object* v_offset_442_; lean_object* v_second_443_; lean_object* v_nano_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_nanos_449_; lean_object* v___x_450_; lean_object* v_nanos_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_offset_427_ = lean_ctor_get(v_tz_426_, 0);
v_name_428_ = lean_ctor_get(v_tz_426_, 1);
v_abbreviation_429_ = lean_ctor_get(v_tz_426_, 2);
v_isDST_430_ = lean_ctor_get_uint8(v_tz_426_, sizeof(void*)*3);
v___x_431_ = l_Std_Time_PlainTime_midnight;
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v_dt_425_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = 0;
v___x_434_ = 1;
lean_inc_ref(v_name_428_);
lean_inc_ref(v_abbreviation_429_);
lean_inc(v_offset_427_);
v_ltt_435_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_435_, 0, v_offset_427_);
lean_ctor_set(v_ltt_435_, 1, v_abbreviation_429_);
lean_ctor_set(v_ltt_435_, 2, v_name_428_);
lean_ctor_set_uint8(v_ltt_435_, sizeof(void*)*3, v_isDST_430_);
lean_ctor_set_uint8(v_ltt_435_, sizeof(void*)*3 + 1, v___x_433_);
lean_ctor_set_uint8(v_ltt_435_, sizeof(void*)*3 + 2, v___x_434_);
v___x_436_ = ((lean_object*)(l_Std_Time_DateTime_ofLocalDateWithZone___closed__0));
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_438_, 0, v_ltt_435_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
lean_ctor_set(v___x_438_, 2, v___x_437_);
v_wt_439_ = l_Std_Time_PlainDateTime_toWallTime(v___x_432_);
v_ltt_440_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_438_, v_wt_439_);
v_tz_441_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_440_);
lean_dec_ref(v_ltt_440_);
v_offset_442_ = lean_ctor_get(v_tz_441_, 0);
lean_inc(v_offset_442_);
lean_dec_ref(v_tz_441_);
v_second_443_ = lean_ctor_get(v_wt_439_, 0);
lean_inc(v_second_443_);
v_nano_444_ = lean_ctor_get(v_wt_439_, 1);
lean_inc(v_nano_444_);
lean_dec_ref(v_wt_439_);
v___x_445_ = lean_int_neg(v_offset_442_);
lean_dec(v_offset_442_);
v___x_446_ = lean_obj_once(&l_Std_Time_DateTime_ofLocalDate___closed__0, &l_Std_Time_DateTime_ofLocalDate___closed__0_once, _init_l_Std_Time_DateTime_ofLocalDate___closed__0);
v___x_447_ = lean_obj_once(&l_Std_Time_PlainDateTime_now___closed__1, &l_Std_Time_PlainDateTime_now___closed__1_once, _init_l_Std_Time_PlainDateTime_now___closed__1);
v___x_448_ = lean_int_mul(v_second_443_, v___x_447_);
lean_dec(v_second_443_);
v_nanos_449_ = lean_int_add(v___x_448_, v_nano_444_);
lean_dec(v_nano_444_);
lean_dec(v___x_448_);
v___x_450_ = lean_int_mul(v___x_445_, v___x_447_);
lean_dec(v___x_445_);
v_nanos_451_ = lean_int_add(v___x_450_, v___x_446_);
lean_dec(v___x_450_);
v___x_452_ = lean_int_add(v_nanos_449_, v_nanos_451_);
lean_dec(v_nanos_451_);
lean_dec(v_nanos_449_);
v___x_453_ = l_Std_Time_Duration_ofNanoseconds(v___x_452_);
lean_dec(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object* v_dt_454_, lean_object* v_tz_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Time_PlainDate_toTimestampWithZone(v_dt_454_, v_tz_455_);
lean_dec_ref(v_tz_455_);
return v_res_456_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
