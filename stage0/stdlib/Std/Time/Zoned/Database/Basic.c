// Lean compiler output
// Module: Std.Time.Zoned.Database.Basic
// Imports: public import Std.Time.Zoned.ZoneRules public import Std.Time.Zoned.Database.TzIf
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Int_instInhabited;
extern uint8_t l_instInhabitedUInt8;
extern lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertWall(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertWall___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertUt(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertUt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "cannot convert transition "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " of the file"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "cannot convert local time "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Time_TimeZone_convertTZifV1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_TimeZone_convertTZifV1___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_convertTZifV1___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_convertTZifV1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "empty transitions for "};
static const lean_object* l_Std_Time_TimeZone_convertTZifV1___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_convertTZifV1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertWall(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
else
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertWall___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_18__boxed_5_; uint8_t v_res_6_; lean_object* v_r_7_; 
v_x_18__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Time_TimeZone_convertWall(v_x_18__boxed_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_convertUt(uint8_t v_x_8_){
_start:
{
if (v_x_8_ == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertUt___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_18__boxed_12_; uint8_t v_res_13_; lean_object* v_r_14_; 
v_x_18__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Std_Time_TimeZone_convertUt(v_x_18__boxed_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType(lean_object* v_index_15_, lean_object* v_tz_16_, lean_object* v_identifier_17_){
_start:
{
lean_object* v_localTimeTypes_18_; lean_object* v_abbreviations_19_; lean_object* v_stdWallIndicators_20_; lean_object* v_utLocalIndicators_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_localTimeTypes_18_ = lean_ctor_get(v_tz_16_, 3);
v_abbreviations_19_ = lean_ctor_get(v_tz_16_, 4);
v_stdWallIndicators_20_ = lean_ctor_get(v_tz_16_, 6);
v_utLocalIndicators_21_ = lean_ctor_get(v_tz_16_, 7);
v___x_22_ = lean_array_get_size(v_localTimeTypes_18_);
v___x_23_ = lean_nat_dec_lt(v_index_15_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_dec_ref(v_identifier_17_);
v___x_24_ = lean_box(0);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v_gmtOffset_26_; uint8_t v_isDst_27_; uint8_t v___y_29_; lean_object* v___y_30_; uint8_t v___y_31_; lean_object* v___y_36_; uint8_t v___y_37_; lean_object* v___y_44_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_25_ = lean_array_fget_borrowed(v_localTimeTypes_18_, v_index_15_);
v_gmtOffset_26_ = lean_ctor_get(v___x_25_, 0);
v_isDst_27_ = lean_ctor_get_uint8(v___x_25_, sizeof(void*)*1);
v___x_49_ = lean_array_get_size(v_abbreviations_19_);
v___x_50_ = lean_nat_dec_lt(v_index_15_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_inc(v_gmtOffset_26_);
v___x_51_ = l_Std_Time_TimeZone_Offset_toIsoString(v_gmtOffset_26_, v___x_23_);
v___y_44_ = v___x_51_;
goto v___jp_43_;
}
else
{
lean_object* v___x_52_; 
v___x_52_ = lean_array_fget_borrowed(v_abbreviations_19_, v_index_15_);
lean_inc(v___x_52_);
v___y_44_ = v___x_52_;
goto v___jp_43_;
}
v___jp_28_:
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = l_Std_Time_TimeZone_convertUt(v___y_31_);
lean_inc(v_gmtOffset_26_);
v___x_33_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_33_, 0, v_gmtOffset_26_);
lean_ctor_set(v___x_33_, 1, v___y_30_);
lean_ctor_set(v___x_33_, 2, v_identifier_17_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*3, v_isDst_27_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*3 + 1, v___y_29_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*3 + 2, v___x_32_);
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
v___jp_35_:
{
uint8_t v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = l_Std_Time_TimeZone_convertWall(v___y_37_);
v___x_39_ = lean_array_get_size(v_utLocalIndicators_21_);
v___x_40_ = lean_nat_dec_lt(v_index_15_, v___x_39_);
if (v___x_40_ == 0)
{
v___y_29_ = v___x_38_;
v___y_30_ = v___y_36_;
v___y_31_ = v___x_23_;
goto v___jp_28_;
}
else
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_array_fget_borrowed(v_utLocalIndicators_21_, v_index_15_);
v___x_42_ = lean_unbox(v___x_41_);
v___y_29_ = v___x_38_;
v___y_30_ = v___y_36_;
v___y_31_ = v___x_42_;
goto v___jp_28_;
}
}
v___jp_43_:
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_array_get_size(v_stdWallIndicators_20_);
v___x_46_ = lean_nat_dec_lt(v_index_15_, v___x_45_);
if (v___x_46_ == 0)
{
v___y_36_ = v___y_44_;
v___y_37_ = v___x_23_;
goto v___jp_35_;
}
else
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_array_fget_borrowed(v_stdWallIndicators_20_, v_index_15_);
v___x_48_ = lean_unbox(v___x_47_);
v___y_36_ = v___y_44_;
v___y_37_ = v___x_48_;
goto v___jp_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType___boxed(lean_object* v_index_53_, lean_object* v_tz_54_, lean_object* v_identifier_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Time_TimeZone_convertLocalTimeType(v_index_53_, v_tz_54_, v_identifier_55_);
lean_dec_ref(v_tz_54_);
lean_dec(v_index_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0_spec__0(lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_nat_to_int(v_a_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0(lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_nat_to_int(v_a_59_);
v___x_61_ = l_Rat_ofInt(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition(lean_object* v_times_62_, lean_object* v_index_63_, lean_object* v_tz_64_){
_start:
{
lean_object* v_transitionTimes_65_; lean_object* v_transitionIndices_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v_time_70_; lean_object* v___x_71_; lean_object* v_indice_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_transitionTimes_65_ = lean_ctor_get(v_tz_64_, 1);
v_transitionIndices_66_ = lean_ctor_get(v_tz_64_, 2);
v___x_67_ = l_Int_instInhabited;
v___x_68_ = l_instInhabitedUInt8;
v___x_69_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v_time_70_ = lean_array_get_borrowed(v___x_67_, v_transitionTimes_65_, v_index_63_);
v___x_71_ = lean_box(v___x_68_);
v_indice_72_ = lean_array_get_borrowed(v___x_71_, v_transitionIndices_66_, v_index_63_);
v___x_73_ = lean_unbox(v_indice_72_);
v___x_74_ = lean_uint8_to_nat(v___x_73_);
v___x_75_ = lean_array_get_borrowed(v___x_69_, v_times_62_, v___x_74_);
lean_inc(v___x_75_);
lean_inc(v_time_70_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_time_70_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition___boxed(lean_object* v_times_78_, lean_object* v_index_79_, lean_object* v_tz_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_Time_TimeZone_convertTransition(v_times_78_, v_index_79_, v_tz_80_);
lean_dec_ref(v_tz_80_);
lean_dec(v_index_79_);
lean_dec_ref(v_times_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(lean_object* v_upperBound_84_, lean_object* v_a_85_, lean_object* v_tz_86_, lean_object* v_a_87_, lean_object* v_b_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_nat_dec_lt(v_a_87_, v_upperBound_84_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec(v_a_87_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v_b_88_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_Time_TimeZone_convertTransition(v_a_85_, v_a_87_, v_tz_86_);
if (lean_obj_tag(v___x_91_) == 1)
{
lean_object* v_val_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_val_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_val_92_);
lean_dec_ref(v___x_91_);
v___x_93_ = lean_array_push(v_b_88_, v_val_92_);
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_a_87_, v___x_94_);
lean_dec(v_a_87_);
v_a_87_ = v___x_95_;
v_b_88_ = v___x_93_;
goto _start;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v___x_91_);
lean_dec_ref(v_b_88_);
v___x_97_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0));
v___x_98_ = l_Nat_reprFast(v_a_87_);
v___x_99_ = lean_string_append(v___x_97_, v___x_98_);
lean_dec_ref(v___x_98_);
v___x_100_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1));
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___boxed(lean_object* v_upperBound_103_, lean_object* v_a_104_, lean_object* v_tz_105_, lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(v_upperBound_103_, v_a_104_, v_tz_105_, v_a_106_, v_b_107_);
lean_dec_ref(v_tz_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_upperBound_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(lean_object* v_upperBound_110_, lean_object* v_tz_111_, lean_object* v_id_112_, lean_object* v_a_113_, lean_object* v_b_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = lean_nat_dec_lt(v_a_113_, v_upperBound_110_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
lean_dec(v_a_113_);
lean_dec_ref(v_id_112_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_b_114_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; 
lean_inc_ref(v_id_112_);
v___x_117_ = l_Std_Time_TimeZone_convertLocalTimeType(v_a_113_, v_tz_111_, v_id_112_);
if (lean_obj_tag(v___x_117_) == 1)
{
lean_object* v_val_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_val_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_118_);
lean_dec_ref(v___x_117_);
v___x_119_ = lean_array_push(v_b_114_, v_val_118_);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_a_113_, v___x_120_);
lean_dec(v_a_113_);
v_a_113_ = v___x_121_;
v_b_114_ = v___x_119_;
goto _start;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v___x_117_);
lean_dec_ref(v_b_114_);
lean_dec_ref(v_id_112_);
v___x_123_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0));
v___x_124_ = l_Nat_reprFast(v_a_113_);
v___x_125_ = lean_string_append(v___x_123_, v___x_124_);
lean_dec_ref(v___x_124_);
v___x_126_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___boxed(lean_object* v_upperBound_129_, lean_object* v_tz_130_, lean_object* v_id_131_, lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(v_upperBound_129_, v_tz_130_, v_id_131_, v_a_132_, v_b_133_);
lean_dec_ref(v_tz_130_);
lean_dec(v_upperBound_129_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1(lean_object* v_tz_138_, lean_object* v_id_139_){
_start:
{
lean_object* v_header_140_; lean_object* v_transitionTimes_141_; uint32_t v_typecnt_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_times_145_; lean_object* v___x_146_; 
v_header_140_ = lean_ctor_get(v_tz_138_, 0);
v_transitionTimes_141_ = lean_ctor_get(v_tz_138_, 1);
v_typecnt_142_ = lean_ctor_get_uint32(v_header_140_, 16);
v___x_143_ = lean_uint32_to_nat(v_typecnt_142_);
v___x_144_ = lean_unsigned_to_nat(0u);
v_times_145_ = ((lean_object*)(l_Std_Time_TimeZone_convertTZifV1___closed__0));
lean_inc_ref(v_id_139_);
v___x_146_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(v___x_143_, v_tz_138_, v_id_139_, v___x_144_, v_times_145_);
lean_dec(v___x_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v_id_139_);
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
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
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_a_155_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_146_);
v___x_156_ = lean_array_get_size(v_transitionTimes_141_);
v___x_157_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(v___x_156_, v_a_155_, v_tz_138_, v___x_144_, v_times_145_);
lean_dec(v_a_155_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
lean_dec_ref(v_id_139_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_181_; 
v_a_166_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_181_ == 0)
{
v___x_168_ = v___x_157_;
v_isShared_169_ = v_isSharedCheck_181_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_157_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_181_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; 
lean_inc_ref(v_id_139_);
v___x_170_ = l_Std_Time_TimeZone_convertLocalTimeType(v___x_144_, v_tz_138_, v_id_139_);
if (lean_obj_tag(v___x_170_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
lean_dec_ref(v_id_139_);
v_val_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_val_171_);
lean_ctor_set(v___x_172_, 1, v_a_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_172_);
v___x_174_ = v___x_168_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
lean_dec(v___x_170_);
lean_dec(v_a_166_);
v___x_176_ = ((lean_object*)(l_Std_Time_TimeZone_convertTZifV1___closed__1));
v___x_177_ = lean_string_append(v___x_176_, v_id_139_);
lean_dec_ref(v_id_139_);
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 0);
lean_ctor_set(v___x_168_, 0, v___x_177_);
v___x_179_ = v___x_168_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___boxed(lean_object* v_tz_182_, lean_object* v_id_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_Time_TimeZone_convertTZifV1(v_tz_182_, v_id_183_);
lean_dec_ref(v_tz_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0(lean_object* v_upperBound_185_, lean_object* v_a_186_, lean_object* v_tz_187_, lean_object* v_inst_188_, lean_object* v_R_189_, lean_object* v_a_190_, lean_object* v_b_191_, lean_object* v_c_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(v_upperBound_185_, v_a_186_, v_tz_187_, v_a_190_, v_b_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___boxed(lean_object* v_upperBound_194_, lean_object* v_a_195_, lean_object* v_tz_196_, lean_object* v_inst_197_, lean_object* v_R_198_, lean_object* v_a_199_, lean_object* v_b_200_, lean_object* v_c_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0(v_upperBound_194_, v_a_195_, v_tz_196_, v_inst_197_, v_R_198_, v_a_199_, v_b_200_, v_c_201_);
lean_dec_ref(v_tz_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_upperBound_194_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1(lean_object* v_upperBound_203_, lean_object* v_tz_204_, lean_object* v_id_205_, lean_object* v_inst_206_, lean_object* v_R_207_, lean_object* v_a_208_, lean_object* v_b_209_, lean_object* v_c_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(v_upperBound_203_, v_tz_204_, v_id_205_, v_a_208_, v_b_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___boxed(lean_object* v_upperBound_212_, lean_object* v_tz_213_, lean_object* v_id_214_, lean_object* v_inst_215_, lean_object* v_R_216_, lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v_c_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1(v_upperBound_212_, v_tz_213_, v_id_214_, v_inst_215_, v_R_216_, v_a_217_, v_b_218_, v_c_219_);
lean_dec_ref(v_tz_213_);
lean_dec(v_upperBound_212_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2(lean_object* v_tz_221_, lean_object* v_id_222_){
_start:
{
lean_object* v_toTZifV1_223_; lean_object* v___x_224_; 
v_toTZifV1_223_ = lean_ctor_get(v_tz_221_, 0);
v___x_224_ = l_Std_Time_TimeZone_convertTZifV1(v_toTZifV1_223_, v_id_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2___boxed(lean_object* v_tz_225_, lean_object* v_id_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Time_TimeZone_convertTZifV2(v_tz_225_, v_id_226_);
lean_dec_ref(v_tz_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif(lean_object* v_tz_228_, lean_object* v_id_229_){
_start:
{
lean_object* v_v2_230_; 
v_v2_230_ = lean_ctor_get(v_tz_228_, 1);
if (lean_obj_tag(v_v2_230_) == 1)
{
lean_object* v_val_231_; lean_object* v___x_232_; 
v_val_231_ = lean_ctor_get(v_v2_230_, 0);
v___x_232_ = l_Std_Time_TimeZone_convertTZifV2(v_val_231_, v_id_229_);
return v___x_232_;
}
else
{
lean_object* v_v1_233_; lean_object* v___x_234_; 
v_v1_233_ = lean_ctor_get(v_tz_228_, 0);
v___x_234_ = l_Std_Time_TimeZone_convertTZifV1(v_v1_233_, v_id_229_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif___boxed(lean_object* v_tz_235_, lean_object* v_id_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Time_TimeZone_convertTZif(v_tz_235_, v_id_236_);
lean_dec_ref(v_tz_235_);
return v_res_237_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TzIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_TzIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
