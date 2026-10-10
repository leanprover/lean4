// Lean compiler output
// Module: Std.Time.Zoned.Database.Basic
// Imports: public import Std.Time.Zoned.ZoneRules public import Std.Time.Zoned.Database.TzIf import Std.Time.Zoned.Database.PosixTz
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
extern lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object*, uint8_t);
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
static const lean_string_object l_Std_Time_TimeZone_convertTZifV2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_TimeZone_convertTZifV2___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_convertTZifV2___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_convertTZifV2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "failed to parse tzif footer: "};
static const lean_object* l_Std_Time_TimeZone_convertTZifV2___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_convertTZifV2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif(lean_object*, lean_object*);
uint8_t l_Std_Time_TimeZone_convertWall(uint8_t v_x_1_){
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
LEAN_EXPORT void l_Std_Time_TimeZone_convertWall_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
uint8_t v_res_4_;
v_res_4_ = l_Std_Time_TimeZone_convertWall(v_x_1_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertWall___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_18__boxed_6_; uint8_t v_res_7_; lean_object* v_r_8_; 
v_x_18__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Time_TimeZone_convertWall(v_x_18__boxed_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint8_t l_Std_Time_TimeZone_convertUt(uint8_t v_x_9_){
_start:
{
if (v_x_9_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 1;
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_convertUt_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_9_ = stack[0].m_num;
uint8_t v_res_12_;
v_res_12_ = l_Std_Time_TimeZone_convertUt(v_x_9_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertUt___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_x_18__boxed_14_; uint8_t v_res_15_; lean_object* v_r_16_; 
v_x_18__boxed_14_ = lean_unbox(v_x_13_);
v_res_15_ = l_Std_Time_TimeZone_convertUt(v_x_18__boxed_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType(lean_object* v_index_17_, lean_object* v_tz_18_, lean_object* v_identifier_19_){
_start:
{
lean_object* v_localTimeTypes_20_; lean_object* v_abbreviations_21_; lean_object* v_stdWallIndicators_22_; lean_object* v_utLocalIndicators_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_localTimeTypes_20_ = lean_ctor_get(v_tz_18_, 3);
v_abbreviations_21_ = lean_ctor_get(v_tz_18_, 4);
v_stdWallIndicators_22_ = lean_ctor_get(v_tz_18_, 6);
v_utLocalIndicators_23_ = lean_ctor_get(v_tz_18_, 7);
v___x_24_ = lean_array_get_size(v_localTimeTypes_20_);
v___x_25_ = lean_nat_dec_lt(v_index_17_, v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
lean_dec_ref(v_identifier_19_);
v___x_26_ = lean_box(0);
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v_gmtOffset_28_; uint8_t v_isDst_29_; uint8_t v___y_31_; lean_object* v___y_32_; uint8_t v___y_33_; lean_object* v___y_38_; uint8_t v___y_39_; lean_object* v___y_46_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_27_ = lean_array_fget_borrowed(v_localTimeTypes_20_, v_index_17_);
v_gmtOffset_28_ = lean_ctor_get(v___x_27_, 0);
v_isDst_29_ = lean_ctor_get_uint8(v___x_27_, sizeof(void*)*1);
v___x_51_ = lean_array_get_size(v_abbreviations_21_);
v___x_52_ = lean_nat_dec_lt(v_index_17_, v___x_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; 
lean_inc(v_gmtOffset_28_);
v___x_53_ = l_Std_Time_TimeZone_Offset_toIsoString(v_gmtOffset_28_, v___x_25_);
v___y_46_ = v___x_53_;
goto v___jp_45_;
}
else
{
lean_object* v___x_54_; 
v___x_54_ = lean_array_fget_borrowed(v_abbreviations_21_, v_index_17_);
lean_inc(v___x_54_);
v___y_46_ = v___x_54_;
goto v___jp_45_;
}
v___jp_30_:
{
uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = l_Std_Time_TimeZone_convertUt(v___y_33_);
lean_inc(v_gmtOffset_28_);
v___x_35_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_35_, 0, v_gmtOffset_28_);
lean_ctor_set(v___x_35_, 1, v___y_32_);
lean_ctor_set(v___x_35_, 2, v_identifier_19_);
lean_ctor_set_uint8(v___x_35_, sizeof(void*)*3, v_isDst_29_);
lean_ctor_set_uint8(v___x_35_, sizeof(void*)*3 + 1, v___y_31_);
lean_ctor_set_uint8(v___x_35_, sizeof(void*)*3 + 2, v___x_34_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
v___jp_37_:
{
uint8_t v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_40_ = l_Std_Time_TimeZone_convertWall(v___y_39_);
v___x_41_ = lean_array_get_size(v_utLocalIndicators_23_);
v___x_42_ = lean_nat_dec_lt(v_index_17_, v___x_41_);
if (v___x_42_ == 0)
{
v___y_31_ = v___x_40_;
v___y_32_ = v___y_38_;
v___y_33_ = v___x_25_;
goto v___jp_30_;
}
else
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_array_fget_borrowed(v_utLocalIndicators_23_, v_index_17_);
v___x_44_ = lean_unbox(v___x_43_);
v___y_31_ = v___x_40_;
v___y_32_ = v___y_38_;
v___y_33_ = v___x_44_;
goto v___jp_30_;
}
}
v___jp_45_:
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_array_get_size(v_stdWallIndicators_22_);
v___x_48_ = lean_nat_dec_lt(v_index_17_, v___x_47_);
if (v___x_48_ == 0)
{
v___y_38_ = v___y_46_;
v___y_39_ = v___x_25_;
goto v___jp_37_;
}
else
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_array_fget_borrowed(v_stdWallIndicators_22_, v_index_17_);
v___x_50_ = lean_unbox(v___x_49_);
v___y_38_ = v___y_46_;
v___y_39_ = v___x_50_;
goto v___jp_37_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertLocalTimeType___boxed(lean_object* v_index_55_, lean_object* v_tz_56_, lean_object* v_identifier_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Time_TimeZone_convertLocalTimeType(v_index_55_, v_tz_56_, v_identifier_57_);
lean_dec_ref(v_tz_56_);
lean_dec(v_index_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0_spec__0(lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_nat_to_int(v_a_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0(lean_object* v_a_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_nat_to_int(v_a_61_);
v___x_63_ = l_Rat_ofInt(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition(lean_object* v_times_64_, lean_object* v_index_65_, lean_object* v_tz_66_){
_start:
{
lean_object* v_transitionTimes_67_; lean_object* v_transitionIndices_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v_time_72_; lean_object* v___x_73_; lean_object* v_indice_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_transitionTimes_67_ = lean_ctor_get(v_tz_66_, 1);
v_transitionIndices_68_ = lean_ctor_get(v_tz_66_, 2);
v___x_69_ = l_Int_instInhabited;
v___x_70_ = 0;
v___x_71_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v_time_72_ = lean_array_get_borrowed(v___x_69_, v_transitionTimes_67_, v_index_65_);
v___x_73_ = lean_box(v___x_70_);
v_indice_74_ = lean_array_get(v___x_73_, v_transitionIndices_68_, v_index_65_);
lean_dec(v___x_73_);
v___x_75_ = lean_unbox(v_indice_74_);
lean_dec(v_indice_74_);
v___x_76_ = lean_uint8_to_nat(v___x_75_);
v___x_77_ = lean_array_get_borrowed(v___x_71_, v_times_64_, v___x_76_);
lean_inc(v___x_77_);
lean_inc(v_time_72_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v_time_72_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTransition___boxed(lean_object* v_times_80_, lean_object* v_index_81_, lean_object* v_tz_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Time_TimeZone_convertTransition(v_times_80_, v_index_81_, v_tz_82_);
lean_dec_ref(v_tz_82_);
lean_dec(v_index_81_);
lean_dec_ref(v_times_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(lean_object* v_upperBound_86_, lean_object* v_a_87_, lean_object* v_tz_88_, lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_nat_dec_lt(v_a_89_, v_upperBound_86_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_dec(v_a_89_);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v_b_90_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_Time_TimeZone_convertTransition(v_a_87_, v_a_89_, v_tz_88_);
if (lean_obj_tag(v___x_93_) == 1)
{
lean_object* v_val_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_val_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_val_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = lean_array_push(v_b_90_, v_val_94_);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_add(v_a_89_, v___x_96_);
lean_dec(v_a_89_);
v_a_89_ = v___x_97_;
v_b_90_ = v___x_95_;
goto _start;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v___x_93_);
lean_dec_ref(v_b_90_);
v___x_99_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0));
v___x_100_ = l_Nat_reprFast(v_a_89_);
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
lean_dec_ref(v___x_100_);
v___x_102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1));
v___x_103_ = lean_string_append(v___x_101_, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___boxed(lean_object* v_upperBound_105_, lean_object* v_a_106_, lean_object* v_tz_107_, lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(v_upperBound_105_, v_a_106_, v_tz_107_, v_a_108_, v_b_109_);
lean_dec_ref(v_tz_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_upperBound_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(lean_object* v_upperBound_112_, lean_object* v_tz_113_, lean_object* v_id_114_, lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = lean_nat_dec_lt(v_a_115_, v_upperBound_112_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_dec(v_a_115_);
lean_dec_ref(v_id_114_);
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v_b_116_);
return v___x_118_;
}
else
{
lean_object* v___x_119_; 
lean_inc_ref(v_id_114_);
v___x_119_ = l_Std_Time_TimeZone_convertLocalTimeType(v_a_115_, v_tz_113_, v_id_114_);
if (lean_obj_tag(v___x_119_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_val_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v___x_119_, 1);
v___x_121_ = lean_array_push(v_b_116_, v_val_120_);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v_a_115_, v___x_122_);
lean_dec(v_a_115_);
v_a_115_ = v___x_123_;
v_b_116_ = v___x_121_;
goto _start;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v___x_119_);
lean_dec_ref(v_b_116_);
lean_dec_ref(v_id_114_);
v___x_125_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0));
v___x_126_ = l_Nat_reprFast(v_a_115_);
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
lean_dec_ref(v___x_126_);
v___x_128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1));
v___x_129_ = lean_string_append(v___x_127_, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___boxed(lean_object* v_upperBound_131_, lean_object* v_tz_132_, lean_object* v_id_133_, lean_object* v_a_134_, lean_object* v_b_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(v_upperBound_131_, v_tz_132_, v_id_133_, v_a_134_, v_b_135_);
lean_dec_ref(v_tz_132_);
lean_dec(v_upperBound_131_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1(lean_object* v_tz_140_, lean_object* v_id_141_){
_start:
{
lean_object* v_header_142_; lean_object* v_transitionTimes_143_; uint32_t v_typecnt_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_times_147_; lean_object* v___x_148_; 
v_header_142_ = lean_ctor_get(v_tz_140_, 0);
v_transitionTimes_143_ = lean_ctor_get(v_tz_140_, 1);
v_typecnt_144_ = lean_ctor_get_uint32(v_header_142_, 16);
v___x_145_ = lean_uint32_to_nat(v_typecnt_144_);
v___x_146_ = lean_unsigned_to_nat(0u);
v_times_147_ = ((lean_object*)(l_Std_Time_TimeZone_convertTZifV1___closed__0));
lean_inc_ref(v_id_141_);
v___x_148_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(v___x_145_, v_tz_140_, v_id_141_, v___x_146_, v_times_147_);
lean_dec(v___x_145_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v_id_141_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_a_157_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_148_, 1);
v___x_158_ = lean_array_get_size(v_transitionTimes_143_);
v___x_159_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(v___x_158_, v_a_157_, v_tz_140_, v___x_146_, v_times_147_);
lean_dec(v_a_157_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_id_141_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
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
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_184_; 
v_a_168_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_184_ == 0)
{
v___x_170_ = v___x_159_;
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_159_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; 
lean_inc_ref(v_id_141_);
v___x_172_ = l_Std_Time_TimeZone_convertLocalTimeType(v___x_146_, v_tz_140_, v_id_141_);
if (lean_obj_tag(v___x_172_) == 1)
{
lean_object* v_val_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
lean_dec_ref(v_id_141_);
v_val_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = lean_box(0);
v___x_175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_175_, 0, v_val_173_);
lean_ctor_set(v___x_175_, 1, v_a_168_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_175_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
lean_dec(v___x_172_);
lean_dec(v_a_168_);
v___x_179_ = ((lean_object*)(l_Std_Time_TimeZone_convertTZifV1___closed__1));
v___x_180_ = lean_string_append(v___x_179_, v_id_141_);
lean_dec_ref(v_id_141_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 0);
lean_ctor_set(v___x_170_, 0, v___x_180_);
v___x_182_ = v___x_170_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV1___boxed(lean_object* v_tz_185_, lean_object* v_id_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Time_TimeZone_convertTZifV1(v_tz_185_, v_id_186_);
lean_dec_ref(v_tz_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0(lean_object* v_upperBound_188_, lean_object* v_a_189_, lean_object* v_tz_190_, lean_object* v_inst_191_, lean_object* v_R_192_, lean_object* v_a_193_, lean_object* v_b_194_, lean_object* v_c_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(v_upperBound_188_, v_a_189_, v_tz_190_, v_a_193_, v_b_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___boxed(lean_object* v_upperBound_197_, lean_object* v_a_198_, lean_object* v_tz_199_, lean_object* v_inst_200_, lean_object* v_R_201_, lean_object* v_a_202_, lean_object* v_b_203_, lean_object* v_c_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0(v_upperBound_197_, v_a_198_, v_tz_199_, v_inst_200_, v_R_201_, v_a_202_, v_b_203_, v_c_204_);
lean_dec_ref(v_tz_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_upperBound_197_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1(lean_object* v_upperBound_206_, lean_object* v_tz_207_, lean_object* v_id_208_, lean_object* v_inst_209_, lean_object* v_R_210_, lean_object* v_a_211_, lean_object* v_b_212_, lean_object* v_c_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(v_upperBound_206_, v_tz_207_, v_id_208_, v_a_211_, v_b_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___boxed(lean_object* v_upperBound_215_, lean_object* v_tz_216_, lean_object* v_id_217_, lean_object* v_inst_218_, lean_object* v_R_219_, lean_object* v_a_220_, lean_object* v_b_221_, lean_object* v_c_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1(v_upperBound_215_, v_tz_216_, v_id_217_, v_inst_218_, v_R_219_, v_a_220_, v_b_221_, v_c_222_);
lean_dec_ref(v_tz_216_);
lean_dec(v_upperBound_215_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZifV2(lean_object* v_tz_226_, lean_object* v_id_227_){
_start:
{
lean_object* v_toTZifV1_228_; lean_object* v_footer_229_; lean_object* v___x_230_; 
v_toTZifV1_228_ = lean_ctor_get(v_tz_226_, 0);
lean_inc_ref(v_toTZifV1_228_);
v_footer_229_ = lean_ctor_get(v_tz_226_, 1);
lean_inc(v_footer_229_);
lean_dec_ref(v_tz_226_);
v___x_230_ = l_Std_Time_TimeZone_convertTZifV1(v_toTZifV1_228_, v_id_227_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_dec(v_footer_229_);
lean_dec_ref(v_toTZifV1_228_);
return v___x_230_;
}
else
{
if (lean_obj_tag(v_footer_229_) == 1)
{
lean_object* v_header_231_; lean_object* v_a_232_; lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_274_; 
v_header_231_ = lean_ctor_get(v_toTZifV1_228_, 0);
lean_inc_ref(v_header_231_);
lean_dec_ref(v_toTZifV1_228_);
v_a_232_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_232_);
v_val_233_ = lean_ctor_get(v_footer_229_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_footer_229_);
if (v_isSharedCheck_274_ == 0)
{
v___x_235_ = v_footer_229_;
v_isShared_236_ = v_isSharedCheck_274_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v_footer_229_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_274_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v_version_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_version_237_ = lean_ctor_get_uint8(v_header_231_, 24);
lean_dec_ref(v_header_231_);
v___x_238_ = ((lean_object*)(l_Std_Time_TimeZone_convertTZifV2___closed__0));
v___x_239_ = lean_string_dec_eq(v_val_233_, v___x_238_);
if (v___x_239_ == 0)
{
uint8_t v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; 
lean_dec_ref_known(v___x_230_, 1);
v___x_240_ = 51;
v___x_241_ = lean_uint8_dec_eq(v_version_237_, v___x_240_);
v___x_242_ = l_Std_Time_TimeZone_parsePosixTz(v_val_233_, v___x_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
lean_del_object(v___x_235_);
lean_dec(v_a_232_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_252_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = ((lean_object*)(l_Std_Time_TimeZone_convertTZifV2___closed__1));
v___x_248_ = lean_string_append(v___x_247_, v_a_243_);
lean_dec(v_a_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_248_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_273_; 
v_a_253_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_273_ == 0)
{
v___x_255_ = v___x_242_;
v_isShared_256_ = v_isSharedCheck_273_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_242_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_273_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v_initialLocalTimeType_257_; lean_object* v_transitions_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_271_; 
v_initialLocalTimeType_257_ = lean_ctor_get(v_a_232_, 0);
v_transitions_258_ = lean_ctor_get(v_a_232_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_a_232_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_a_232_, 2);
lean_dec(v_unused_272_);
v___x_260_ = v_a_232_;
v_isShared_261_ = v_isSharedCheck_271_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_transitions_258_);
lean_inc(v_initialLocalTimeType_257_);
lean_dec(v_a_232_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_271_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v_a_253_);
v___x_263_ = v___x_235_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_253_);
v___x_263_ = v_reuseFailAlloc_270_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_265_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 2, v___x_263_);
v___x_265_ = v___x_260_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_initialLocalTimeType_257_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_transitions_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v___x_263_);
v___x_265_ = v_reuseFailAlloc_269_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_267_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_265_);
v___x_267_ = v___x_255_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_235_);
lean_dec(v_val_233_);
lean_dec(v_a_232_);
return v___x_230_;
}
}
}
else
{
lean_dec(v_footer_229_);
lean_dec_ref(v_toTZifV1_228_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_convertTZif(lean_object* v_tz_275_, lean_object* v_id_276_){
_start:
{
lean_object* v_v2_277_; 
v_v2_277_ = lean_ctor_get(v_tz_275_, 1);
if (lean_obj_tag(v_v2_277_) == 1)
{
lean_object* v_val_278_; lean_object* v___x_279_; 
lean_inc_ref(v_v2_277_);
lean_dec_ref(v_tz_275_);
v_val_278_ = lean_ctor_get(v_v2_277_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v_v2_277_, 1);
v___x_279_ = l_Std_Time_TimeZone_convertTZifV2(v_val_278_, v_id_276_);
return v___x_279_;
}
else
{
lean_object* v_v1_280_; lean_object* v___x_281_; 
v_v1_280_ = lean_ctor_get(v_tz_275_, 0);
lean_inc_ref(v_v1_280_);
lean_dec_ref(v_tz_275_);
v___x_281_ = l_Std_Time_TimeZone_convertTZifV1(v_v1_280_, v_id_276_);
lean_dec_ref(v_v1_280_);
return v___x_281_;
}
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_PosixTz(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TzIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_PosixTz(builtin);
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
lean_object* initialize_Std_Time_Zoned_Database_PosixTz(uint8_t builtin);
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
res = initialize_Std_Time_Zoned_Database_PosixTz(builtin);
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
