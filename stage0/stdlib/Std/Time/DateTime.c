// Lean compiler output
// Module: Std.Time.DateTime
// Imports: public import Std.Time.DateTime.Timestamp public import Std.Time.DateTime.PlainDateTime import all Std.Time.Date.Unit.Month
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
extern lean_object* l_Std_Time_PlainTime_midnight;
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateTimeAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0;
static lean_once_cell_t l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_instHSubDuration___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHSubDuration = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__2;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__3;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__4;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__5;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__6;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__7;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__8;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__9;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__10;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__11;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__12;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__13;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__14;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__15;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__16;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__17;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__18;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_instHSubDuration___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubDuration = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateTimeAssumingUTC(lean_object* v_pdt_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(lean_object* v_timestamp_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(86400u);
v___x_6_ = lean_nat_to_int(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC(lean_object* v_pd_9_){
_start:
{
lean_object* v_days_10_; lean_object* v___x_11_; lean_object* v_secs_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_days_10_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_pd_9_);
v___x_11_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
v_secs_12_ = lean_int_mul(v_days_10_, v___x_11_);
lean_dec(v_days_10_);
v___x_13_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_secs_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC(lean_object* v_timestamp_15_){
_start:
{
lean_object* v_second_16_; lean_object* v___x_17_; lean_object* v_days_18_; lean_object* v___x_19_; 
v_second_16_ = lean_ctor_get(v_timestamp_15_, 0);
v___x_17_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
v_days_18_ = lean_int_ediv(v_second_16_, v___x_17_);
v___x_19_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_days_18_);
lean_dec(v_days_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC___boxed(lean_object* v_timestamp_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Time_Timestamp_toPlainDateAssumingUTC(v_timestamp_20_);
lean_dec_ref(v_timestamp_20_);
return v_res_21_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1000000000u);
v___x_23_ = lean_nat_to_int(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC(lean_object* v_timestamp_24_){
_start:
{
lean_object* v_second_25_; lean_object* v_nano_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v_nanos_29_; lean_object* v___x_30_; 
v_second_25_ = lean_ctor_get(v_timestamp_24_, 0);
v_nano_26_ = lean_ctor_get(v_timestamp_24_, 1);
v___x_27_ = lean_obj_once(&l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0, &l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0);
v___x_28_ = lean_int_mul(v_second_25_, v___x_27_);
v_nanos_29_ = lean_int_add(v___x_28_, v_nano_26_);
lean_dec(v___x_28_);
v___x_30_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_29_);
lean_dec(v_nanos_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___boxed(lean_object* v_timestamp_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_Time_Timestamp_getTimeAssumingUTC(v_timestamp_31_);
lean_dec_ref(v_timestamp_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object* v_pdt_33_){
_start:
{
lean_object* v_days_34_; lean_object* v___x_35_; lean_object* v_secs_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_days_34_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_pdt_33_);
v___x_35_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
v_secs_36_ = lean_int_mul(v_days_34_, v___x_35_);
lean_dec(v_days_34_);
v___x_37_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_secs_36_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
v___x_40_ = lean_int_neg(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* v_x_41_, lean_object* v_y_42_){
_start:
{
lean_object* v_days_43_; lean_object* v___x_44_; lean_object* v_secs_45_; lean_object* v___x_46_; lean_object* v_days_47_; lean_object* v_secs_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_days_43_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_x_41_);
v___x_44_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
v_secs_45_ = lean_int_mul(v_days_43_, v___x_44_);
lean_dec(v_days_43_);
v___x_46_ = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
v_days_47_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_y_42_);
v_secs_48_ = lean_int_mul(v_days_47_, v___x_44_);
lean_dec(v_days_47_);
v___x_49_ = lean_int_neg(v_secs_48_);
lean_dec(v_secs_48_);
v___x_50_ = lean_obj_once(&l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0, &l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0);
v___x_51_ = lean_obj_once(&l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0, &l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0);
v___x_52_ = lean_int_mul(v_secs_45_, v___x_51_);
lean_dec(v_secs_45_);
v___x_53_ = lean_int_add(v___x_52_, v___x_46_);
lean_dec(v___x_52_);
v___x_54_ = lean_int_mul(v___x_49_, v___x_51_);
lean_dec(v___x_49_);
v___x_55_ = lean_int_add(v___x_54_, v___x_50_);
lean_dec(v___x_54_);
v___x_56_ = lean_int_add(v___x_53_, v___x_55_);
lean_dec(v___x_55_);
lean_dec(v___x_53_);
v___x_57_ = l_Std_Time_Duration_ofNanoseconds(v___x_56_);
lean_dec(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* v_date_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = l_Std_Time_PlainTime_midnight;
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_date_60_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* v_pdt_63_){
_start:
{
lean_object* v_date_64_; 
v_date_64_ = lean_ctor_get(v_pdt_63_, 0);
lean_inc_ref(v_date_64_);
return v_date_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* v_pdt_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_65_);
lean_dec_ref(v_pdt_65_);
return v_res_66_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(11u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__1, &l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1);
v___x_72_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_73_ = lean_int_add(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_75_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__2, &l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2);
v___x_76_ = lean_int_sub(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v_range_79_; 
v___x_77_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_78_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__3, &l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3);
v_range_79_ = lean_int_add(v___x_78_, v___x_77_);
return v_range_79_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_81_ = lean_int_sub(v___x_80_, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6(void){
_start:
{
lean_object* v_range_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_range_82_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
v___x_83_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__5, &l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5);
v___x_84_ = lean_int_emod(v___x_83_, v_range_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7(void){
_start:
{
lean_object* v_range_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_range_85_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
v___x_86_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__6, &l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6);
v___x_87_ = lean_int_add(v___x_86_, v_range_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8(void){
_start:
{
lean_object* v_range_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_range_88_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
v___x_89_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__7, &l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7);
v___x_90_ = lean_int_emod(v___x_89_, v_range_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_92_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__8, &l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8);
v___x_93_ = lean_int_add(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(30u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__10, &l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10);
v___x_97_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_98_ = lean_int_add(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_100_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__11, &l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11);
v___x_101_ = lean_int_sub(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_range_104_; 
v___x_102_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_103_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__12, &l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12);
v_range_104_ = lean_int_add(v___x_103_, v___x_102_);
return v_range_104_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14(void){
_start:
{
lean_object* v_range_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_range_105_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
v___x_106_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__5, &l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5);
v___x_107_ = lean_int_emod(v___x_106_, v_range_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15(void){
_start:
{
lean_object* v_range_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_range_108_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
v___x_109_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__14, &l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14);
v___x_110_ = lean_int_add(v___x_109_, v_range_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16(void){
_start:
{
lean_object* v_range_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_range_111_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
v___x_112_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__15, &l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15);
v___x_113_ = lean_int_emod(v___x_112_, v_range_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_115_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__16, &l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16);
v___x_116_ = lean_int_add(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__17, &l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17);
v___x_118_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__9, &l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9);
v___x_119_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object* v_time_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__18, &l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_time_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* v_pdt_124_){
_start:
{
lean_object* v_time_125_; 
v_time_125_ = lean_ctor_get(v_pdt_124_, 1);
lean_inc_ref(v_time_125_);
return v_time_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* v_pdt_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_126_);
lean_dec_ref(v_pdt_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* v_x_128_, lean_object* v_y_129_){
_start:
{
lean_object* v___x_130_; lean_object* v_second_131_; lean_object* v_nano_132_; lean_object* v___x_133_; lean_object* v_second_134_; lean_object* v_nano_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_130_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_y_129_);
v_second_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_second_131_);
v_nano_132_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_nano_132_);
lean_dec_ref(v___x_130_);
v___x_133_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_x_128_);
v_second_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_second_134_);
v_nano_135_ = lean_ctor_get(v___x_133_, 1);
lean_inc(v_nano_135_);
lean_dec_ref(v___x_133_);
v___x_136_ = lean_int_neg(v_second_131_);
lean_dec(v_second_131_);
v___x_137_ = lean_int_neg(v_nano_132_);
lean_dec(v_nano_132_);
v___x_138_ = lean_obj_once(&l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0, &l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0);
v___x_139_ = lean_int_mul(v_second_134_, v___x_138_);
lean_dec(v_second_134_);
v___x_140_ = lean_int_add(v___x_139_, v_nano_135_);
lean_dec(v_nano_135_);
lean_dec(v___x_139_);
v___x_141_ = lean_int_mul(v___x_136_, v___x_138_);
lean_dec(v___x_136_);
v___x_142_ = lean_int_add(v___x_141_, v___x_137_);
lean_dec(v___x_137_);
lean_dec(v___x_141_);
v___x_143_ = lean_int_add(v___x_140_, v___x_142_);
lean_dec(v___x_142_);
lean_dec(v___x_140_);
v___x_144_ = l_Std_Time_Duration_ofNanoseconds(v___x_143_);
lean_dec(v___x_143_);
return v___x_144_;
}
}
lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_DateTime(builtin);
}
#ifdef __cplusplus
}
#endif
