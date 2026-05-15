// Lean compiler output
// Module: Std.Time.DateTime
// Imports: public import Std.Time.Zoned.Offset public import Std.Time.DateTime.WallTime public import Std.Time.DateTime.Timestamp public import Std.Time.DateTime.PlainDateTime import all Std.Time.Date.Unit.Month
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
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
extern lean_object* l_Std_Time_PlainTime_midnight;
static lean_once_cell_t l_Std_Time_Timestamp_toWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_toWallTime___closed__0;
static lean_once_cell_t l_Std_Time_Timestamp_toWallTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_toWallTime___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_ofWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_ofWallTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_toWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_toWallTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_instHSubDuration___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHSubDuration = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object*);
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
static lean_object* _init_l_Std_Time_Timestamp_toWallTime___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toWallTime___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1000000000u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime(lean_object* v_ts_5_, lean_object* v_offset_6_){
_start:
{
lean_object* v_second_7_; lean_object* v_nano_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_second_7_ = lean_ctor_get(v_ts_5_, 0);
v_nano_8_ = lean_ctor_get(v_ts_5_, 1);
v___x_9_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_10_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__1, &l_Std_Time_Timestamp_toWallTime___closed__1_once, _init_l_Std_Time_Timestamp_toWallTime___closed__1);
v___x_11_ = lean_int_mul(v_second_7_, v___x_10_);
v___x_12_ = lean_int_add(v___x_11_, v_nano_8_);
lean_dec(v___x_11_);
v___x_13_ = lean_int_mul(v_offset_6_, v___x_10_);
v___x_14_ = lean_int_add(v___x_13_, v___x_9_);
lean_dec(v___x_13_);
v___x_15_ = lean_int_add(v___x_12_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_12_);
v___x_16_ = l_Std_Time_Duration_ofNanoseconds(v___x_15_);
lean_dec(v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime___boxed(lean_object* v_ts_17_, lean_object* v_offset_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Time_Timestamp_toWallTime(v_ts_17_, v_offset_18_);
lean_dec(v_offset_18_);
lean_dec_ref(v_ts_17_);
return v_res_19_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_21_ = lean_int_neg(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime(lean_object* v_wt_22_, lean_object* v_offset_23_){
_start:
{
lean_object* v_second_24_; lean_object* v_nano_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_second_24_ = lean_ctor_get(v_wt_22_, 0);
v_nano_25_ = lean_ctor_get(v_wt_22_, 1);
v___x_26_ = lean_int_neg(v_offset_23_);
v___x_27_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_28_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__1, &l_Std_Time_Timestamp_toWallTime___closed__1_once, _init_l_Std_Time_Timestamp_toWallTime___closed__1);
v___x_29_ = lean_int_mul(v_second_24_, v___x_28_);
v___x_30_ = lean_int_add(v___x_29_, v_nano_25_);
lean_dec(v___x_29_);
v___x_31_ = lean_int_mul(v___x_26_, v___x_28_);
lean_dec(v___x_26_);
v___x_32_ = lean_int_add(v___x_31_, v___x_27_);
lean_dec(v___x_31_);
v___x_33_ = lean_int_add(v___x_30_, v___x_32_);
lean_dec(v___x_32_);
lean_dec(v___x_30_);
v___x_34_ = l_Std_Time_Duration_ofNanoseconds(v___x_33_);
lean_dec(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime___boxed(lean_object* v_wt_35_, lean_object* v_offset_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Time_Timestamp_ofWallTime(v_wt_35_, v_offset_36_);
lean_dec(v_offset_36_);
lean_dec_ref(v_wt_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp(lean_object* v_wt_38_, lean_object* v_offset_39_){
_start:
{
lean_object* v_second_40_; lean_object* v_nano_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_second_40_ = lean_ctor_get(v_wt_38_, 0);
v_nano_41_ = lean_ctor_get(v_wt_38_, 1);
v___x_42_ = lean_int_neg(v_offset_39_);
v___x_43_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_44_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__1, &l_Std_Time_Timestamp_toWallTime___closed__1_once, _init_l_Std_Time_Timestamp_toWallTime___closed__1);
v___x_45_ = lean_int_mul(v_second_40_, v___x_44_);
v___x_46_ = lean_int_add(v___x_45_, v_nano_41_);
lean_dec(v___x_45_);
v___x_47_ = lean_int_mul(v___x_42_, v___x_44_);
lean_dec(v___x_42_);
v___x_48_ = lean_int_add(v___x_47_, v___x_43_);
lean_dec(v___x_47_);
v___x_49_ = lean_int_add(v___x_46_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v___x_46_);
v___x_50_ = l_Std_Time_Duration_ofNanoseconds(v___x_49_);
lean_dec(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp___boxed(lean_object* v_wt_51_, lean_object* v_offset_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_Time_WallTime_toTimestamp(v_wt_51_, v_offset_52_);
lean_dec(v_offset_52_);
lean_dec_ref(v_wt_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp(lean_object* v_ts_54_, lean_object* v_offset_55_){
_start:
{
lean_object* v_second_56_; lean_object* v_nano_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_second_56_ = lean_ctor_get(v_ts_54_, 0);
v_nano_57_ = lean_ctor_get(v_ts_54_, 1);
v___x_58_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_59_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__1, &l_Std_Time_Timestamp_toWallTime___closed__1_once, _init_l_Std_Time_Timestamp_toWallTime___closed__1);
v___x_60_ = lean_int_mul(v_second_56_, v___x_59_);
v___x_61_ = lean_int_add(v___x_60_, v_nano_57_);
lean_dec(v___x_60_);
v___x_62_ = lean_int_mul(v_offset_55_, v___x_59_);
v___x_63_ = lean_int_add(v___x_62_, v___x_58_);
lean_dec(v___x_62_);
v___x_64_ = lean_int_add(v___x_61_, v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_61_);
v___x_65_ = l_Std_Time_Duration_ofNanoseconds(v___x_64_);
lean_dec(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp___boxed(lean_object* v_ts_66_, lean_object* v_offset_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Time_WallTime_ofTimestamp(v_ts_66_, v_offset_67_);
lean_dec(v_offset_67_);
lean_dec_ref(v_ts_66_);
return v_res_68_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toWallTime___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(86400u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object* v_pd_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_72_ = l_Std_Time_PlainDate_toEpochDay(v_pd_71_);
v___x_73_ = lean_obj_once(&l_Std_Time_PlainDate_toWallTime___closed__0, &l_Std_Time_PlainDate_toWallTime___closed__0_once, _init_l_Std_Time_PlainDate_toWallTime___closed__0);
v___x_74_ = lean_int_mul(v___x_72_, v___x_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object* v_wt_77_){
_start:
{
lean_object* v_second_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_second_78_ = lean_ctor_get(v_wt_77_, 0);
v___x_79_ = lean_obj_once(&l_Std_Time_PlainDate_toWallTime___closed__0, &l_Std_Time_PlainDate_toWallTime___closed__0_once, _init_l_Std_Time_PlainDate_toWallTime___closed__0);
v___x_80_ = lean_int_div(v_second_78_, v___x_79_);
v___x_81_ = l_Std_Time_PlainDate_ofEpochDay(v___x_80_);
lean_dec(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime___boxed(lean_object* v_wt_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Time_PlainDate_ofWallTime(v_wt_82_);
lean_dec_ref(v_wt_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* v_x_84_, lean_object* v_y_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_86_ = l_Std_Time_PlainDate_toEpochDay(v_x_84_);
v___x_87_ = lean_obj_once(&l_Std_Time_PlainDate_toWallTime___closed__0, &l_Std_Time_PlainDate_toWallTime___closed__0_once, _init_l_Std_Time_PlainDate_toWallTime___closed__0);
v___x_88_ = lean_int_mul(v___x_86_, v___x_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_90_ = l_Std_Time_PlainDate_toEpochDay(v_y_85_);
v___x_91_ = lean_int_mul(v___x_90_, v___x_87_);
lean_dec(v___x_90_);
v___x_92_ = lean_int_neg(v___x_91_);
lean_dec(v___x_91_);
v___x_93_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_94_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__1, &l_Std_Time_Timestamp_toWallTime___closed__1_once, _init_l_Std_Time_Timestamp_toWallTime___closed__1);
v___x_95_ = lean_int_mul(v___x_88_, v___x_94_);
lean_dec(v___x_88_);
v___x_96_ = lean_int_add(v___x_95_, v___x_89_);
lean_dec(v___x_95_);
v___x_97_ = lean_int_mul(v___x_92_, v___x_94_);
lean_dec(v___x_92_);
v___x_98_ = lean_int_add(v___x_97_, v___x_93_);
lean_dec(v___x_97_);
v___x_99_ = lean_int_add(v___x_96_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v___x_96_);
v___x_100_ = l_Std_Time_Duration_ofNanoseconds(v___x_99_);
lean_dec(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object* v_pt_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_103_);
v___x_105_ = l_Std_Time_Duration_ofNanoseconds(v___x_104_);
lean_dec(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object* v_pt_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Time_PlainTime_toWallTime(v_pt_106_);
lean_dec_ref(v_pt_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object* v_wt_108_){
_start:
{
lean_object* v_second_109_; lean_object* v_nano_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v_nanos_113_; lean_object* v___x_114_; 
v_second_109_ = lean_ctor_get(v_wt_108_, 0);
v_nano_110_ = lean_ctor_get(v_wt_108_, 1);
v___x_111_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__1, &l_Std_Time_Timestamp_toWallTime___closed__1_once, _init_l_Std_Time_Timestamp_toWallTime___closed__1);
v___x_112_ = lean_int_mul(v_second_109_, v___x_111_);
v_nanos_113_ = lean_int_add(v___x_112_, v_nano_110_);
lean_dec(v___x_112_);
v___x_114_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_113_);
lean_dec(v_nanos_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object* v_wt_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Time_PlainTime_ofWallTime(v_wt_115_);
lean_dec_ref(v_wt_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* v_date_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = l_Std_Time_PlainTime_midnight;
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_date_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* v_pdt_120_){
_start:
{
lean_object* v_date_121_; 
v_date_121_ = lean_ctor_get(v_pdt_120_, 0);
lean_inc_ref(v_date_121_);
return v_date_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* v_pdt_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_122_);
lean_dec_ref(v_pdt_122_);
return v_res_123_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(11u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__1, &l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1);
v___x_129_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_130_ = lean_int_add(v___x_129_, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_132_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__2, &l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2);
v___x_133_ = lean_int_sub(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_range_136_; 
v___x_134_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_135_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__3, &l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3);
v_range_136_ = lean_int_add(v___x_135_, v___x_134_);
return v_range_136_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_138_ = lean_int_sub(v___x_137_, v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6(void){
_start:
{
lean_object* v_range_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_range_139_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
v___x_140_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__5, &l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5);
v___x_141_ = lean_int_emod(v___x_140_, v_range_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7(void){
_start:
{
lean_object* v_range_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_range_142_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
v___x_143_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__6, &l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6);
v___x_144_ = lean_int_add(v___x_143_, v_range_142_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8(void){
_start:
{
lean_object* v_range_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_range_145_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
v___x_146_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__7, &l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7);
v___x_147_ = lean_int_emod(v___x_146_, v_range_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_149_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__8, &l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8);
v___x_150_ = lean_int_add(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(30u);
v___x_152_ = lean_nat_to_int(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__10, &l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10);
v___x_154_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_155_ = lean_int_add(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_157_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__11, &l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11);
v___x_158_ = lean_int_sub(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_range_161_; 
v___x_159_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_160_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__12, &l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12);
v_range_161_ = lean_int_add(v___x_160_, v___x_159_);
return v_range_161_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14(void){
_start:
{
lean_object* v_range_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_range_162_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
v___x_163_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__5, &l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5);
v___x_164_ = lean_int_emod(v___x_163_, v_range_162_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15(void){
_start:
{
lean_object* v_range_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_range_165_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
v___x_166_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__14, &l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14);
v___x_167_ = lean_int_add(v___x_166_, v_range_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16(void){
_start:
{
lean_object* v_range_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_range_168_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
v___x_169_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__15, &l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15);
v___x_170_ = lean_int_emod(v___x_169_, v_range_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_172_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__16, &l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16);
v___x_173_ = lean_int_add(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__17, &l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17);
v___x_175_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__9, &l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9);
v___x_176_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_174_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object* v_time_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__18, &l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_time_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* v_pdt_181_){
_start:
{
lean_object* v_time_182_; 
v_time_182_ = lean_ctor_get(v_pdt_181_, 1);
lean_inc_ref(v_time_182_);
return v_time_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* v_pdt_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_183_);
lean_dec_ref(v_pdt_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* v_x_185_, lean_object* v_y_186_){
_start:
{
lean_object* v___x_187_; lean_object* v_second_188_; lean_object* v_nano_189_; lean_object* v___x_190_; lean_object* v_second_191_; lean_object* v_nano_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_187_ = l_Std_Time_PlainDateTime_toWallTime(v_y_186_);
v_second_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_second_188_);
v_nano_189_ = lean_ctor_get(v___x_187_, 1);
lean_inc(v_nano_189_);
lean_dec_ref(v___x_187_);
v___x_190_ = l_Std_Time_PlainDateTime_toWallTime(v_x_185_);
v_second_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_second_191_);
v_nano_192_ = lean_ctor_get(v___x_190_, 1);
lean_inc(v_nano_192_);
lean_dec_ref(v___x_190_);
v___x_193_ = lean_int_neg(v_second_188_);
lean_dec(v_second_188_);
v___x_194_ = lean_int_neg(v_nano_189_);
lean_dec(v_nano_189_);
v___x_195_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__1, &l_Std_Time_Timestamp_toWallTime___closed__1_once, _init_l_Std_Time_Timestamp_toWallTime___closed__1);
v___x_196_ = lean_int_mul(v_second_191_, v___x_195_);
lean_dec(v_second_191_);
v___x_197_ = lean_int_add(v___x_196_, v_nano_192_);
lean_dec(v_nano_192_);
lean_dec(v___x_196_);
v___x_198_ = lean_int_mul(v___x_193_, v___x_195_);
lean_dec(v___x_193_);
v___x_199_ = lean_int_add(v___x_198_, v___x_194_);
lean_dec(v___x_194_);
lean_dec(v___x_198_);
v___x_200_ = lean_int_add(v___x_197_, v___x_199_);
lean_dec(v___x_199_);
lean_dec(v___x_197_);
v___x_201_ = l_Std_Time_Duration_ofNanoseconds(v___x_200_);
lean_dec(v___x_200_);
return v___x_201_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_Offset(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
lean_object* initialize_Std_Time_Zoned_Offset(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
