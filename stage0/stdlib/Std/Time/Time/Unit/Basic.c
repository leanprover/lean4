// Lean compiler output
// Module: Std.Time.Time.Unit.Basic
// Imports: public import Std.Time.Time.Unit.Hour public import Std.Time.Time.Unit.Millisecond
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
lean_object* lean_int_div(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMilliseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_Offset_toSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofSeconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_Offset_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_Offset_toHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_Offset_toHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofNanoseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_Offset_toSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofSeconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_Offset_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_Offset_toHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_Offset_toHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMilliseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Second_Offset_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_Offset_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Second_Offset_toHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_Offset_toHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMinutes___boxed(lean_object*);
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1000000u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMilliseconds(lean_object* v_offset_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0, &l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0);
v___x_5_ = lean_int_div(v_offset_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMilliseconds___boxed(lean_object* v_offset_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Time_Nanosecond_Offset_toMilliseconds(v_offset_6_);
lean_dec(v_offset_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMilliseconds(lean_object* v_offset_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0, &l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0);
v___x_10_ = lean_int_mul(v_offset_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMilliseconds___boxed(lean_object* v_offset_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Time_Nanosecond_Offset_ofMilliseconds(v_offset_11_);
lean_dec(v_offset_11_);
return v_res_12_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(1000000000u);
v___x_14_ = lean_nat_to_int(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toSeconds(lean_object* v_offset_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toSeconds___closed__0, &l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0);
v___x_17_ = lean_int_div(v_offset_15_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toSeconds___boxed(lean_object* v_offset_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Time_Nanosecond_Offset_toSeconds(v_offset_18_);
lean_dec(v_offset_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofSeconds(lean_object* v_offset_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toSeconds___closed__0, &l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0);
v___x_22_ = lean_int_mul(v_offset_20_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofSeconds___boxed(lean_object* v_offset_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Time_Nanosecond_Offset_ofSeconds(v_offset_23_);
lean_dec(v_offset_23_);
return v_res_24_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_cstr_to_nat("60000000000");
v___x_26_ = lean_nat_to_int(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMinutes(lean_object* v_offset_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMinutes___closed__0, &l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0);
v___x_29_ = lean_int_div(v_offset_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toMinutes___boxed(lean_object* v_offset_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Time_Nanosecond_Offset_toMinutes(v_offset_30_);
lean_dec(v_offset_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMinutes(lean_object* v_offset_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMinutes___closed__0, &l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0);
v___x_34_ = lean_int_mul(v_offset_32_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofMinutes___boxed(lean_object* v_offset_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Time_Nanosecond_Offset_ofMinutes(v_offset_35_);
lean_dec(v_offset_35_);
return v_res_36_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_cstr_to_nat("3600000000000");
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toHours(lean_object* v_offset_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toHours___closed__0, &l_Std_Time_Nanosecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0);
v___x_41_ = lean_int_div(v_offset_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toHours___boxed(lean_object* v_offset_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Time_Nanosecond_Offset_toHours(v_offset_42_);
lean_dec(v_offset_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofHours(lean_object* v_offset_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toHours___closed__0, &l_Std_Time_Nanosecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0);
v___x_46_ = lean_int_mul(v_offset_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofHours___boxed(lean_object* v_offset_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Time_Nanosecond_Offset_ofHours(v_offset_47_);
lean_dec(v_offset_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toNanoseconds(lean_object* v_offset_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0, &l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0);
v___x_51_ = lean_int_mul(v_offset_49_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toNanoseconds___boxed(lean_object* v_offset_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_Time_Millisecond_Offset_toNanoseconds(v_offset_52_);
lean_dec(v_offset_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofNanoseconds(lean_object* v_offset_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0, &l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0);
v___x_56_ = lean_int_div(v_offset_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofNanoseconds___boxed(lean_object* v_offset_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Time_Millisecond_Offset_ofNanoseconds(v_offset_57_);
lean_dec(v_offset_57_);
return v_res_58_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(1000u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toSeconds(lean_object* v_offset_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toSeconds___closed__0, &l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0);
v___x_63_ = lean_int_div(v_offset_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toSeconds___boxed(lean_object* v_offset_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Time_Millisecond_Offset_toSeconds(v_offset_64_);
lean_dec(v_offset_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofSeconds(lean_object* v_offset_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toSeconds___closed__0, &l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0);
v___x_68_ = lean_int_mul(v_offset_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofSeconds___boxed(lean_object* v_offset_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Time_Millisecond_Offset_ofSeconds(v_offset_69_);
lean_dec(v_offset_69_);
return v_res_70_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(60000u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toMinutes(lean_object* v_offset_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toMinutes___closed__0, &l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0);
v___x_75_ = lean_int_div(v_offset_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toMinutes___boxed(lean_object* v_offset_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_Time_Millisecond_Offset_toMinutes(v_offset_76_);
lean_dec(v_offset_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofMinutes(lean_object* v_offset_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toMinutes___closed__0, &l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0);
v___x_80_ = lean_int_mul(v_offset_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofMinutes___boxed(lean_object* v_offset_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_Time_Millisecond_Offset_ofMinutes(v_offset_81_);
lean_dec(v_offset_81_);
return v_res_82_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(3600000u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toHours(lean_object* v_offset_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toHours___closed__0, &l_Std_Time_Millisecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toHours___closed__0);
v___x_87_ = lean_int_div(v_offset_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toHours___boxed(lean_object* v_offset_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Time_Millisecond_Offset_toHours(v_offset_88_);
lean_dec(v_offset_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofHours(lean_object* v_offset_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toHours___closed__0, &l_Std_Time_Millisecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toHours___closed__0);
v___x_92_ = lean_int_mul(v_offset_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofHours___boxed(lean_object* v_offset_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Time_Millisecond_Offset_ofHours(v_offset_93_);
lean_dec(v_offset_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toNanoseconds(lean_object* v_offset_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toSeconds___closed__0, &l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0);
v___x_97_ = lean_int_mul(v_offset_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toNanoseconds___boxed(lean_object* v_offset_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_Time_Second_Offset_toNanoseconds(v_offset_98_);
lean_dec(v_offset_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNanoseconds(lean_object* v_offset_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toSeconds___closed__0, &l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0);
v___x_102_ = lean_int_div(v_offset_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNanoseconds___boxed(lean_object* v_offset_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_Time_Second_Offset_ofNanoseconds(v_offset_103_);
lean_dec(v_offset_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMilliseconds(lean_object* v_offset_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toSeconds___closed__0, &l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0);
v___x_107_ = lean_int_mul(v_offset_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMilliseconds___boxed(lean_object* v_offset_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Time_Second_Offset_toMilliseconds(v_offset_108_);
lean_dec(v_offset_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMilliseconds(lean_object* v_offset_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toSeconds___closed__0, &l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0);
v___x_112_ = lean_int_div(v_offset_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMilliseconds___boxed(lean_object* v_offset_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_Time_Second_Offset_ofMilliseconds(v_offset_113_);
lean_dec(v_offset_113_);
return v_res_114_;
}
}
static lean_object* _init_l_Std_Time_Second_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(60u);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMinutes(lean_object* v_offset_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_119_ = lean_int_div(v_offset_117_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toMinutes___boxed(lean_object* v_offset_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_Time_Second_Offset_toMinutes(v_offset_120_);
lean_dec(v_offset_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMinutes(lean_object* v_offset_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_124_ = lean_int_mul(v_offset_122_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofMinutes___boxed(lean_object* v_offset_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_Time_Second_Offset_ofMinutes(v_offset_125_);
lean_dec(v_offset_125_);
return v_res_126_;
}
}
static lean_object* _init_l_Std_Time_Second_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(3600u);
v___x_128_ = lean_nat_to_int(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toHours(lean_object* v_offset_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Std_Time_Second_Offset_toHours___closed__0, &l_Std_Time_Second_Offset_toHours___closed__0_once, _init_l_Std_Time_Second_Offset_toHours___closed__0);
v___x_131_ = lean_int_div(v_offset_129_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toHours___boxed(lean_object* v_offset_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_Time_Second_Offset_toHours(v_offset_132_);
lean_dec(v_offset_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofHours(lean_object* v_offset_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l_Std_Time_Second_Offset_toHours___closed__0, &l_Std_Time_Second_Offset_toHours___closed__0_once, _init_l_Std_Time_Second_Offset_toHours___closed__0);
v___x_136_ = lean_int_mul(v_offset_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofHours___boxed(lean_object* v_offset_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Time_Second_Offset_ofHours(v_offset_137_);
lean_dec(v_offset_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toNanoseconds(lean_object* v_offset_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMinutes___closed__0, &l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0);
v___x_141_ = lean_int_mul(v_offset_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toNanoseconds___boxed(lean_object* v_offset_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_Time_Minute_Offset_toNanoseconds(v_offset_142_);
lean_dec(v_offset_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofNanoseconds(lean_object* v_offset_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toMinutes___closed__0, &l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0);
v___x_146_ = lean_int_div(v_offset_144_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofNanoseconds___boxed(lean_object* v_offset_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_Time_Minute_Offset_ofNanoseconds(v_offset_147_);
lean_dec(v_offset_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toMilliseconds(lean_object* v_offset_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toMinutes___closed__0, &l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0);
v___x_151_ = lean_int_mul(v_offset_149_, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toMilliseconds___boxed(lean_object* v_offset_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Time_Minute_Offset_toMilliseconds(v_offset_152_);
lean_dec(v_offset_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofMilliseconds(lean_object* v_offset_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toMinutes___closed__0, &l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0);
v___x_156_ = lean_int_div(v_offset_154_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofMilliseconds___boxed(lean_object* v_offset_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_Time_Minute_Offset_ofMilliseconds(v_offset_157_);
lean_dec(v_offset_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toSeconds(lean_object* v_offset_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_161_ = lean_int_mul(v_offset_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toSeconds___boxed(lean_object* v_offset_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Time_Minute_Offset_toSeconds(v_offset_162_);
lean_dec(v_offset_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofSeconds(lean_object* v_offset_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_166_ = lean_int_div(v_offset_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofSeconds___boxed(lean_object* v_offset_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Time_Minute_Offset_ofSeconds(v_offset_167_);
lean_dec(v_offset_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toHours(lean_object* v_offset_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_171_ = lean_int_div(v_offset_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toHours___boxed(lean_object* v_offset_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_Time_Minute_Offset_toHours(v_offset_172_);
lean_dec(v_offset_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofHours(lean_object* v_offset_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_176_ = lean_int_mul(v_offset_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofHours___boxed(lean_object* v_offset_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Time_Minute_Offset_ofHours(v_offset_177_);
lean_dec(v_offset_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toNanoseconds(lean_object* v_offset_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toHours___closed__0, &l_Std_Time_Nanosecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0);
v___x_181_ = lean_int_mul(v_offset_179_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toNanoseconds___boxed(lean_object* v_offset_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_Hour_Offset_toNanoseconds(v_offset_182_);
lean_dec(v_offset_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofNanoseconds(lean_object* v_offset_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toHours___closed__0, &l_Std_Time_Nanosecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0);
v___x_186_ = lean_int_div(v_offset_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofNanoseconds___boxed(lean_object* v_offset_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_Time_Hour_Offset_ofNanoseconds(v_offset_187_);
lean_dec(v_offset_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMilliseconds(lean_object* v_offset_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toHours___closed__0, &l_Std_Time_Millisecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toHours___closed__0);
v___x_191_ = lean_int_mul(v_offset_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMilliseconds___boxed(lean_object* v_offset_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Time_Hour_Offset_toMilliseconds(v_offset_192_);
lean_dec(v_offset_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMilliseconds(lean_object* v_offset_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toHours___closed__0, &l_Std_Time_Millisecond_Offset_toHours___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toHours___closed__0);
v___x_196_ = lean_int_div(v_offset_194_, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMilliseconds___boxed(lean_object* v_offset_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_Hour_Offset_ofMilliseconds(v_offset_197_);
lean_dec(v_offset_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toSeconds(lean_object* v_offset_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l_Std_Time_Second_Offset_toHours___closed__0, &l_Std_Time_Second_Offset_toHours___closed__0_once, _init_l_Std_Time_Second_Offset_toHours___closed__0);
v___x_201_ = lean_int_mul(v_offset_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toSeconds___boxed(lean_object* v_offset_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_Time_Hour_Offset_toSeconds(v_offset_202_);
lean_dec(v_offset_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofSeconds(lean_object* v_offset_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_obj_once(&l_Std_Time_Second_Offset_toHours___closed__0, &l_Std_Time_Second_Offset_toHours___closed__0_once, _init_l_Std_Time_Second_Offset_toHours___closed__0);
v___x_206_ = lean_int_div(v_offset_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofSeconds___boxed(lean_object* v_offset_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Time_Hour_Offset_ofSeconds(v_offset_207_);
lean_dec(v_offset_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMinutes(lean_object* v_offset_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_211_ = lean_int_mul(v_offset_209_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toMinutes___boxed(lean_object* v_offset_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Time_Hour_Offset_toMinutes(v_offset_212_);
lean_dec(v_offset_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMinutes(lean_object* v_offset_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Std_Time_Second_Offset_toMinutes___closed__0, &l_Std_Time_Second_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Second_Offset_toMinutes___closed__0);
v___x_216_ = lean_int_div(v_offset_214_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofMinutes___boxed(lean_object* v_offset_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Time_Hour_Offset_ofMinutes(v_offset_217_);
lean_dec(v_offset_217_);
return v_res_218_;
}
}
lean_object* runtime_initialize_Std_Time_Time_Unit_Hour(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Time_Unit_Millisecond(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Time_Unit_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Time_Unit_Hour(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Time_Unit_Millisecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Time_Unit_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Time_Unit_Hour(uint8_t builtin);
lean_object* initialize_Std_Time_Time_Unit_Millisecond(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Time_Unit_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time_Unit_Hour(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Time_Unit_Millisecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Time_Unit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Time_Unit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Time_Unit_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
