// Lean compiler output
// Module: Std.Time.Date.ValidDate
// Imports: public import Std.Time.Date.Unit.Month import all Std.Time.Date.Unit.Month import Init.Data.Bool
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
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Day_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_cumulativeDays(uint8_t, lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__0;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__1;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__2;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__3;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__4;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__5;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__6;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__7;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__8;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__9;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__10;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__11;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__12;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__13;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__14;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__15;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__16;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__17;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___redArg___closed__18;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___redArg();
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instOrdValidDate___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instOrdValidDate___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdValidDate___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdValidDate___redArg___closed__0 = (const lean_object*)&l_Std_Time_instOrdValidDate___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg();
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__4;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__5;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__6;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__7;
static lean_once_cell_t l_Std_Time_ValidDate_ofOrdinal___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ValidDate_ofOrdinal___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(11u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__1, &l_Std_Time_instInhabitedValidDate___redArg___closed__1_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__1);
v___x_6_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_7_ = lean_int_add(v___x_6_, v___x_5_);
return v___x_7_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_9_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__2, &l_Std_Time_instInhabitedValidDate___redArg___closed__2_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__2);
v___x_10_ = lean_int_sub(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_range_13_; 
v___x_11_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_12_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__3, &l_Std_Time_instInhabitedValidDate___redArg___closed__3_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__3);
v_range_13_ = lean_int_add(v___x_12_, v___x_11_);
return v_range_13_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__5(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_15_ = lean_int_sub(v___x_14_, v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__6(void){
_start:
{
lean_object* v_range_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_range_16_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__4, &l_Std_Time_instInhabitedValidDate___redArg___closed__4_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__4);
v___x_17_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__5, &l_Std_Time_instInhabitedValidDate___redArg___closed__5_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__5);
v___x_18_ = lean_int_emod(v___x_17_, v_range_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__7(void){
_start:
{
lean_object* v_range_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_range_19_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__4, &l_Std_Time_instInhabitedValidDate___redArg___closed__4_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__4);
v___x_20_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__6, &l_Std_Time_instInhabitedValidDate___redArg___closed__6_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__6);
v___x_21_ = lean_int_add(v___x_20_, v_range_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__8(void){
_start:
{
lean_object* v_range_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_range_22_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__4, &l_Std_Time_instInhabitedValidDate___redArg___closed__4_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__4);
v___x_23_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__7, &l_Std_Time_instInhabitedValidDate___redArg___closed__7_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__7);
v___x_24_ = lean_int_emod(v___x_23_, v_range_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__9(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_26_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__8, &l_Std_Time_instInhabitedValidDate___redArg___closed__8_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__8);
v___x_27_ = lean_int_add(v___x_26_, v___x_25_);
return v___x_27_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__10(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(30u);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__11(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__10, &l_Std_Time_instInhabitedValidDate___redArg___closed__10_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__10);
v___x_31_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_32_ = lean_int_add(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__12(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_34_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__11, &l_Std_Time_instInhabitedValidDate___redArg___closed__11_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__11);
v___x_35_ = lean_int_sub(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__13(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v_range_38_; 
v___x_36_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_37_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__12, &l_Std_Time_instInhabitedValidDate___redArg___closed__12_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__12);
v_range_38_ = lean_int_add(v___x_37_, v___x_36_);
return v_range_38_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__14(void){
_start:
{
lean_object* v_range_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_range_39_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__13, &l_Std_Time_instInhabitedValidDate___redArg___closed__13_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__13);
v___x_40_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__5, &l_Std_Time_instInhabitedValidDate___redArg___closed__5_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__5);
v___x_41_ = lean_int_emod(v___x_40_, v_range_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__15(void){
_start:
{
lean_object* v_range_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_range_42_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__13, &l_Std_Time_instInhabitedValidDate___redArg___closed__13_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__13);
v___x_43_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__14, &l_Std_Time_instInhabitedValidDate___redArg___closed__14_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__14);
v___x_44_ = lean_int_add(v___x_43_, v_range_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__16(void){
_start:
{
lean_object* v_range_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_range_45_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__13, &l_Std_Time_instInhabitedValidDate___redArg___closed__13_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__13);
v___x_46_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__15, &l_Std_Time_instInhabitedValidDate___redArg___closed__15_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__15);
v___x_47_ = lean_int_emod(v___x_46_, v_range_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__17(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_49_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__16, &l_Std_Time_instInhabitedValidDate___redArg___closed__16_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__16);
v___x_50_ = lean_int_add(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___redArg___closed__18(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__17, &l_Std_Time_instInhabitedValidDate___redArg___closed__17_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__17);
v___x_52_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__9, &l_Std_Time_instInhabitedValidDate___redArg___closed__9_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__9);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___redArg(){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__18, &l_Std_Time_instInhabitedValidDate___redArg___closed__18_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__18);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___redArg___boxed(lean_object* v___dummy_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Time_instInhabitedValidDate___redArg();
return v_res_57_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__0(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Time_instInhabitedValidDate___redArg();
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate(uint8_t v_l_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___boxed(lean_object* v_l_61_){
_start:
{
uint8_t v_l_boxed_62_; lean_object* v_res_63_; 
v_l_boxed_62_ = lean_unbox(v_l_61_);
v_res_63_ = l_Std_Time_instInhabitedValidDate(v_l_boxed_62_);
return v_res_63_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate___redArg(lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_alloc_closure((void*)(l_Std_Time_Month_instDecidableEqOrdinal___boxed), 2, 0);
v___x_67_ = lean_alloc_closure((void*)(l_Std_Time_Day_instDecidableEqOrdinal___boxed), 2, 0);
v___x_68_ = l_instDecidableEqProd___redArg(v___x_66_, v___x_67_, v_a_64_, v_b_65_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___redArg___boxed(lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_69_, v_b_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate(uint8_t v_leap_73_, lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_74_, v_b_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___boxed(lean_object* v_leap_77_, lean_object* v_a_78_, lean_object* v_b_79_){
_start:
{
uint8_t v_leap_boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_leap_boxed_80_ = lean_unbox(v_leap_77_);
v_res_81_ = l_Std_Time_instDecidableEqValidDate(v_leap_boxed_80_, v_a_78_, v_b_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instOrdValidDate___redArg___lam__0(lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v_fst_87_; lean_object* v_snd_88_; uint8_t v___x_89_; 
v_fst_85_ = lean_ctor_get(v_a_83_, 0);
v_snd_86_ = lean_ctor_get(v_a_83_, 1);
v_fst_87_ = lean_ctor_get(v_b_84_, 0);
v_snd_88_ = lean_ctor_get(v_b_84_, 1);
v___x_89_ = lean_int_dec_lt(v_fst_85_, v_fst_87_);
if (v___x_89_ == 0)
{
uint8_t v___x_90_; 
v___x_90_ = lean_int_dec_eq(v_fst_85_, v_fst_87_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 2;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = lean_int_dec_lt(v_snd_86_, v_snd_88_);
if (v___x_92_ == 0)
{
uint8_t v___x_93_; 
v___x_93_ = lean_int_dec_eq(v_snd_86_, v_snd_88_);
if (v___x_93_ == 0)
{
uint8_t v___x_94_; 
v___x_94_ = 2;
return v___x_94_;
}
else
{
uint8_t v___x_95_; 
v___x_95_ = 1;
return v___x_95_;
}
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg___lam__0___boxed(lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_Time_instOrdValidDate___redArg___lam__0(v_a_98_, v_b_99_);
lean_dec_ref(v_b_99_);
lean_dec_ref(v_a_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg(){
_start:
{
lean_object* v___f_104_; 
v___f_104_ = ((lean_object*)(l_Std_Time_instOrdValidDate___redArg___closed__0));
return v___f_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg___boxed(lean_object* v___dummy_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Time_instOrdValidDate___redArg();
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate(uint8_t v_leap_107_){
_start:
{
lean_object* v___f_108_; 
v___f_108_ = ((lean_object*)(l_Std_Time_instOrdValidDate___redArg___closed__0));
return v___f_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___boxed(lean_object* v_leap_109_){
_start:
{
uint8_t v_leap_boxed_110_; lean_object* v_res_111_; 
v_leap_boxed_110_ = lean_unbox(v_leap_109_);
v_res_111_ = l_Std_Time_instOrdValidDate(v_leap_boxed_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t v_leap_112_, lean_object* v_ordinal_113_){
_start:
{
lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v_days_116_; lean_object* v_bounded_117_; 
v_fst_114_ = lean_ctor_get(v_ordinal_113_, 0);
v_snd_115_ = lean_ctor_get(v_ordinal_113_, 1);
v_days_116_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_112_, v_fst_114_);
v_bounded_117_ = lean_int_add(v_days_116_, v_snd_115_);
lean_dec(v_days_116_);
return v_bounded_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear___boxed(lean_object* v_leap_118_, lean_object* v_ordinal_119_){
_start:
{
uint8_t v_leap_boxed_120_; lean_object* v_res_121_; 
v_leap_boxed_120_ = lean_unbox(v_leap_118_);
v_res_121_ = l_Std_Time_ValidDate_dayOfYear(v_leap_boxed_120_, v_ordinal_119_);
lean_dec_ref(v_ordinal_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(uint8_t v_leap_122_, lean_object* v_ordinal_123_, lean_object* v_idx_124_, lean_object* v_acc_125_){
_start:
{
lean_object* v_monthDays_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_monthDays_126_ = l_Std_Time_Month_Ordinal_days(v_leap_122_, v_idx_124_);
v___x_127_ = lean_int_add(v_acc_125_, v_monthDays_126_);
lean_dec(v_monthDays_126_);
v___x_128_ = lean_int_dec_le(v_ordinal_123_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v_idx_u2082_130_; 
lean_dec(v_acc_125_);
v___x_129_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v_idx_u2082_130_ = lean_int_add(v_idx_124_, v___x_129_);
lean_dec(v_idx_124_);
v_idx_124_ = v_idx_u2082_130_;
v_acc_125_ = v___x_127_;
goto _start;
}
else
{
lean_object* v___x_132_; lean_object* v_days_u2081_133_; lean_object* v___x_134_; 
lean_dec(v___x_127_);
v___x_132_ = lean_int_neg(v_acc_125_);
lean_dec(v_acc_125_);
v_days_u2081_133_ = lean_int_add(v_ordinal_123_, v___x_132_);
lean_dec(v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_idx_124_);
lean_ctor_set(v___x_134_, 1, v_days_u2081_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg___boxed(lean_object* v_leap_135_, lean_object* v_ordinal_136_, lean_object* v_idx_137_, lean_object* v_acc_138_){
_start:
{
uint8_t v_leap_boxed_139_; lean_object* v_res_140_; 
v_leap_boxed_139_ = lean_unbox(v_leap_135_);
v_res_140_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_boxed_139_, v_ordinal_136_, v_idx_137_, v_acc_138_);
lean_dec(v_ordinal_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(uint8_t v_leap_141_, lean_object* v_ordinal_142_, lean_object* v_idx_143_, lean_object* v_acc_144_, lean_object* v_h_145_, lean_object* v_p_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_141_, v_ordinal_142_, v_idx_143_, v_acc_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___boxed(lean_object* v_leap_148_, lean_object* v_ordinal_149_, lean_object* v_idx_150_, lean_object* v_acc_151_, lean_object* v_h_152_, lean_object* v_p_153_){
_start:
{
uint8_t v_leap_boxed_154_; lean_object* v_res_155_; 
v_leap_boxed_154_ = lean_unbox(v_leap_148_);
v_res_155_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(v_leap_boxed_154_, v_ordinal_149_, v_idx_150_, v_acc_151_, v_h_152_, v_p_153_);
lean_dec(v_ordinal_149_);
return v_res_155_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(11u);
v___x_157_ = lean_nat_to_int(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__1(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__0, &l_Std_Time_ValidDate_ofOrdinal___closed__0_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__0);
v___x_159_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_160_ = lean_int_add(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__2(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_162_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__1, &l_Std_Time_ValidDate_ofOrdinal___closed__1_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__1);
v___x_163_ = lean_int_sub(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__3(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_range_166_; 
v___x_164_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_165_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__2, &l_Std_Time_ValidDate_ofOrdinal___closed__2_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__2);
v_range_166_ = lean_int_add(v___x_165_, v___x_164_);
return v_range_166_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__4(void){
_start:
{
lean_object* v_range_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_range_167_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_168_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__5, &l_Std_Time_instInhabitedValidDate___redArg___closed__5_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__5);
v___x_169_ = lean_int_emod(v___x_168_, v_range_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__5(void){
_start:
{
lean_object* v_range_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_range_170_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_171_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__4, &l_Std_Time_ValidDate_ofOrdinal___closed__4_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__4);
v___x_172_ = lean_int_add(v___x_171_, v_range_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__6(void){
_start:
{
lean_object* v_range_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_range_173_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_174_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__5, &l_Std_Time_ValidDate_ofOrdinal___closed__5_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__5);
v___x_175_ = lean_int_emod(v___x_174_, v_range_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__7(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_177_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__6, &l_Std_Time_ValidDate_ofOrdinal___closed__6_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__6);
v___x_178_ = lean_int_add(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__8(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_nat_to_int(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t v_leap_181_, lean_object* v_ordinal_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__7, &l_Std_Time_ValidDate_ofOrdinal___closed__7_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__7);
v___x_184_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__8, &l_Std_Time_ValidDate_ofOrdinal___closed__8_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__8);
v___x_185_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_181_, v_ordinal_182_, v___x_183_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal___boxed(lean_object* v_leap_186_, lean_object* v_ordinal_187_){
_start:
{
uint8_t v_leap_boxed_188_; lean_object* v_res_189_; 
v_leap_boxed_188_ = lean_unbox(v_leap_186_);
v_res_189_ = l_Std_Time_ValidDate_ofOrdinal(v_leap_boxed_188_, v_ordinal_187_);
lean_dec(v_ordinal_187_);
return v_res_189_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_ValidDate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_ValidDate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_ValidDate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_ValidDate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_ValidDate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_ValidDate(builtin);
}
#ifdef __cplusplus
}
#endif
