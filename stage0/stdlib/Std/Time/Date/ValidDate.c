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
lean_object* l_Std_Time_instInhabitedValidDate___redArg(){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__18, &l_Std_Time_instInhabitedValidDate___redArg___closed__18_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__18);
return v___x_55_;
}
}
LEAN_EXPORT void l_Std_Time_instInhabitedValidDate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l_Std_Time_instInhabitedValidDate___redArg();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___redArg___boxed(lean_object* v___dummy_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Time_instInhabitedValidDate___redArg();
return v_res_58_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_Time_instInhabitedValidDate___redArg();
return v___x_59_;
}
}
lean_object* l_Std_Time_instInhabitedValidDate(uint8_t v_l_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
return v___x_61_;
}
}
LEAN_EXPORT void l_Std_Time_instInhabitedValidDate_0interp(lean_interpreter_value* stack)
{
uint8_t v_l_60_ = stack[0].m_num;
lean_object* v_res_62_;
v_res_62_ = l_Std_Time_instInhabitedValidDate(v_l_60_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___boxed(lean_object* v_l_63_){
_start:
{
uint8_t v_l_boxed_64_; lean_object* v_res_65_; 
v_l_boxed_64_ = lean_unbox(v_l_63_);
v_res_65_ = l_Std_Time_instInhabitedValidDate(v_l_boxed_64_);
return v_res_65_;
}
}
uint8_t l_Std_Time_instDecidableEqValidDate___redArg(lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_68_ = lean_alloc_closure((void*)(l_Std_Time_Month_instDecidableEqOrdinal___boxed), 2, 0);
v___x_69_ = lean_alloc_closure((void*)(l_Std_Time_Day_instDecidableEqOrdinal___boxed), 2, 0);
v___x_70_ = l_instDecidableEqProd___redArg(v___x_68_, v___x_69_, v_a_66_, v_b_67_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqValidDate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_66_ = stack[0].m_obj;
lean_object* v_b_67_ = stack[1].m_obj;
uint8_t v_res_71_;
v_res_71_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_66_, v_b_67_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___redArg___boxed(lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_72_, v_b_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
uint8_t l_Std_Time_instDecidableEqValidDate(uint8_t v_leap_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_77_, v_b_78_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqValidDate_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_76_ = stack[0].m_num;
lean_object* v_a_77_ = stack[1].m_obj;
lean_object* v_b_78_ = stack[2].m_obj;
uint8_t v_res_80_;
v_res_80_ = l_Std_Time_instDecidableEqValidDate(v_leap_76_, v_a_77_, v_b_78_);
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___boxed(lean_object* v_leap_81_, lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
uint8_t v_leap_boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_leap_boxed_84_ = lean_unbox(v_leap_81_);
v_res_85_ = l_Std_Time_instDecidableEqValidDate(v_leap_boxed_84_, v_a_82_, v_b_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
uint8_t l_Std_Time_instOrdValidDate___redArg___lam__0(lean_object* v_a_87_, lean_object* v_b_88_){
_start:
{
lean_object* v_fst_89_; lean_object* v_snd_90_; lean_object* v_fst_91_; lean_object* v_snd_92_; uint8_t v___x_93_; 
v_fst_89_ = lean_ctor_get(v_a_87_, 0);
v_snd_90_ = lean_ctor_get(v_a_87_, 1);
v_fst_91_ = lean_ctor_get(v_b_88_, 0);
v_snd_92_ = lean_ctor_get(v_b_88_, 1);
v___x_93_ = lean_int_dec_lt(v_fst_89_, v_fst_91_);
if (v___x_93_ == 0)
{
uint8_t v___x_94_; 
v___x_94_ = lean_int_dec_eq(v_fst_89_, v_fst_91_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 2;
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = lean_int_dec_lt(v_snd_90_, v_snd_92_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; 
v___x_97_ = lean_int_dec_eq(v_snd_90_, v_snd_92_);
if (v___x_97_ == 0)
{
uint8_t v___x_98_; 
v___x_98_ = 2;
return v___x_98_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = 1;
return v___x_99_;
}
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
}
LEAN_EXPORT void l_Std_Time_instOrdValidDate___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_87_ = stack[0].m_obj;
lean_object* v_b_88_ = stack[1].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Std_Time_instOrdValidDate___redArg___lam__0(v_a_87_, v_b_88_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg___lam__0___boxed(lean_object* v_a_103_, lean_object* v_b_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Std_Time_instOrdValidDate___redArg___lam__0(v_a_103_, v_b_104_);
lean_dec_ref(v_b_104_);
lean_dec_ref(v_a_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
lean_object* l_Std_Time_instOrdValidDate___redArg(){
_start:
{
lean_object* v___f_109_; 
v___f_109_ = ((lean_object*)(l_Std_Time_instOrdValidDate___redArg___closed__0));
return v___f_109_;
}
}
LEAN_EXPORT void l_Std_Time_instOrdValidDate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_110_;
v_res_110_ = l_Std_Time_instOrdValidDate___redArg();
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___redArg___boxed(lean_object* v___dummy_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Time_instOrdValidDate___redArg();
return v_res_112_;
}
}
lean_object* l_Std_Time_instOrdValidDate(uint8_t v_leap_113_){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = ((lean_object*)(l_Std_Time_instOrdValidDate___redArg___closed__0));
return v___f_114_;
}
}
LEAN_EXPORT void l_Std_Time_instOrdValidDate_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_113_ = stack[0].m_num;
lean_object* v_res_115_;
v_res_115_ = l_Std_Time_instOrdValidDate(v_leap_113_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___boxed(lean_object* v_leap_116_){
_start:
{
uint8_t v_leap_boxed_117_; lean_object* v_res_118_; 
v_leap_boxed_117_ = lean_unbox(v_leap_116_);
v_res_118_ = l_Std_Time_instOrdValidDate(v_leap_boxed_117_);
return v_res_118_;
}
}
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t v_leap_119_, lean_object* v_ordinal_120_){
_start:
{
lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v_days_123_; lean_object* v_bounded_124_; 
v_fst_121_ = lean_ctor_get(v_ordinal_120_, 0);
v_snd_122_ = lean_ctor_get(v_ordinal_120_, 1);
v_days_123_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_119_, v_fst_121_);
v_bounded_124_ = lean_int_add(v_days_123_, v_snd_122_);
lean_dec(v_days_123_);
return v_bounded_124_;
}
}
LEAN_EXPORT void l_Std_Time_ValidDate_dayOfYear_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_119_ = stack[0].m_num;
lean_object* v_ordinal_120_ = stack[1].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_Std_Time_ValidDate_dayOfYear(v_leap_119_, v_ordinal_120_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear___boxed(lean_object* v_leap_126_, lean_object* v_ordinal_127_){
_start:
{
uint8_t v_leap_boxed_128_; lean_object* v_res_129_; 
v_leap_boxed_128_ = lean_unbox(v_leap_126_);
v_res_129_ = l_Std_Time_ValidDate_dayOfYear(v_leap_boxed_128_, v_ordinal_127_);
lean_dec_ref(v_ordinal_127_);
return v_res_129_;
}
}
lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(uint8_t v_leap_130_, lean_object* v_ordinal_131_, lean_object* v_idx_132_, lean_object* v_acc_133_){
_start:
{
lean_object* v_monthDays_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_monthDays_134_ = l_Std_Time_Month_Ordinal_days(v_leap_130_, v_idx_132_);
v___x_135_ = lean_int_add(v_acc_133_, v_monthDays_134_);
lean_dec(v_monthDays_134_);
v___x_136_ = lean_int_dec_le(v_ordinal_131_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v_idx_u2082_138_; 
lean_dec(v_acc_133_);
v___x_137_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v_idx_u2082_138_ = lean_int_add(v_idx_132_, v___x_137_);
lean_dec(v_idx_132_);
v_idx_132_ = v_idx_u2082_138_;
v_acc_133_ = v___x_135_;
goto _start;
}
else
{
lean_object* v___x_140_; lean_object* v_days_u2081_141_; lean_object* v___x_142_; 
lean_dec(v___x_135_);
v___x_140_ = lean_int_neg(v_acc_133_);
lean_dec(v_acc_133_);
v_days_u2081_141_ = lean_int_add(v_ordinal_131_, v___x_140_);
lean_dec(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_idx_132_);
lean_ctor_set(v___x_142_, 1, v_days_u2081_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_130_ = stack[0].m_num;
lean_object* v_ordinal_131_ = stack[1].m_obj;
lean_object* v_idx_132_ = stack[2].m_obj;
lean_object* v_acc_133_ = stack[3].m_obj;
lean_object* v_res_143_;
v_res_143_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_130_, v_ordinal_131_, v_idx_132_, v_acc_133_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg___boxed(lean_object* v_leap_144_, lean_object* v_ordinal_145_, lean_object* v_idx_146_, lean_object* v_acc_147_){
_start:
{
uint8_t v_leap_boxed_148_; lean_object* v_res_149_; 
v_leap_boxed_148_ = lean_unbox(v_leap_144_);
v_res_149_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_boxed_148_, v_ordinal_145_, v_idx_146_, v_acc_147_);
lean_dec(v_ordinal_145_);
return v_res_149_;
}
}
lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(uint8_t v_leap_150_, lean_object* v_ordinal_151_, lean_object* v_idx_152_, lean_object* v_acc_153_, lean_object* v_h_154_, lean_object* v_p_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_150_, v_ordinal_151_, v_idx_152_, v_acc_153_);
return v___x_156_;
}
}
LEAN_EXPORT void l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_150_ = stack[0].m_num;
lean_object* v_ordinal_151_ = stack[1].m_obj;
lean_object* v_idx_152_ = stack[2].m_obj;
lean_object* v_acc_153_ = stack[3].m_obj;
lean_object* v_res_157_;
v_res_157_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(v_leap_150_, v_ordinal_151_, v_idx_152_, v_acc_153_, lean_box(0), lean_box(0));
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___boxed(lean_object* v_leap_158_, lean_object* v_ordinal_159_, lean_object* v_idx_160_, lean_object* v_acc_161_, lean_object* v_h_162_, lean_object* v_p_163_){
_start:
{
uint8_t v_leap_boxed_164_; lean_object* v_res_165_; 
v_leap_boxed_164_ = lean_unbox(v_leap_158_);
v_res_165_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(v_leap_boxed_164_, v_ordinal_159_, v_idx_160_, v_acc_161_, v_h_162_, v_p_163_);
lean_dec(v_ordinal_159_);
return v_res_165_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__0(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(11u);
v___x_167_ = lean_nat_to_int(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__0, &l_Std_Time_ValidDate_ofOrdinal___closed__0_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__0);
v___x_169_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_170_ = lean_int_add(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__2(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_172_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__1, &l_Std_Time_ValidDate_ofOrdinal___closed__1_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__1);
v___x_173_ = lean_int_sub(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__3(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_range_176_; 
v___x_174_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_175_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__2, &l_Std_Time_ValidDate_ofOrdinal___closed__2_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__2);
v_range_176_ = lean_int_add(v___x_175_, v___x_174_);
return v_range_176_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__4(void){
_start:
{
lean_object* v_range_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_range_177_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_178_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__5, &l_Std_Time_instInhabitedValidDate___redArg___closed__5_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__5);
v___x_179_ = lean_int_emod(v___x_178_, v_range_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__5(void){
_start:
{
lean_object* v_range_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_range_180_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_181_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__4, &l_Std_Time_ValidDate_ofOrdinal___closed__4_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__4);
v___x_182_ = lean_int_add(v___x_181_, v_range_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__6(void){
_start:
{
lean_object* v_range_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_range_183_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_184_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__5, &l_Std_Time_ValidDate_ofOrdinal___closed__5_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__5);
v___x_185_ = lean_int_emod(v___x_184_, v_range_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__7(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___redArg___closed__0, &l_Std_Time_instInhabitedValidDate___redArg___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___redArg___closed__0);
v___x_187_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__6, &l_Std_Time_ValidDate_ofOrdinal___closed__6_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__6);
v___x_188_ = lean_int_add(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__8(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_nat_to_int(v___x_189_);
return v___x_190_;
}
}
lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t v_leap_191_, lean_object* v_ordinal_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__7, &l_Std_Time_ValidDate_ofOrdinal___closed__7_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__7);
v___x_194_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__8, &l_Std_Time_ValidDate_ofOrdinal___closed__8_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__8);
v___x_195_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_191_, v_ordinal_192_, v___x_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT void l_Std_Time_ValidDate_ofOrdinal_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_191_ = stack[0].m_num;
lean_object* v_ordinal_192_ = stack[1].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_Std_Time_ValidDate_ofOrdinal(v_leap_191_, v_ordinal_192_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal___boxed(lean_object* v_leap_197_, lean_object* v_ordinal_198_){
_start:
{
uint8_t v_leap_boxed_199_; lean_object* v_res_200_; 
v_leap_boxed_199_ = lean_unbox(v_leap_197_);
v_res_200_ = l_Std_Time_ValidDate_ofOrdinal(v_leap_boxed_199_, v_ordinal_198_);
lean_dec(v_ordinal_198_);
return v_res_200_;
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
