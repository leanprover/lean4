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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Std_Time_Month_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Day_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_cumulativeDays(uint8_t, lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__0;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__1;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__2;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__3;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__4;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__5;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__6;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__7;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__8;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__9;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__10;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__11;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__12;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__13;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__14;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__15;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__16;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__17;
static lean_once_cell_t l_Std_Time_instInhabitedValidDate___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedValidDate___closed__18;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instOrdValidDate___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instOrdValidDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdValidDate___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdValidDate___closed__0 = (const lean_object*)&l_Std_Time_instOrdValidDate___closed__0_value;
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
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(11u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__1, &l_Std_Time_instInhabitedValidDate___closed__1_once, _init_l_Std_Time_instInhabitedValidDate___closed__1);
v___x_6_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_7_ = lean_int_add(v___x_6_, v___x_5_);
return v___x_7_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_9_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__2, &l_Std_Time_instInhabitedValidDate___closed__2_once, _init_l_Std_Time_instInhabitedValidDate___closed__2);
v___x_10_ = lean_int_sub(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_range_13_; 
v___x_11_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_12_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__3, &l_Std_Time_instInhabitedValidDate___closed__3_once, _init_l_Std_Time_instInhabitedValidDate___closed__3);
v_range_13_ = lean_int_add(v___x_12_, v___x_11_);
return v_range_13_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__5(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_15_ = lean_int_sub(v___x_14_, v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__6(void){
_start:
{
lean_object* v_range_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_range_16_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__4, &l_Std_Time_instInhabitedValidDate___closed__4_once, _init_l_Std_Time_instInhabitedValidDate___closed__4);
v___x_17_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__5, &l_Std_Time_instInhabitedValidDate___closed__5_once, _init_l_Std_Time_instInhabitedValidDate___closed__5);
v___x_18_ = lean_int_emod(v___x_17_, v_range_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__7(void){
_start:
{
lean_object* v_range_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_range_19_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__4, &l_Std_Time_instInhabitedValidDate___closed__4_once, _init_l_Std_Time_instInhabitedValidDate___closed__4);
v___x_20_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__6, &l_Std_Time_instInhabitedValidDate___closed__6_once, _init_l_Std_Time_instInhabitedValidDate___closed__6);
v___x_21_ = lean_int_add(v___x_20_, v_range_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__8(void){
_start:
{
lean_object* v_range_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_range_22_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__4, &l_Std_Time_instInhabitedValidDate___closed__4_once, _init_l_Std_Time_instInhabitedValidDate___closed__4);
v___x_23_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__7, &l_Std_Time_instInhabitedValidDate___closed__7_once, _init_l_Std_Time_instInhabitedValidDate___closed__7);
v___x_24_ = lean_int_emod(v___x_23_, v_range_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__9(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_26_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__8, &l_Std_Time_instInhabitedValidDate___closed__8_once, _init_l_Std_Time_instInhabitedValidDate___closed__8);
v___x_27_ = lean_int_add(v___x_26_, v___x_25_);
return v___x_27_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__10(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(30u);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__11(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__10, &l_Std_Time_instInhabitedValidDate___closed__10_once, _init_l_Std_Time_instInhabitedValidDate___closed__10);
v___x_31_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_32_ = lean_int_add(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__12(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_34_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__11, &l_Std_Time_instInhabitedValidDate___closed__11_once, _init_l_Std_Time_instInhabitedValidDate___closed__11);
v___x_35_ = lean_int_sub(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__13(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v_range_38_; 
v___x_36_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_37_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__12, &l_Std_Time_instInhabitedValidDate___closed__12_once, _init_l_Std_Time_instInhabitedValidDate___closed__12);
v_range_38_ = lean_int_add(v___x_37_, v___x_36_);
return v_range_38_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__14(void){
_start:
{
lean_object* v_range_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_range_39_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__13, &l_Std_Time_instInhabitedValidDate___closed__13_once, _init_l_Std_Time_instInhabitedValidDate___closed__13);
v___x_40_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__5, &l_Std_Time_instInhabitedValidDate___closed__5_once, _init_l_Std_Time_instInhabitedValidDate___closed__5);
v___x_41_ = lean_int_emod(v___x_40_, v_range_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__15(void){
_start:
{
lean_object* v_range_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_range_42_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__13, &l_Std_Time_instInhabitedValidDate___closed__13_once, _init_l_Std_Time_instInhabitedValidDate___closed__13);
v___x_43_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__14, &l_Std_Time_instInhabitedValidDate___closed__14_once, _init_l_Std_Time_instInhabitedValidDate___closed__14);
v___x_44_ = lean_int_add(v___x_43_, v_range_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__16(void){
_start:
{
lean_object* v_range_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_range_45_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__13, &l_Std_Time_instInhabitedValidDate___closed__13_once, _init_l_Std_Time_instInhabitedValidDate___closed__13);
v___x_46_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__15, &l_Std_Time_instInhabitedValidDate___closed__15_once, _init_l_Std_Time_instInhabitedValidDate___closed__15);
v___x_47_ = lean_int_emod(v___x_46_, v_range_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__17(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_49_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__16, &l_Std_Time_instInhabitedValidDate___closed__16_once, _init_l_Std_Time_instInhabitedValidDate___closed__16);
v___x_50_ = lean_int_add(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedValidDate___closed__18(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__17, &l_Std_Time_instInhabitedValidDate___closed__17_once, _init_l_Std_Time_instInhabitedValidDate___closed__17);
v___x_52_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__9, &l_Std_Time_instInhabitedValidDate___closed__9_once, _init_l_Std_Time_instInhabitedValidDate___closed__9);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate(uint8_t v_l_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__18, &l_Std_Time_instInhabitedValidDate___closed__18_once, _init_l_Std_Time_instInhabitedValidDate___closed__18);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___boxed(lean_object* v_l_56_){
_start:
{
uint8_t v_l_boxed_57_; lean_object* v_res_58_; 
v_l_boxed_57_ = lean_unbox(v_l_56_);
v_res_58_ = l_Std_Time_instInhabitedValidDate(v_l_boxed_57_);
return v_res_58_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate___redArg(lean_object* v_a_59_, lean_object* v_b_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_alloc_closure((void*)(l_Std_Time_Month_instDecidableEqOrdinal___boxed), 2, 0);
v___x_62_ = lean_alloc_closure((void*)(l_Std_Time_Day_instDecidableEqOrdinal___boxed), 2, 0);
v___x_63_ = l_instDecidableEqProd___redArg(v___x_61_, v___x_62_, v_a_59_, v_b_60_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___redArg___boxed(lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_64_, v_b_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate(uint8_t v_leap_68_, lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = l_Std_Time_instDecidableEqValidDate___redArg(v_a_69_, v_b_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___boxed(lean_object* v_leap_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
uint8_t v_leap_boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_leap_boxed_75_ = lean_unbox(v_leap_72_);
v_res_76_ = l_Std_Time_instDecidableEqValidDate(v_leap_boxed_75_, v_a_73_, v_b_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instOrdValidDate___lam__0(lean_object* v_a_78_, lean_object* v_b_79_){
_start:
{
lean_object* v_fst_80_; lean_object* v_snd_81_; lean_object* v_fst_82_; lean_object* v_snd_83_; uint8_t v___x_84_; 
v_fst_80_ = lean_ctor_get(v_a_78_, 0);
v_snd_81_ = lean_ctor_get(v_a_78_, 1);
v_fst_82_ = lean_ctor_get(v_b_79_, 0);
v_snd_83_ = lean_ctor_get(v_b_79_, 1);
v___x_84_ = lean_int_dec_lt(v_fst_80_, v_fst_82_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = lean_int_dec_eq(v_fst_80_, v_fst_82_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 2;
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = lean_int_dec_lt(v_snd_81_, v_snd_83_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
v___x_88_ = lean_int_dec_eq(v_snd_81_, v_snd_83_);
if (v___x_88_ == 0)
{
uint8_t v___x_89_; 
v___x_89_ = 2;
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 1;
return v___x_90_;
}
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___lam__0___boxed(lean_object* v_a_93_, lean_object* v_b_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Std_Time_instOrdValidDate___lam__0(v_a_93_, v_b_94_);
lean_dec_ref(v_b_94_);
lean_dec_ref(v_a_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate(uint8_t v_leap_98_){
_start:
{
lean_object* v___f_99_; 
v___f_99_ = ((lean_object*)(l_Std_Time_instOrdValidDate___closed__0));
return v___f_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___boxed(lean_object* v_leap_100_){
_start:
{
uint8_t v_leap_boxed_101_; lean_object* v_res_102_; 
v_leap_boxed_101_ = lean_unbox(v_leap_100_);
v_res_102_ = l_Std_Time_instOrdValidDate(v_leap_boxed_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t v_leap_103_, lean_object* v_ordinal_104_){
_start:
{
lean_object* v_fst_105_; lean_object* v_snd_106_; lean_object* v_days_107_; lean_object* v_bounded_108_; 
v_fst_105_ = lean_ctor_get(v_ordinal_104_, 0);
v_snd_106_ = lean_ctor_get(v_ordinal_104_, 1);
v_days_107_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_103_, v_fst_105_);
v_bounded_108_ = lean_int_add(v_days_107_, v_snd_106_);
lean_dec(v_days_107_);
return v_bounded_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear___boxed(lean_object* v_leap_109_, lean_object* v_ordinal_110_){
_start:
{
uint8_t v_leap_boxed_111_; lean_object* v_res_112_; 
v_leap_boxed_111_ = lean_unbox(v_leap_109_);
v_res_112_ = l_Std_Time_ValidDate_dayOfYear(v_leap_boxed_111_, v_ordinal_110_);
lean_dec_ref(v_ordinal_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(uint8_t v_leap_113_, lean_object* v_ordinal_114_, lean_object* v_idx_115_, lean_object* v_acc_116_){
_start:
{
lean_object* v_monthDays_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_monthDays_117_ = l_Std_Time_Month_Ordinal_days(v_leap_113_, v_idx_115_);
v___x_118_ = lean_int_add(v_acc_116_, v_monthDays_117_);
lean_dec(v_monthDays_117_);
v___x_119_ = lean_int_dec_le(v_ordinal_114_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_idx_u2082_121_; 
lean_dec(v_acc_116_);
v___x_120_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v_idx_u2082_121_ = lean_int_add(v_idx_115_, v___x_120_);
lean_dec(v_idx_115_);
v_idx_115_ = v_idx_u2082_121_;
v_acc_116_ = v___x_118_;
goto _start;
}
else
{
lean_object* v___x_123_; lean_object* v_days_u2081_124_; lean_object* v___x_125_; 
lean_dec(v___x_118_);
v___x_123_ = lean_int_neg(v_acc_116_);
lean_dec(v_acc_116_);
v_days_u2081_124_ = lean_int_add(v_ordinal_114_, v___x_123_);
lean_dec(v___x_123_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_idx_115_);
lean_ctor_set(v___x_125_, 1, v_days_u2081_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg___boxed(lean_object* v_leap_126_, lean_object* v_ordinal_127_, lean_object* v_idx_128_, lean_object* v_acc_129_){
_start:
{
uint8_t v_leap_boxed_130_; lean_object* v_res_131_; 
v_leap_boxed_130_ = lean_unbox(v_leap_126_);
v_res_131_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_boxed_130_, v_ordinal_127_, v_idx_128_, v_acc_129_);
lean_dec(v_ordinal_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(uint8_t v_leap_132_, lean_object* v_ordinal_133_, lean_object* v_idx_134_, lean_object* v_acc_135_, lean_object* v_h_136_, lean_object* v_p_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_132_, v_ordinal_133_, v_idx_134_, v_acc_135_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___boxed(lean_object* v_leap_139_, lean_object* v_ordinal_140_, lean_object* v_idx_141_, lean_object* v_acc_142_, lean_object* v_h_143_, lean_object* v_p_144_){
_start:
{
uint8_t v_leap_boxed_145_; lean_object* v_res_146_; 
v_leap_boxed_145_ = lean_unbox(v_leap_139_);
v_res_146_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go(v_leap_boxed_145_, v_ordinal_140_, v_idx_141_, v_acc_142_, v_h_143_, v_p_144_);
lean_dec(v_ordinal_140_);
return v_res_146_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__0(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(11u);
v___x_148_ = lean_nat_to_int(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__1(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__0, &l_Std_Time_ValidDate_ofOrdinal___closed__0_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__0);
v___x_150_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_151_ = lean_int_add(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__2(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_153_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__1, &l_Std_Time_ValidDate_ofOrdinal___closed__1_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__1);
v___x_154_ = lean_int_sub(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__3(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_range_157_; 
v___x_155_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_156_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__2, &l_Std_Time_ValidDate_ofOrdinal___closed__2_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__2);
v_range_157_ = lean_int_add(v___x_156_, v___x_155_);
return v_range_157_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__4(void){
_start:
{
lean_object* v_range_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_range_158_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_159_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__5, &l_Std_Time_instInhabitedValidDate___closed__5_once, _init_l_Std_Time_instInhabitedValidDate___closed__5);
v___x_160_ = lean_int_emod(v___x_159_, v_range_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__5(void){
_start:
{
lean_object* v_range_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_range_161_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_162_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__4, &l_Std_Time_ValidDate_ofOrdinal___closed__4_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__4);
v___x_163_ = lean_int_add(v___x_162_, v_range_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__6(void){
_start:
{
lean_object* v_range_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_range_164_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__3, &l_Std_Time_ValidDate_ofOrdinal___closed__3_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__3);
v___x_165_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__5, &l_Std_Time_ValidDate_ofOrdinal___closed__5_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__5);
v___x_166_ = lean_int_emod(v___x_165_, v_range_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__7(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&l_Std_Time_instInhabitedValidDate___closed__0, &l_Std_Time_instInhabitedValidDate___closed__0_once, _init_l_Std_Time_instInhabitedValidDate___closed__0);
v___x_168_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__6, &l_Std_Time_ValidDate_ofOrdinal___closed__6_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__6);
v___x_169_ = lean_int_add(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_ValidDate_ofOrdinal___closed__8(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_nat_to_int(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t v_leap_172_, lean_object* v_ordinal_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__7, &l_Std_Time_ValidDate_ofOrdinal___closed__7_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__7);
v___x_175_ = lean_obj_once(&l_Std_Time_ValidDate_ofOrdinal___closed__8, &l_Std_Time_ValidDate_ofOrdinal___closed__8_once, _init_l_Std_Time_ValidDate_ofOrdinal___closed__8);
v___x_176_ = l___private_Std_Time_Date_ValidDate_0__Std_Time_ValidDate_ofOrdinal_go___redArg(v_leap_172_, v_ordinal_173_, v___x_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal___boxed(lean_object* v_leap_177_, lean_object* v_ordinal_178_){
_start:
{
uint8_t v_leap_boxed_179_; lean_object* v_res_180_; 
v_leap_boxed_179_ = lean_unbox(v_leap_177_);
v_res_180_ = l_Std_Time_ValidDate_ofOrdinal(v_leap_boxed_179_, v_ordinal_178_);
lean_dec(v_ordinal_178_);
return v_res_180_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_ValidDate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
