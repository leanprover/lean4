// Lean compiler output
// Module: Std.Time.Zoned.TimeZone
// Imports: public import Std.Time.Zoned.Offset
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
lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
extern lean_object* l_Std_Time_TimeZone_Offset_zero;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimeZone_default_spec__1(lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedTimeZone_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedTimeZone_default___closed__0;
static const lean_string_object l_Std_Time_instInhabitedTimeZone_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_instInhabitedTimeZone_default___closed__1 = (const lean_object*)&l_Std_Time_instInhabitedTimeZone_default___closed__1_value;
static lean_once_cell_t l_Std_Time_instInhabitedTimeZone_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedTimeZone_default___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedTimeZone_default;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimeZone_default_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedTimeZone;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__12;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "abbreviation"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__14 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__14_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__15;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isDST"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__17 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__17_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__18;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__19 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__19_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__20;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__21;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__22 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__22_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__19_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__23 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__23_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprTimeZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprTimeZone_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprTimeZone___closed__0 = (const lean_object*)&l_Std_Time_instReprTimeZone___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprTimeZone = (const lean_object*)&l_Std_Time_instReprTimeZone___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_UTC___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l_Std_Time_TimeZone_UTC___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_UTC___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_UTC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_UTC___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTC;
static const lean_string_object l_Std_Time_TimeZone_GMT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Greenwich Mean Time"};
static const lean_object* l_Std_Time_TimeZone_GMT___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_GMT___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_GMT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GMT"};
static const lean_object* l_Std_Time_TimeZone_GMT___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_GMT___closed__1_value;
static lean_once_cell_t l_Std_Time_TimeZone_GMT___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_GMT___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_GMT;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimeZone_default_spec__1(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone_default___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone_default___closed__2(void){
_start:
{
uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = 0;
v___x_7_ = ((lean_object*)(l_Std_Time_instInhabitedTimeZone_default___closed__1));
v___x_8_ = lean_obj_once(&l_Std_Time_instInhabitedTimeZone_default___closed__0, &l_Std_Time_instInhabitedTimeZone_default___closed__0_once, _init_l_Std_Time_instInhabitedTimeZone_default___closed__0);
v___x_9_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
lean_ctor_set_uint8(v___x_9_, sizeof(void*)*3, v___x_6_);
return v___x_9_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone_default(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Std_Time_instInhabitedTimeZone_default___closed__2, &l_Std_Time_instInhabitedTimeZone_default___closed__2_once, _init_l_Std_Time_instInhabitedTimeZone_default___closed__2);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimeZone_default_spec__0(lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_nat_to_int(v_a_11_);
v___x_13_ = l_Rat_ofInt(v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Time_instInhabitedTimeZone_default;
return v___x_14_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(10u);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(8u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(16u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(9u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__0));
v___x_50_ = lean_string_length(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__20, &l_Std_Time_instReprTimeZone_repr___redArg___closed__20_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__20);
v___x_52_ = lean_nat_to_int(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___redArg(lean_object* v_x_57_){
_start:
{
lean_object* v_offset_58_; lean_object* v_name_59_; lean_object* v_abbreviation_60_; uint8_t v_isDST_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_offset_58_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_offset_58_);
v_name_59_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_name_59_);
v_abbreviation_60_ = lean_ctor_get(v_x_57_, 2);
lean_inc_ref(v_abbreviation_60_);
v_isDST_61_ = lean_ctor_get_uint8(v_x_57_, sizeof(void*)*3);
lean_dec_ref(v_x_57_);
v___x_62_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__5));
v___x_63_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__6));
v___x_64_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__7, &l_Std_Time_instReprTimeZone_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__7);
v___x_65_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_offset_58_);
lean_dec(v_offset_58_);
v___x_66_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = 0;
v___x_68_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_63_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__9));
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_box(1);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__11));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_62_);
v___x_77_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__12, &l_Std_Time_instReprTimeZone_repr___redArg___closed__12_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__12);
v___x_78_ = l_String_quote(v_name_59_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_77_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_67_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_76_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_70_);
v___x_84_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_72_);
v___x_85_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__14));
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_62_);
v___x_88_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__15, &l_Std_Time_instReprTimeZone_repr___redArg___closed__15_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__15);
v___x_89_ = l_String_quote(v_abbreviation_60_);
v___x_90_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_88_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*1, v___x_67_);
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_87_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_70_);
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_72_);
v___x_96_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__17));
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_62_);
v___x_99_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__18, &l_Std_Time_instReprTimeZone_repr___redArg___closed__18_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__18);
v___x_100_ = l_Bool_repr___redArg(v_isDST_61_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_67_);
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_98_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__21, &l_Std_Time_instReprTimeZone_repr___redArg___closed__21_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__21);
v___x_105_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__22));
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_103_);
v___x_107_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__23));
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_104_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_67_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr(lean_object* v_x_111_, lean_object* v_prec_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Time_instReprTimeZone_repr___redArg(v_x_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___boxed(lean_object* v_x_114_, lean_object* v_prec_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Time_instReprTimeZone_repr(v_x_114_, v_prec_115_);
lean_dec(v_prec_115_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone_decEq(lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_offset_121_; lean_object* v_name_122_; lean_object* v_abbreviation_123_; uint8_t v_isDST_124_; lean_object* v_offset_125_; lean_object* v_name_126_; lean_object* v_abbreviation_127_; uint8_t v_isDST_128_; uint8_t v___x_129_; 
v_offset_121_ = lean_ctor_get(v_x_119_, 0);
v_name_122_ = lean_ctor_get(v_x_119_, 1);
v_abbreviation_123_ = lean_ctor_get(v_x_119_, 2);
v_isDST_124_ = lean_ctor_get_uint8(v_x_119_, sizeof(void*)*3);
v_offset_125_ = lean_ctor_get(v_x_120_, 0);
v_name_126_ = lean_ctor_get(v_x_120_, 1);
v_abbreviation_127_ = lean_ctor_get(v_x_120_, 2);
v_isDST_128_ = lean_ctor_get_uint8(v_x_120_, sizeof(void*)*3);
v___x_129_ = lean_int_dec_eq(v_offset_121_, v_offset_125_);
if (v___x_129_ == 0)
{
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = lean_string_dec_eq(v_name_122_, v_name_126_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = lean_string_dec_eq(v_abbreviation_123_, v_abbreviation_127_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
if (v_isDST_124_ == 0)
{
if (v_isDST_128_ == 0)
{
return v___x_131_;
}
else
{
return v_isDST_124_;
}
}
else
{
return v_isDST_128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone_decEq___boxed(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_132_, v_x_133_);
lean_dec_ref(v_x_133_);
lean_dec_ref(v_x_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_136_, v_x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Std_Time_instDecidableEqTimeZone(v_x_139_, v_x_140_);
lean_dec_ref(v_x_140_);
lean_dec_ref(v_x_139_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC___closed__1(void){
_start:
{
uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = 0;
v___x_145_ = ((lean_object*)(l_Std_Time_TimeZone_UTC___closed__0));
v___x_146_ = l_Std_Time_TimeZone_Offset_zero;
v___x_147_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*3, v___x_144_);
return v___x_147_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Std_Time_TimeZone_UTC___closed__1, &l_Std_Time_TimeZone_UTC___closed__1_once, _init_l_Std_Time_TimeZone_UTC___closed__1);
return v___x_148_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT___closed__2(void){
_start:
{
uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = 0;
v___x_152_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__1));
v___x_153_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__0));
v___x_154_ = l_Std_Time_TimeZone_Offset_zero;
v___x_155_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_152_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*3, v___x_151_);
return v___x_155_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Std_Time_TimeZone_GMT___closed__2, &l_Std_Time_TimeZone_GMT___closed__2_once, _init_l_Std_Time_TimeZone_GMT___closed__2);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours(lean_object* v_name_157_, lean_object* v_abbreviation_158_, lean_object* v_n_159_, uint8_t v_isDST_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_159_);
v___x_162_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_name_157_);
lean_ctor_set(v___x_162_, 2, v_abbreviation_158_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*3, v_isDST_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object* v_name_163_, lean_object* v_abbreviation_164_, lean_object* v_n_165_, lean_object* v_isDST_166_){
_start:
{
uint8_t v_isDST_boxed_167_; lean_object* v_res_168_; 
v_isDST_boxed_167_ = lean_unbox(v_isDST_166_);
v_res_168_ = l_Std_Time_TimeZone_ofHours(v_name_163_, v_abbreviation_164_, v_n_165_, v_isDST_boxed_167_);
lean_dec(v_n_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object* v_name_169_, lean_object* v_abbreviation_170_, lean_object* v_n_171_, uint8_t v_isDST_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_173_, 0, v_n_171_);
lean_ctor_set(v___x_173_, 1, v_name_169_);
lean_ctor_set(v___x_173_, 2, v_abbreviation_170_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*3, v_isDST_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object* v_name_174_, lean_object* v_abbreviation_175_, lean_object* v_n_176_, lean_object* v_isDST_177_){
_start:
{
uint8_t v_isDST_boxed_178_; lean_object* v_res_179_; 
v_isDST_boxed_178_ = lean_unbox(v_isDST_177_);
v_res_179_ = l_Std_Time_TimeZone_ofSeconds(v_name_174_, v_abbreviation_175_, v_n_176_, v_isDST_boxed_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object* v_tz_180_){
_start:
{
lean_object* v_offset_181_; 
v_offset_181_ = lean_ctor_get(v_tz_180_, 0);
lean_inc(v_offset_181_);
return v_offset_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object* v_tz_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_TimeZone_toSeconds(v_tz_182_);
lean_dec_ref(v_tz_182_);
return v_res_183_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_Offset(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedTimeZone_default = _init_l_Std_Time_instInhabitedTimeZone_default();
lean_mark_persistent(l_Std_Time_instInhabitedTimeZone_default);
l_Std_Time_instInhabitedTimeZone = _init_l_Std_Time_instInhabitedTimeZone();
lean_mark_persistent(l_Std_Time_instInhabitedTimeZone);
l_Std_Time_TimeZone_UTC = _init_l_Std_Time_TimeZone_UTC();
lean_mark_persistent(l_Std_Time_TimeZone_UTC);
l_Std_Time_TimeZone_GMT = _init_l_Std_Time_TimeZone_GMT();
lean_mark_persistent(l_Std_Time_TimeZone_GMT);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_Offset(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_TimeZone(builtin);
}
#ifdef __cplusplus
}
#endif
