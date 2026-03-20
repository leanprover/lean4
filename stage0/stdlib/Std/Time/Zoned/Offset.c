// Lean compiler output
// Module: Std.Time.Zoned.Offset
// Imports: public import Std.Time.Time
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
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
extern lean_object* l_Std_Time_Second_instAddOffset;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instReprOffset_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9;
static lean_once_cell_t l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprOffset_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprOffset = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_TimeZone_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instInhabitedOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__0_value;
static const lean_closure_object l_Std_Time_TimeZone_instOrdOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instOrdOffset___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__1_value;
static const lean_closure_object l_Std_Time_TimeZone_instOrdOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__1_value),((lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__0_value)} };
static const lean_object* l_Std_Time_TimeZone_instOrdOffset___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instOrdOffset = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__2_value;
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__1(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_Offset_toIsoString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__1;
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__2_value;
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__4;
static lean_once_cell_t l_Std_Time_TimeZone_Offset_toIsoString___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__5;
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_zero;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instReprOffset_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(10u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0));
v___x_20_ = lean_string_length(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_28_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6));
v___x_29_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l_Std_Time_Internal_UnitVal_instRepr___lam__0(v_x_27_, v___x_30_);
v___x_32_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_29_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = 0;
v___x_34_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_34_, 0, v___x_32_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*1, v___x_33_);
v___x_35_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_28_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10);
v___x_37_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11));
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_35_);
v___x_39_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12));
v___x_40_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_36_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*1, v___x_33_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_x_43_);
lean_dec(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr(lean_object* v_x_45_, lean_object* v_prec_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_x_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___boxed(lean_object* v_x_48_, lean_object* v_prec_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Time_TimeZone_instReprOffset_repr(v_x_48_, v_prec_49_);
lean_dec(v_prec_49_);
lean_dec(v_x_48_);
return v_res_50_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset_decEq(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = lean_int_dec_eq(v_x_53_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset_decEq___boxed(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_Time_TimeZone_instDecidableEqOffset_decEq(v_x_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_x_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = lean_int_dec_eq(v_x_60_, v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset___boxed(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Std_Time_TimeZone_instDecidableEqOffset(v_x_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_x_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedOffset(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedOffset___closed__0, &l_Std_Time_TimeZone_instInhabitedOffset___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0(lean_object* v_x_70_){
_start:
{
lean_inc(v_x_70_);
return v_x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(lean_object* v_x_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Time_TimeZone_instOrdOffset___lam__0(v_x_71_);
lean_dec(v_x_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__1(lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Rat_ofInt(v_a_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__1(void){
_start:
{
lean_object* v_natZero_82_; lean_object* v_intZero_83_; 
v_natZero_82_ = lean_unsigned_to_nat(0u);
v_intZero_83_ = lean_nat_to_int(v_natZero_82_);
return v_intZero_83_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(3600u);
v___x_87_ = lean_nat_to_int(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__5(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(60u);
v___x_89_ = lean_nat_to_int(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object* v_offset_91_, uint8_t v_colon_92_){
_start:
{
lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_110_; uint8_t v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___y_139_; uint8_t v___y_140_; lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v___y_143_; lean_object* v___y_144_; lean_object* v_fst_147_; lean_object* v_snd_148_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__1, &l_Std_Time_TimeZone_Offset_toIsoString___closed__1_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__1);
v___x_180_ = lean_int_dec_le(v___x_179_, v_offset_91_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__2));
v___x_182_ = lean_int_neg(v_offset_91_);
lean_dec(v_offset_91_);
v_fst_147_ = v___x_181_;
v_snd_148_ = v___x_182_;
goto v___jp_146_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__6));
v_fst_147_ = v___x_183_;
v_snd_148_ = v_offset_91_;
goto v___jp_146_;
}
v___jp_93_:
{
if (v_colon_92_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_string_append(v___y_94_, v___y_95_);
lean_dec_ref(v___y_95_);
v___x_98_ = lean_string_append(v___x_97_, v___y_96_);
lean_dec_ref(v___y_96_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_string_append(v___y_94_, v___y_95_);
lean_dec_ref(v___y_95_);
v___x_100_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__0));
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
v___x_102_ = lean_string_append(v___x_101_, v___y_96_);
lean_dec_ref(v___y_96_);
return v___x_102_;
}
}
v___jp_103_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_string_append(v___y_104_, v___y_107_);
lean_dec_ref(v___y_107_);
v___y_94_ = v___y_105_;
v___y_95_ = v___y_106_;
v___y_96_ = v___x_108_;
goto v___jp_93_;
}
v___jp_109_:
{
if (v___y_111_ == 0)
{
lean_object* v_intZero_115_; uint8_t v_isNeg_116_; 
v_intZero_115_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__1, &l_Std_Time_TimeZone_Offset_toIsoString___closed__1_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__1);
v_isNeg_116_ = lean_int_dec_lt(v___y_110_, v_intZero_115_);
if (v_isNeg_116_ == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_nat_abs(v___y_110_);
lean_dec(v___y_110_);
v___x_118_ = l_Nat_reprFast(v_a_117_);
v___y_94_ = v___y_113_;
v___y_95_ = v___y_114_;
v___y_96_ = v___x_118_;
goto v___jp_93_;
}
else
{
lean_object* v_abs_119_; lean_object* v_one_120_; lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_abs_119_ = lean_nat_abs(v___y_110_);
lean_dec(v___y_110_);
v_one_120_ = lean_unsigned_to_nat(1u);
v_a_121_ = lean_nat_sub(v_abs_119_, v_one_120_);
lean_dec(v_abs_119_);
v___x_122_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__2));
v___x_123_ = lean_nat_add(v_a_121_, v___y_112_);
lean_dec(v_a_121_);
v___x_124_ = l_Nat_reprFast(v___x_123_);
v___x_125_ = lean_string_append(v___x_122_, v___x_124_);
lean_dec_ref(v___x_124_);
v___y_94_ = v___y_113_;
v___y_95_ = v___y_114_;
v___y_96_ = v___x_125_;
goto v___jp_93_;
}
}
else
{
lean_object* v___x_126_; lean_object* v_intZero_127_; uint8_t v_isNeg_128_; 
v___x_126_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__3));
v_intZero_127_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__1, &l_Std_Time_TimeZone_Offset_toIsoString___closed__1_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__1);
v_isNeg_128_ = lean_int_dec_lt(v___y_110_, v_intZero_127_);
if (v_isNeg_128_ == 0)
{
lean_object* v_a_129_; lean_object* v___x_130_; 
v_a_129_ = lean_nat_abs(v___y_110_);
lean_dec(v___y_110_);
v___x_130_ = l_Nat_reprFast(v_a_129_);
v___y_104_ = v___x_126_;
v___y_105_ = v___y_113_;
v___y_106_ = v___y_114_;
v___y_107_ = v___x_130_;
goto v___jp_103_;
}
else
{
lean_object* v_abs_131_; lean_object* v_one_132_; lean_object* v_a_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_abs_131_ = lean_nat_abs(v___y_110_);
lean_dec(v___y_110_);
v_one_132_ = lean_unsigned_to_nat(1u);
v_a_133_ = lean_nat_sub(v_abs_131_, v_one_132_);
lean_dec(v_abs_131_);
v___x_134_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__2));
v___x_135_ = lean_nat_add(v_a_133_, v___y_112_);
lean_dec(v_a_133_);
v___x_136_ = l_Nat_reprFast(v___x_135_);
v___x_137_ = lean_string_append(v___x_134_, v___x_136_);
lean_dec_ref(v___x_136_);
v___y_104_ = v___x_126_;
v___y_105_ = v___y_113_;
v___y_106_ = v___y_114_;
v___y_107_ = v___x_137_;
goto v___jp_103_;
}
}
}
v___jp_138_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_string_append(v___y_141_, v___y_144_);
lean_dec_ref(v___y_144_);
v___y_110_ = v___y_139_;
v___y_111_ = v___y_140_;
v___y_112_ = v___y_143_;
v___y_113_ = v___y_142_;
v___y_114_ = v___x_145_;
goto v___jp_109_;
}
v___jp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_hour_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_minute_154_; lean_object* v___x_155_; uint8_t v___x_156_; uint8_t v___x_157_; 
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v_hour_151_ = lean_int_div(v_snd_148_, v___x_150_);
v___x_152_ = lean_int_mod(v_snd_148_, v___x_150_);
lean_dec(v_snd_148_);
v___x_153_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__5, &l_Std_Time_TimeZone_Offset_toIsoString___closed__5_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__5);
v_minute_154_ = lean_int_ediv(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7);
v___x_156_ = lean_int_dec_lt(v_hour_151_, v___x_155_);
v___x_157_ = lean_int_dec_lt(v_minute_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v_intZero_158_; uint8_t v_isNeg_159_; 
v_intZero_158_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__1, &l_Std_Time_TimeZone_Offset_toIsoString___closed__1_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__1);
v_isNeg_159_ = lean_int_dec_lt(v_hour_151_, v_intZero_158_);
if (v_isNeg_159_ == 0)
{
lean_object* v_a_160_; lean_object* v___x_161_; 
v_a_160_ = lean_nat_abs(v_hour_151_);
lean_dec(v_hour_151_);
v___x_161_ = l_Nat_reprFast(v_a_160_);
v___y_110_ = v_minute_154_;
v___y_111_ = v___x_157_;
v___y_112_ = v___x_149_;
v___y_113_ = v_fst_147_;
v___y_114_ = v___x_161_;
goto v___jp_109_;
}
else
{
lean_object* v_abs_162_; lean_object* v_a_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_abs_162_ = lean_nat_abs(v_hour_151_);
lean_dec(v_hour_151_);
v_a_163_ = lean_nat_sub(v_abs_162_, v___x_149_);
lean_dec(v_abs_162_);
v___x_164_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__2));
v___x_165_ = lean_nat_add(v_a_163_, v___x_149_);
lean_dec(v_a_163_);
v___x_166_ = l_Nat_reprFast(v___x_165_);
v___x_167_ = lean_string_append(v___x_164_, v___x_166_);
lean_dec_ref(v___x_166_);
v___y_110_ = v_minute_154_;
v___y_111_ = v___x_157_;
v___y_112_ = v___x_149_;
v___y_113_ = v_fst_147_;
v___y_114_ = v___x_167_;
goto v___jp_109_;
}
}
else
{
lean_object* v___x_168_; lean_object* v_intZero_169_; uint8_t v_isNeg_170_; 
v___x_168_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__3));
v_intZero_169_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__1, &l_Std_Time_TimeZone_Offset_toIsoString___closed__1_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__1);
v_isNeg_170_ = lean_int_dec_lt(v_hour_151_, v_intZero_169_);
if (v_isNeg_170_ == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; 
v_a_171_ = lean_nat_abs(v_hour_151_);
lean_dec(v_hour_151_);
v___x_172_ = l_Nat_reprFast(v_a_171_);
v___y_139_ = v_minute_154_;
v___y_140_ = v___x_157_;
v___y_141_ = v___x_168_;
v___y_142_ = v_fst_147_;
v___y_143_ = v___x_149_;
v___y_144_ = v___x_172_;
goto v___jp_138_;
}
else
{
lean_object* v_abs_173_; lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_abs_173_ = lean_nat_abs(v_hour_151_);
lean_dec(v_hour_151_);
v_a_174_ = lean_nat_sub(v_abs_173_, v___x_149_);
lean_dec(v_abs_173_);
v___x_175_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__2));
v___x_176_ = lean_nat_add(v_a_174_, v___x_149_);
lean_dec(v_a_174_);
v___x_177_ = l_Nat_reprFast(v___x_176_);
v___x_178_ = lean_string_append(v___x_175_, v___x_177_);
lean_dec_ref(v___x_177_);
v___y_139_ = v_minute_154_;
v___y_140_ = v___x_157_;
v___y_141_ = v___x_168_;
v___y_142_ = v_fst_147_;
v___y_143_ = v___x_149_;
v___y_144_ = v___x_178_;
goto v___jp_138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString___boxed(lean_object* v_offset_184_, lean_object* v_colon_185_){
_start:
{
uint8_t v_colon_boxed_186_; lean_object* v_res_187_; 
v_colon_boxed_186_ = lean_unbox(v_colon_185_);
v_res_187_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_184_, v_colon_boxed_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__0(lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_nat_to_int(v_a_188_);
v___x_190_ = l_Rat_ofInt(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_zero(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__1, &l_Std_Time_TimeZone_Offset_toIsoString___closed__1_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__1);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object* v_n_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_194_ = lean_int_mul(v_n_192_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours___boxed(lean_object* v_n_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_195_);
lean_dec(v_n_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(lean_object* v_n_197_, lean_object* v_m_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_40__overap_203_; lean_object* v___x_204_; 
v___x_199_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_200_ = lean_int_mul(v_n_197_, v___x_199_);
v___x_201_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__5, &l_Std_Time_TimeZone_Offset_toIsoString___closed__5_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__5);
v___x_202_ = lean_int_mul(v_m_198_, v___x_201_);
v___x_40__overap_203_ = l_Std_Time_Second_instAddOffset;
v___x_204_ = lean_apply_2(v___x_40__overap_203_, v___x_200_, v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(lean_object* v_n_205_, lean_object* v_m_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(v_n_205_, v_m_206_);
lean_dec(v_m_206_);
lean_dec(v_n_205_);
return v_res_207_;
}
}
lean_object* runtime_initialize_Std_Time_Time(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Offset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_TimeZone_instInhabitedOffset = _init_l_Std_Time_TimeZone_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedOffset);
l_Std_Time_TimeZone_Offset_zero = _init_l_Std_Time_TimeZone_Offset_zero();
lean_mark_persistent(l_Std_Time_TimeZone_Offset_zero);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Offset(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Time(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Offset(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Offset(builtin);
}
#ifdef __cplusplus
}
#endif
