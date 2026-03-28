// Lean compiler output
// Module: Init.Data.Slice.Array.Basic
// Imports: public import Init.Data.Array.Subarray public import Init.Data.Slice.Notation public import Init.Data.Range.Polymorphic.Nat
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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__1___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__2___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__3___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__4___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__4___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__5___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__6___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__7___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__7___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__8___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__8___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__8___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__1___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__2___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__3___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__4___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__4___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__5___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__6___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__7___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__7___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__8___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__8___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___lam__0(lean_object* v_xs_1_, lean_object* v_range_2_){
_start:
{
lean_object* v_lower_3_; lean_object* v_upper_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_lower_3_ = lean_ctor_get(v_range_2_, 0);
lean_inc(v_lower_3_);
v_upper_4_ = lean_ctor_get(v_range_2_, 1);
lean_inc(v_upper_4_);
lean_dec_ref(v_range_2_);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_add(v_upper_4_, v___x_5_);
lean_dec(v_upper_4_);
v___x_7_ = l_Array_toSubarray___redArg(v_xs_1_, v_lower_3_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object* v_00_u03b1_9_){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = ((lean_object*)(l_instSliceableArrayNatSubarray___closed__0));
return v___f_10_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___lam__0(lean_object* v_xs_11_, lean_object* v_range_12_){
_start:
{
lean_object* v_lower_13_; lean_object* v_upper_14_; lean_object* v___x_15_; 
v_lower_13_ = lean_ctor_get(v_range_12_, 0);
lean_inc(v_lower_13_);
v_upper_14_ = lean_ctor_get(v_range_12_, 1);
lean_inc(v_upper_14_);
lean_dec_ref(v_range_12_);
v___x_15_ = l_Array_toSubarray___redArg(v_xs_11_, v_lower_13_, v_upper_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object* v_00_u03b1_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = ((lean_object*)(l_instSliceableArrayNatSubarray__1___closed__0));
return v___f_18_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___lam__0(lean_object* v_xs_19_, lean_object* v_range_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = lean_array_get_size(v_xs_19_);
v___x_23_ = lean_nat_dec_le(v_range_20_, v___x_21_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
v___x_24_ = l_Array_toSubarray___redArg(v_xs_19_, v_range_20_, v___x_22_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; 
lean_dec(v_range_20_);
v___x_25_ = l_Array_toSubarray___redArg(v_xs_19_, v___x_21_, v___x_22_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object* v_00_u03b1_27_){
_start:
{
lean_object* v___f_28_; 
v___f_28_ = ((lean_object*)(l_instSliceableArrayNatSubarray__2___closed__0));
return v___f_28_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0(lean_object* v_xs_29_, lean_object* v_range_30_){
_start:
{
lean_object* v_lower_31_; lean_object* v_upper_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_lower_31_ = lean_ctor_get(v_range_30_, 0);
v_upper_32_ = lean_ctor_get(v_range_30_, 1);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_lower_31_, v___x_33_);
v___x_35_ = lean_nat_add(v_upper_32_, v___x_33_);
v___x_36_ = l_Array_toSubarray___redArg(v_xs_29_, v___x_34_, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0___boxed(lean_object* v_xs_37_, lean_object* v_range_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_instSliceableArrayNatSubarray__3___lam__0(v_xs_37_, v_range_38_);
lean_dec_ref(v_range_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object* v_00_u03b1_41_){
_start:
{
lean_object* v___f_42_; 
v___f_42_ = ((lean_object*)(l_instSliceableArrayNatSubarray__3___closed__0));
return v___f_42_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___lam__0(lean_object* v_xs_43_, lean_object* v_range_44_){
_start:
{
lean_object* v_lower_45_; lean_object* v_upper_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_lower_45_ = lean_ctor_get(v_range_44_, 0);
lean_inc(v_lower_45_);
v_upper_46_ = lean_ctor_get(v_range_44_, 1);
lean_inc(v_upper_46_);
lean_dec_ref(v_range_44_);
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_lower_45_, v___x_47_);
lean_dec(v_lower_45_);
v___x_49_ = l_Array_toSubarray___redArg(v_xs_43_, v___x_48_, v_upper_46_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object* v_00_u03b1_51_){
_start:
{
lean_object* v___f_52_; 
v___f_52_ = ((lean_object*)(l_instSliceableArrayNatSubarray__4___closed__0));
return v___f_52_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0(lean_object* v_xs_53_, lean_object* v_range_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_array_get_size(v_xs_53_);
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_nat_add(v_range_54_, v___x_57_);
v___x_59_ = lean_nat_dec_le(v___x_58_, v___x_55_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = l_Array_toSubarray___redArg(v_xs_53_, v___x_58_, v___x_56_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
lean_dec(v___x_58_);
v___x_61_ = l_Array_toSubarray___redArg(v_xs_53_, v___x_55_, v___x_56_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0___boxed(lean_object* v_xs_62_, lean_object* v_range_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_instSliceableArrayNatSubarray__5___lam__0(v_xs_62_, v_range_63_);
lean_dec(v_range_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object* v_00_u03b1_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = ((lean_object*)(l_instSliceableArrayNatSubarray__5___closed__0));
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0(lean_object* v_xs_68_, lean_object* v_range_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_range_69_, v___x_71_);
v___x_73_ = l_Array_toSubarray___redArg(v_xs_68_, v___x_70_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0___boxed(lean_object* v_xs_74_, lean_object* v_range_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_instSliceableArrayNatSubarray__6___lam__0(v_xs_74_, v_range_75_);
lean_dec(v_range_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object* v_00_u03b1_78_){
_start:
{
lean_object* v___f_79_; 
v___f_79_ = ((lean_object*)(l_instSliceableArrayNatSubarray__6___closed__0));
return v___f_79_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___lam__0(lean_object* v_xs_80_, lean_object* v_range_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = l_Array_toSubarray___redArg(v_xs_80_, v___x_82_, v_range_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object* v_00_u03b1_85_){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = ((lean_object*)(l_instSliceableArrayNatSubarray__7___closed__0));
return v___f_86_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___lam__0(lean_object* v_xs_87_, lean_object* v_x_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_array_get_size(v_xs_87_);
v___x_91_ = l_Array_toSubarray___redArg(v_xs_87_, v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object* v_00_u03b1_93_){
_start:
{
lean_object* v___f_94_; 
v___f_94_ = ((lean_object*)(l_instSliceableArrayNatSubarray__8___closed__0));
return v___f_94_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0(lean_object* v_xs_95_, lean_object* v_range_96_){
_start:
{
lean_object* v_array_97_; lean_object* v_start_98_; lean_object* v_stop_99_; lean_object* v_lower_101_; lean_object* v_upper_102_; lean_object* v_lower_106_; lean_object* v_upper_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___y_111_; uint8_t v___x_115_; 
v_array_97_ = lean_ctor_get(v_xs_95_, 0);
lean_inc_ref(v_array_97_);
v_start_98_ = lean_ctor_get(v_xs_95_, 1);
lean_inc(v_start_98_);
v_stop_99_ = lean_ctor_get(v_xs_95_, 2);
lean_inc(v_stop_99_);
lean_dec_ref(v_xs_95_);
v_lower_106_ = lean_ctor_get(v_range_96_, 0);
v_upper_107_ = lean_ctor_get(v_range_96_, 1);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_nat_sub(v_stop_99_, v_start_98_);
lean_dec(v_stop_99_);
v___x_115_ = lean_nat_dec_le(v_lower_106_, v___x_108_);
if (v___x_115_ == 0)
{
v___y_111_ = v_lower_106_;
goto v___jp_110_;
}
else
{
v___y_111_ = v___x_108_;
goto v___jp_110_;
}
v___jp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_nat_add(v_lower_101_, v_start_98_);
v___x_104_ = lean_nat_add(v_upper_102_, v_start_98_);
lean_dec(v_start_98_);
lean_dec(v_upper_102_);
v___x_105_ = l_Array_toSubarray___redArg(v_array_97_, v___x_103_, v___x_104_);
return v___x_105_;
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v_upper_107_, v___x_112_);
v___x_114_ = lean_nat_dec_le(v___x_113_, v___x_109_);
if (v___x_114_ == 0)
{
lean_dec(v___x_113_);
v_lower_101_ = v___y_111_;
v_upper_102_ = v___x_109_;
goto v___jp_100_;
}
else
{
lean_dec(v___x_109_);
v_lower_101_ = v___y_111_;
v_upper_102_ = v___x_113_;
goto v___jp_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___lam__0___boxed(lean_object* v_xs_116_, lean_object* v_range_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_instSliceableSubarrayNat___lam__0(v_xs_116_, v_range_117_);
lean_dec_ref(v_range_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat(lean_object* v_00_u03b1_120_){
_start:
{
lean_object* v___f_121_; 
v___f_121_ = ((lean_object*)(l_instSliceableSubarrayNat___closed__0));
return v___f_121_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___lam__0(lean_object* v_xs_122_, lean_object* v_range_123_){
_start:
{
lean_object* v_array_124_; lean_object* v_start_125_; lean_object* v_stop_126_; lean_object* v_lower_128_; lean_object* v_upper_129_; lean_object* v_lower_133_; lean_object* v_upper_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___y_138_; uint8_t v___x_140_; 
v_array_124_ = lean_ctor_get(v_xs_122_, 0);
lean_inc_ref(v_array_124_);
v_start_125_ = lean_ctor_get(v_xs_122_, 1);
lean_inc(v_start_125_);
v_stop_126_ = lean_ctor_get(v_xs_122_, 2);
lean_inc(v_stop_126_);
lean_dec_ref(v_xs_122_);
v_lower_133_ = lean_ctor_get(v_range_123_, 0);
lean_inc(v_lower_133_);
v_upper_134_ = lean_ctor_get(v_range_123_, 1);
lean_inc(v_upper_134_);
lean_dec_ref(v_range_123_);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_nat_sub(v_stop_126_, v_start_125_);
lean_dec(v_stop_126_);
v___x_140_ = lean_nat_dec_le(v_lower_133_, v___x_135_);
if (v___x_140_ == 0)
{
v___y_138_ = v_lower_133_;
goto v___jp_137_;
}
else
{
lean_dec(v_lower_133_);
v___y_138_ = v___x_135_;
goto v___jp_137_;
}
v___jp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_nat_add(v_lower_128_, v_start_125_);
lean_dec(v_lower_128_);
v___x_131_ = lean_nat_add(v_upper_129_, v_start_125_);
lean_dec(v_start_125_);
lean_dec(v_upper_129_);
v___x_132_ = l_Array_toSubarray___redArg(v_array_124_, v___x_130_, v___x_131_);
return v___x_132_;
}
v___jp_137_:
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_le(v_upper_134_, v___x_136_);
if (v___x_139_ == 0)
{
lean_dec(v_upper_134_);
v_lower_128_ = v___y_138_;
v_upper_129_ = v___x_136_;
goto v___jp_127_;
}
else
{
lean_dec(v___x_136_);
v_lower_128_ = v___y_138_;
v_upper_129_ = v_upper_134_;
goto v___jp_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1(lean_object* v_00_u03b1_142_){
_start:
{
lean_object* v___f_143_; 
v___f_143_ = ((lean_object*)(l_instSliceableSubarrayNat__1___closed__0));
return v___f_143_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0(lean_object* v_xs_144_, lean_object* v_range_145_){
_start:
{
lean_object* v_array_146_; lean_object* v_start_147_; lean_object* v_stop_148_; lean_object* v_lower_150_; lean_object* v_upper_151_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_array_146_ = lean_ctor_get(v_xs_144_, 0);
lean_inc_ref(v_array_146_);
v_start_147_ = lean_ctor_get(v_xs_144_, 1);
lean_inc(v_start_147_);
v_stop_148_ = lean_ctor_get(v_xs_144_, 2);
lean_inc(v_stop_148_);
lean_dec_ref(v_xs_144_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_nat_sub(v_stop_148_, v_start_147_);
lean_dec(v_stop_148_);
v___x_157_ = lean_nat_dec_le(v_range_145_, v___x_155_);
if (v___x_157_ == 0)
{
v_lower_150_ = v_range_145_;
v_upper_151_ = v___x_156_;
goto v___jp_149_;
}
else
{
v_lower_150_ = v___x_155_;
v_upper_151_ = v___x_156_;
goto v___jp_149_;
}
v___jp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_nat_add(v_lower_150_, v_start_147_);
v___x_153_ = lean_nat_add(v_upper_151_, v_start_147_);
lean_dec(v_start_147_);
lean_dec(v_upper_151_);
v___x_154_ = l_Array_toSubarray___redArg(v_array_146_, v___x_152_, v___x_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___lam__0___boxed(lean_object* v_xs_158_, lean_object* v_range_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_instSliceableSubarrayNat__2___lam__0(v_xs_158_, v_range_159_);
lean_dec(v_range_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2(lean_object* v_00_u03b1_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = ((lean_object*)(l_instSliceableSubarrayNat__2___closed__0));
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0(lean_object* v_xs_164_, lean_object* v_range_165_){
_start:
{
lean_object* v_array_166_; lean_object* v_start_167_; lean_object* v_stop_168_; lean_object* v_lower_170_; lean_object* v_upper_171_; lean_object* v_lower_175_; lean_object* v_upper_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___y_181_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_array_166_ = lean_ctor_get(v_xs_164_, 0);
lean_inc_ref(v_array_166_);
v_start_167_ = lean_ctor_get(v_xs_164_, 1);
lean_inc(v_start_167_);
v_stop_168_ = lean_ctor_get(v_xs_164_, 2);
lean_inc(v_stop_168_);
lean_dec_ref(v_xs_164_);
v_lower_175_ = lean_ctor_get(v_range_165_, 0);
v_upper_176_ = lean_ctor_get(v_range_165_, 1);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_nat_sub(v_stop_168_, v_start_167_);
lean_dec(v_stop_168_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_lower_175_, v___x_179_);
v___x_185_ = lean_nat_dec_le(v___x_184_, v___x_177_);
if (v___x_185_ == 0)
{
v___y_181_ = v___x_184_;
goto v___jp_180_;
}
else
{
lean_dec(v___x_184_);
v___y_181_ = v___x_177_;
goto v___jp_180_;
}
v___jp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_nat_add(v_lower_170_, v_start_167_);
lean_dec(v_lower_170_);
v___x_173_ = lean_nat_add(v_upper_171_, v_start_167_);
lean_dec(v_start_167_);
lean_dec(v_upper_171_);
v___x_174_ = l_Array_toSubarray___redArg(v_array_166_, v___x_172_, v___x_173_);
return v___x_174_;
}
v___jp_180_:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_nat_add(v_upper_176_, v___x_179_);
v___x_183_ = lean_nat_dec_le(v___x_182_, v___x_178_);
if (v___x_183_ == 0)
{
lean_dec(v___x_182_);
v_lower_170_ = v___y_181_;
v_upper_171_ = v___x_178_;
goto v___jp_169_;
}
else
{
lean_dec(v___x_178_);
v_lower_170_ = v___y_181_;
v_upper_171_ = v___x_182_;
goto v___jp_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___lam__0___boxed(lean_object* v_xs_186_, lean_object* v_range_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_instSliceableSubarrayNat__3___lam__0(v_xs_186_, v_range_187_);
lean_dec_ref(v_range_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3(lean_object* v_00_u03b1_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = ((lean_object*)(l_instSliceableSubarrayNat__3___closed__0));
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___lam__0(lean_object* v_xs_192_, lean_object* v_range_193_){
_start:
{
lean_object* v_array_194_; lean_object* v_start_195_; lean_object* v_stop_196_; lean_object* v_lower_198_; lean_object* v_upper_199_; lean_object* v_lower_203_; lean_object* v_upper_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___y_208_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_array_194_ = lean_ctor_get(v_xs_192_, 0);
lean_inc_ref(v_array_194_);
v_start_195_ = lean_ctor_get(v_xs_192_, 1);
lean_inc(v_start_195_);
v_stop_196_ = lean_ctor_get(v_xs_192_, 2);
lean_inc(v_stop_196_);
lean_dec_ref(v_xs_192_);
v_lower_203_ = lean_ctor_get(v_range_193_, 0);
lean_inc(v_lower_203_);
v_upper_204_ = lean_ctor_get(v_range_193_, 1);
lean_inc(v_upper_204_);
lean_dec_ref(v_range_193_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_sub(v_stop_196_, v_start_195_);
lean_dec(v_stop_196_);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_lower_203_, v___x_210_);
lean_dec(v_lower_203_);
v___x_212_ = lean_nat_dec_le(v___x_211_, v___x_205_);
if (v___x_212_ == 0)
{
v___y_208_ = v___x_211_;
goto v___jp_207_;
}
else
{
lean_dec(v___x_211_);
v___y_208_ = v___x_205_;
goto v___jp_207_;
}
v___jp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_nat_add(v_lower_198_, v_start_195_);
lean_dec(v_lower_198_);
v___x_201_ = lean_nat_add(v_upper_199_, v_start_195_);
lean_dec(v_start_195_);
lean_dec(v_upper_199_);
v___x_202_ = l_Array_toSubarray___redArg(v_array_194_, v___x_200_, v___x_201_);
return v___x_202_;
}
v___jp_207_:
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_le(v_upper_204_, v___x_206_);
if (v___x_209_ == 0)
{
lean_dec(v_upper_204_);
v_lower_198_ = v___y_208_;
v_upper_199_ = v___x_206_;
goto v___jp_197_;
}
else
{
lean_dec(v___x_206_);
v_lower_198_ = v___y_208_;
v_upper_199_ = v_upper_204_;
goto v___jp_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4(lean_object* v_00_u03b1_214_){
_start:
{
lean_object* v___f_215_; 
v___f_215_ = ((lean_object*)(l_instSliceableSubarrayNat__4___closed__0));
return v___f_215_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0(lean_object* v_xs_216_, lean_object* v_range_217_){
_start:
{
lean_object* v_array_218_; lean_object* v_start_219_; lean_object* v_stop_220_; lean_object* v_lower_222_; lean_object* v_upper_223_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_array_218_ = lean_ctor_get(v_xs_216_, 0);
lean_inc_ref(v_array_218_);
v_start_219_ = lean_ctor_get(v_xs_216_, 1);
lean_inc(v_start_219_);
v_stop_220_ = lean_ctor_get(v_xs_216_, 2);
lean_inc(v_stop_220_);
lean_dec_ref(v_xs_216_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_sub(v_stop_220_, v_start_219_);
lean_dec(v_stop_220_);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_add(v_range_217_, v___x_229_);
v___x_231_ = lean_nat_dec_le(v___x_230_, v___x_227_);
if (v___x_231_ == 0)
{
v_lower_222_ = v___x_230_;
v_upper_223_ = v___x_228_;
goto v___jp_221_;
}
else
{
lean_dec(v___x_230_);
v_lower_222_ = v___x_227_;
v_upper_223_ = v___x_228_;
goto v___jp_221_;
}
v___jp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_nat_add(v_lower_222_, v_start_219_);
lean_dec(v_lower_222_);
v___x_225_ = lean_nat_add(v_upper_223_, v_start_219_);
lean_dec(v_start_219_);
lean_dec(v_upper_223_);
v___x_226_ = l_Array_toSubarray___redArg(v_array_218_, v___x_224_, v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___lam__0___boxed(lean_object* v_xs_232_, lean_object* v_range_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_instSliceableSubarrayNat__5___lam__0(v_xs_232_, v_range_233_);
lean_dec(v_range_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5(lean_object* v_00_u03b1_236_){
_start:
{
lean_object* v___f_237_; 
v___f_237_ = ((lean_object*)(l_instSliceableSubarrayNat__5___closed__0));
return v___f_237_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0(lean_object* v_xs_238_, lean_object* v_range_239_){
_start:
{
lean_object* v_array_240_; lean_object* v_start_241_; lean_object* v_stop_242_; lean_object* v_lower_244_; lean_object* v_upper_245_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_array_240_ = lean_ctor_get(v_xs_238_, 0);
lean_inc_ref(v_array_240_);
v_start_241_ = lean_ctor_get(v_xs_238_, 1);
lean_inc(v_start_241_);
v_stop_242_ = lean_ctor_get(v_xs_238_, 2);
lean_inc(v_stop_242_);
lean_dec_ref(v_xs_238_);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_nat_sub(v_stop_242_, v_start_241_);
lean_dec(v_stop_242_);
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_nat_add(v_range_239_, v___x_251_);
v___x_253_ = lean_nat_dec_le(v___x_252_, v___x_250_);
if (v___x_253_ == 0)
{
lean_dec(v___x_252_);
v_lower_244_ = v___x_249_;
v_upper_245_ = v___x_250_;
goto v___jp_243_;
}
else
{
lean_dec(v___x_250_);
v_lower_244_ = v___x_249_;
v_upper_245_ = v___x_252_;
goto v___jp_243_;
}
v___jp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_nat_add(v_lower_244_, v_start_241_);
v___x_247_ = lean_nat_add(v_upper_245_, v_start_241_);
lean_dec(v_start_241_);
lean_dec(v_upper_245_);
v___x_248_ = l_Array_toSubarray___redArg(v_array_240_, v___x_246_, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___lam__0___boxed(lean_object* v_xs_254_, lean_object* v_range_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_instSliceableSubarrayNat__6___lam__0(v_xs_254_, v_range_255_);
lean_dec(v_range_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6(lean_object* v_00_u03b1_258_){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = ((lean_object*)(l_instSliceableSubarrayNat__6___closed__0));
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___lam__0(lean_object* v_xs_260_, lean_object* v_range_261_){
_start:
{
lean_object* v_array_262_; lean_object* v_start_263_; lean_object* v_stop_264_; lean_object* v_lower_266_; lean_object* v_upper_267_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_array_262_ = lean_ctor_get(v_xs_260_, 0);
lean_inc_ref(v_array_262_);
v_start_263_ = lean_ctor_get(v_xs_260_, 1);
lean_inc(v_start_263_);
v_stop_264_ = lean_ctor_get(v_xs_260_, 2);
lean_inc(v_stop_264_);
lean_dec_ref(v_xs_260_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_nat_sub(v_stop_264_, v_start_263_);
lean_dec(v_stop_264_);
v___x_273_ = lean_nat_dec_le(v_range_261_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v_range_261_);
v_lower_266_ = v___x_271_;
v_upper_267_ = v___x_272_;
goto v___jp_265_;
}
else
{
lean_dec(v___x_272_);
v_lower_266_ = v___x_271_;
v_upper_267_ = v_range_261_;
goto v___jp_265_;
}
v___jp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_nat_add(v_lower_266_, v_start_263_);
v___x_269_ = lean_nat_add(v_upper_267_, v_start_263_);
lean_dec(v_start_263_);
lean_dec(v_upper_267_);
v___x_270_ = l_Array_toSubarray___redArg(v_array_262_, v___x_268_, v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7(lean_object* v_00_u03b1_275_){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = ((lean_object*)(l_instSliceableSubarrayNat__7___closed__0));
return v___f_276_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0(lean_object* v_xs_277_, lean_object* v_x_278_){
_start:
{
lean_inc_ref(v_xs_277_);
return v_xs_277_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___lam__0___boxed(lean_object* v_xs_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_instSliceableSubarrayNat__8___lam__0(v_xs_279_, v_x_280_);
lean_dec_ref(v_xs_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8(lean_object* v_00_u03b1_283_){
_start:
{
lean_object* v___f_284_; 
v___f_284_ = ((lean_object*)(l_instSliceableSubarrayNat__8___closed__0));
return v___f_284_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_Array_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
