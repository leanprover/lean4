// Lean compiler output
// Module: Init.Data.Slice.List.Basic
// Imports: public import Init.Data.Slice.Basic public import Init.Data.Slice.Notation
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static const lean_ctor_object l_List_toSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_toSlice___redArg___closed__0 = (const lean_object*)&l_List_toSlice___redArg___closed__0_value;
static const lean_ctor_object l_List_toSlice___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_toSlice___redArg___closed__0_value)}};
static const lean_object* l_List_toSlice___redArg___closed__1 = (const lean_object*)&l_List_toSlice___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_toSlice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSlice___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSlice(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toUnboundedSlice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toUnboundedSlice___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toUnboundedSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toUnboundedSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__1___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1(lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_toUnboundedSlice___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__2___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__3___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__4___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__4___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__5___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__6___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__7___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__7___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__8___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__8___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat___closed__0 = (const lean_object*)&l_instSliceableListSliceNat___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__1___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__2___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__3___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__4___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__4___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__5___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__6___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__7___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__7___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__8___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__8___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8(lean_object*);
LEAN_EXPORT lean_object* l_List_toSlice___redArg(lean_object* v_as_6_, lean_object* v_start_7_, lean_object* v_stop_8_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_lt(v_start_7_, v_stop_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_start_7_);
v___x_10_ = ((lean_object*)(l_List_toSlice___redArg___closed__1));
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
lean_inc(v_start_7_);
v___x_11_ = l_List_drop___redArg(v_start_7_, v_as_6_);
v___x_12_ = lean_nat_sub(v_stop_8_, v_start_7_);
lean_dec(v_start_7_);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_11_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_List_toSlice___redArg___boxed(lean_object* v_as_15_, lean_object* v_start_16_, lean_object* v_stop_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_List_toSlice___redArg(v_as_15_, v_start_16_, v_stop_17_);
lean_dec(v_stop_17_);
lean_dec(v_as_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_List_toSlice(lean_object* v_00_u03b1_19_, lean_object* v_as_20_, lean_object* v_start_21_, lean_object* v_stop_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_List_toSlice___redArg(v_as_20_, v_start_21_, v_stop_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_List_toSlice___boxed(lean_object* v_00_u03b1_24_, lean_object* v_as_25_, lean_object* v_start_26_, lean_object* v_stop_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_List_toSlice(v_00_u03b1_24_, v_as_25_, v_start_26_, v_stop_27_);
lean_dec(v_stop_27_);
lean_dec(v_as_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_List_toUnboundedSlice___redArg(lean_object* v_as_29_, lean_object* v_start_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = l_List_drop___redArg(v_start_30_, v_as_29_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_31_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_List_toUnboundedSlice___redArg___boxed(lean_object* v_as_34_, lean_object* v_start_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_List_toUnboundedSlice___redArg(v_as_34_, v_start_35_);
lean_dec(v_as_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_List_toUnboundedSlice(lean_object* v_00_u03b1_37_, lean_object* v_as_38_, lean_object* v_start_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_List_toUnboundedSlice___redArg(v_as_38_, v_start_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_List_toUnboundedSlice___boxed(lean_object* v_00_u03b1_41_, lean_object* v_as_42_, lean_object* v_start_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_List_toUnboundedSlice(v_00_u03b1_41_, v_as_42_, v_start_43_);
lean_dec(v_as_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___lam__0(lean_object* v_xs_45_, lean_object* v_range_46_){
_start:
{
lean_object* v_lower_47_; lean_object* v_upper_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_lower_47_ = lean_ctor_get(v_range_46_, 0);
lean_inc(v_lower_47_);
v_upper_48_ = lean_ctor_get(v_range_46_, 1);
lean_inc(v_upper_48_);
lean_dec_ref(v_range_46_);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_upper_48_, v___x_49_);
lean_dec(v_upper_48_);
v___x_51_ = l_List_toSlice___redArg(v_xs_45_, v_lower_47_, v___x_50_);
lean_dec(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___lam__0___boxed(lean_object* v_xs_52_, lean_object* v_range_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_instSliceableListNatListSlice___lam__0(v_xs_52_, v_range_53_);
lean_dec(v_xs_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice(lean_object* v_00_u03b1_56_){
_start:
{
lean_object* v___f_57_; 
v___f_57_ = ((lean_object*)(l_instSliceableListNatListSlice___closed__0));
return v___f_57_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___lam__0(lean_object* v_xs_58_, lean_object* v_range_59_){
_start:
{
lean_object* v_lower_60_; lean_object* v_upper_61_; lean_object* v___x_62_; 
v_lower_60_ = lean_ctor_get(v_range_59_, 0);
lean_inc(v_lower_60_);
v_upper_61_ = lean_ctor_get(v_range_59_, 1);
lean_inc(v_upper_61_);
lean_dec_ref(v_range_59_);
v___x_62_ = l_List_toSlice___redArg(v_xs_58_, v_lower_60_, v_upper_61_);
lean_dec(v_upper_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___lam__0___boxed(lean_object* v_xs_63_, lean_object* v_range_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_instSliceableListNatListSlice__1___lam__0(v_xs_63_, v_range_64_);
lean_dec(v_xs_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1(lean_object* v_00_u03b1_67_){
_start:
{
lean_object* v___f_68_; 
v___f_68_ = ((lean_object*)(l_instSliceableListNatListSlice__1___closed__0));
return v___f_68_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2(lean_object* v_00_u03b1_70_){
_start:
{
lean_object* v___f_71_; 
v___f_71_ = ((lean_object*)(l_instSliceableListNatListSlice__2___closed__0));
return v___f_71_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___lam__0(lean_object* v_xs_72_, lean_object* v_range_73_){
_start:
{
lean_object* v_lower_74_; lean_object* v_upper_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_lower_74_ = lean_ctor_get(v_range_73_, 0);
v_upper_75_ = lean_ctor_get(v_range_73_, 1);
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_add(v_lower_74_, v___x_76_);
v___x_78_ = lean_nat_add(v_upper_75_, v___x_76_);
v___x_79_ = l_List_toSlice___redArg(v_xs_72_, v___x_77_, v___x_78_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___lam__0___boxed(lean_object* v_xs_80_, lean_object* v_range_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_instSliceableListNatListSlice__3___lam__0(v_xs_80_, v_range_81_);
lean_dec_ref(v_range_81_);
lean_dec(v_xs_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3(lean_object* v_00_u03b1_84_){
_start:
{
lean_object* v___f_85_; 
v___f_85_ = ((lean_object*)(l_instSliceableListNatListSlice__3___closed__0));
return v___f_85_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___lam__0(lean_object* v_xs_86_, lean_object* v_range_87_){
_start:
{
lean_object* v_lower_88_; lean_object* v_upper_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_lower_88_ = lean_ctor_get(v_range_87_, 0);
v_upper_89_ = lean_ctor_get(v_range_87_, 1);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_lower_88_, v___x_90_);
v___x_92_ = l_List_toSlice___redArg(v_xs_86_, v___x_91_, v_upper_89_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___lam__0___boxed(lean_object* v_xs_93_, lean_object* v_range_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_instSliceableListNatListSlice__4___lam__0(v_xs_93_, v_range_94_);
lean_dec_ref(v_range_94_);
lean_dec(v_xs_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4(lean_object* v_00_u03b1_97_){
_start:
{
lean_object* v___f_98_; 
v___f_98_ = ((lean_object*)(l_instSliceableListNatListSlice__4___closed__0));
return v___f_98_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___lam__0(lean_object* v_xs_99_, lean_object* v_range_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_range_100_, v___x_101_);
v___x_103_ = l_List_toUnboundedSlice___redArg(v_xs_99_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___lam__0___boxed(lean_object* v_xs_104_, lean_object* v_range_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_instSliceableListNatListSlice__5___lam__0(v_xs_104_, v_range_105_);
lean_dec(v_range_105_);
lean_dec(v_xs_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5(lean_object* v_00_u03b1_108_){
_start:
{
lean_object* v___f_109_; 
v___f_109_ = ((lean_object*)(l_instSliceableListNatListSlice__5___closed__0));
return v___f_109_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___lam__0(lean_object* v_xs_110_, lean_object* v_range_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_add(v_range_111_, v___x_113_);
v___x_115_ = l_List_toSlice___redArg(v_xs_110_, v___x_112_, v___x_114_);
lean_dec(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___lam__0___boxed(lean_object* v_xs_116_, lean_object* v_range_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_instSliceableListNatListSlice__6___lam__0(v_xs_116_, v_range_117_);
lean_dec(v_range_117_);
lean_dec(v_xs_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6(lean_object* v_00_u03b1_120_){
_start:
{
lean_object* v___f_121_; 
v___f_121_ = ((lean_object*)(l_instSliceableListNatListSlice__6___closed__0));
return v___f_121_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___lam__0(lean_object* v_xs_122_, lean_object* v_range_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_List_toSlice___redArg(v_xs_122_, v___x_124_, v_range_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___lam__0___boxed(lean_object* v_xs_126_, lean_object* v_range_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_instSliceableListNatListSlice__7___lam__0(v_xs_126_, v_range_127_);
lean_dec(v_range_127_);
lean_dec(v_xs_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7(lean_object* v_00_u03b1_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = ((lean_object*)(l_instSliceableListNatListSlice__7___closed__0));
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___lam__0(lean_object* v_xs_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = l_List_toUnboundedSlice___redArg(v_xs_132_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___lam__0___boxed(lean_object* v_xs_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_instSliceableListNatListSlice__8___lam__0(v_xs_136_, v_x_137_);
lean_dec(v_xs_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8(lean_object* v_00_u03b1_140_){
_start:
{
lean_object* v___f_141_; 
v___f_141_ = ((lean_object*)(l_instSliceableListNatListSlice__8___closed__0));
return v___f_141_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___lam__0(lean_object* v_xs_142_, lean_object* v_range_143_){
_start:
{
lean_object* v_list_144_; lean_object* v_stop_145_; lean_object* v___y_147_; 
v_list_144_ = lean_ctor_get(v_xs_142_, 0);
lean_inc(v_list_144_);
v_stop_145_ = lean_ctor_get(v_xs_142_, 1);
lean_inc(v_stop_145_);
lean_dec_ref(v_xs_142_);
if (lean_obj_tag(v_stop_145_) == 0)
{
lean_object* v_upper_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_upper_150_ = lean_ctor_get(v_range_143_, 1);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_upper_150_, v___x_151_);
v___y_147_ = v___x_152_;
goto v___jp_146_;
}
else
{
lean_object* v_val_153_; lean_object* v_upper_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_val_153_ = lean_ctor_get(v_stop_145_, 0);
lean_inc(v_val_153_);
lean_dec_ref(v_stop_145_);
v_upper_154_ = lean_ctor_get(v_range_143_, 1);
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_add(v_upper_154_, v___x_155_);
v___x_157_ = lean_nat_dec_le(v_val_153_, v___x_156_);
if (v___x_157_ == 0)
{
lean_dec(v_val_153_);
v___y_147_ = v___x_156_;
goto v___jp_146_;
}
else
{
lean_dec(v___x_156_);
v___y_147_ = v_val_153_;
goto v___jp_146_;
}
}
v___jp_146_:
{
lean_object* v_lower_148_; lean_object* v___x_149_; 
v_lower_148_ = lean_ctor_get(v_range_143_, 0);
lean_inc(v_lower_148_);
lean_dec_ref(v_range_143_);
v___x_149_ = l_List_toSlice___redArg(v_list_144_, v_lower_148_, v___y_147_);
lean_dec(v___y_147_);
lean_dec(v_list_144_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat(lean_object* v_00_u03b1_159_){
_start:
{
lean_object* v___f_160_; 
v___f_160_ = ((lean_object*)(l_instSliceableListSliceNat___closed__0));
return v___f_160_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___lam__0(lean_object* v_xs_161_, lean_object* v_range_162_){
_start:
{
lean_object* v_list_163_; lean_object* v_stop_164_; lean_object* v___y_166_; 
v_list_163_ = lean_ctor_get(v_xs_161_, 0);
lean_inc(v_list_163_);
v_stop_164_ = lean_ctor_get(v_xs_161_, 1);
lean_inc(v_stop_164_);
lean_dec_ref(v_xs_161_);
if (lean_obj_tag(v_stop_164_) == 0)
{
lean_object* v_upper_169_; 
v_upper_169_ = lean_ctor_get(v_range_162_, 1);
lean_inc(v_upper_169_);
v___y_166_ = v_upper_169_;
goto v___jp_165_;
}
else
{
lean_object* v_val_170_; lean_object* v_upper_171_; uint8_t v___x_172_; 
v_val_170_ = lean_ctor_get(v_stop_164_, 0);
lean_inc(v_val_170_);
lean_dec_ref(v_stop_164_);
v_upper_171_ = lean_ctor_get(v_range_162_, 1);
v___x_172_ = lean_nat_dec_le(v_val_170_, v_upper_171_);
if (v___x_172_ == 0)
{
lean_dec(v_val_170_);
lean_inc(v_upper_171_);
v___y_166_ = v_upper_171_;
goto v___jp_165_;
}
else
{
v___y_166_ = v_val_170_;
goto v___jp_165_;
}
}
v___jp_165_:
{
lean_object* v_lower_167_; lean_object* v___x_168_; 
v_lower_167_ = lean_ctor_get(v_range_162_, 0);
lean_inc(v_lower_167_);
lean_dec_ref(v_range_162_);
v___x_168_ = l_List_toSlice___redArg(v_list_163_, v_lower_167_, v___y_166_);
lean_dec(v___y_166_);
lean_dec(v_list_163_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1(lean_object* v_00_u03b1_174_){
_start:
{
lean_object* v___f_175_; 
v___f_175_ = ((lean_object*)(l_instSliceableListSliceNat__1___closed__0));
return v___f_175_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___lam__0(lean_object* v_xs_176_, lean_object* v_range_177_){
_start:
{
lean_object* v_stop_178_; 
v_stop_178_ = lean_ctor_get(v_xs_176_, 1);
if (lean_obj_tag(v_stop_178_) == 0)
{
lean_object* v_list_179_; lean_object* v___x_180_; 
v_list_179_ = lean_ctor_get(v_xs_176_, 0);
v___x_180_ = l_List_toUnboundedSlice___redArg(v_list_179_, v_range_177_);
return v___x_180_;
}
else
{
lean_object* v_list_181_; lean_object* v_val_182_; lean_object* v___x_183_; 
v_list_181_ = lean_ctor_get(v_xs_176_, 0);
v_val_182_ = lean_ctor_get(v_stop_178_, 0);
v___x_183_ = l_List_toSlice___redArg(v_list_181_, v_range_177_, v_val_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___lam__0___boxed(lean_object* v_xs_184_, lean_object* v_range_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_instSliceableListSliceNat__2___lam__0(v_xs_184_, v_range_185_);
lean_dec_ref(v_xs_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2(lean_object* v_00_u03b1_188_){
_start:
{
lean_object* v___f_189_; 
v___f_189_ = ((lean_object*)(l_instSliceableListSliceNat__2___closed__0));
return v___f_189_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___lam__0(lean_object* v_xs_190_, lean_object* v_range_191_){
_start:
{
lean_object* v_list_192_; lean_object* v_stop_193_; lean_object* v___y_195_; 
v_list_192_ = lean_ctor_get(v_xs_190_, 0);
lean_inc(v_list_192_);
v_stop_193_ = lean_ctor_get(v_xs_190_, 1);
lean_inc(v_stop_193_);
lean_dec_ref(v_xs_190_);
if (lean_obj_tag(v_stop_193_) == 0)
{
lean_object* v_upper_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_upper_200_ = lean_ctor_get(v_range_191_, 1);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_upper_200_, v___x_201_);
v___y_195_ = v___x_202_;
goto v___jp_194_;
}
else
{
lean_object* v_val_203_; lean_object* v_upper_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_val_203_ = lean_ctor_get(v_stop_193_, 0);
lean_inc(v_val_203_);
lean_dec_ref(v_stop_193_);
v_upper_204_ = lean_ctor_get(v_range_191_, 1);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_add(v_upper_204_, v___x_205_);
v___x_207_ = lean_nat_dec_le(v_val_203_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v_val_203_);
v___y_195_ = v___x_206_;
goto v___jp_194_;
}
else
{
lean_dec(v___x_206_);
v___y_195_ = v_val_203_;
goto v___jp_194_;
}
}
v___jp_194_:
{
lean_object* v_lower_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_lower_196_ = lean_ctor_get(v_range_191_, 0);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_add(v_lower_196_, v___x_197_);
v___x_199_ = l_List_toSlice___redArg(v_list_192_, v___x_198_, v___y_195_);
lean_dec(v___y_195_);
lean_dec(v_list_192_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___lam__0___boxed(lean_object* v_xs_208_, lean_object* v_range_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_instSliceableListSliceNat__3___lam__0(v_xs_208_, v_range_209_);
lean_dec_ref(v_range_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3(lean_object* v_00_u03b1_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = ((lean_object*)(l_instSliceableListSliceNat__3___closed__0));
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___lam__0(lean_object* v_xs_214_, lean_object* v_range_215_){
_start:
{
lean_object* v_list_216_; lean_object* v_stop_217_; lean_object* v___y_219_; 
v_list_216_ = lean_ctor_get(v_xs_214_, 0);
v_stop_217_ = lean_ctor_get(v_xs_214_, 1);
if (lean_obj_tag(v_stop_217_) == 0)
{
lean_object* v_upper_224_; 
v_upper_224_ = lean_ctor_get(v_range_215_, 1);
v___y_219_ = v_upper_224_;
goto v___jp_218_;
}
else
{
lean_object* v_val_225_; lean_object* v_upper_226_; uint8_t v___x_227_; 
v_val_225_ = lean_ctor_get(v_stop_217_, 0);
v_upper_226_ = lean_ctor_get(v_range_215_, 1);
v___x_227_ = lean_nat_dec_le(v_val_225_, v_upper_226_);
if (v___x_227_ == 0)
{
v___y_219_ = v_upper_226_;
goto v___jp_218_;
}
else
{
v___y_219_ = v_val_225_;
goto v___jp_218_;
}
}
v___jp_218_:
{
lean_object* v_lower_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_lower_220_ = lean_ctor_get(v_range_215_, 0);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_lower_220_, v___x_221_);
v___x_223_ = l_List_toSlice___redArg(v_list_216_, v___x_222_, v___y_219_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___lam__0___boxed(lean_object* v_xs_228_, lean_object* v_range_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_instSliceableListSliceNat__4___lam__0(v_xs_228_, v_range_229_);
lean_dec_ref(v_range_229_);
lean_dec_ref(v_xs_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4(lean_object* v_00_u03b1_232_){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = ((lean_object*)(l_instSliceableListSliceNat__4___closed__0));
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___lam__0(lean_object* v_xs_234_, lean_object* v_range_235_){
_start:
{
lean_object* v_stop_236_; 
v_stop_236_ = lean_ctor_get(v_xs_234_, 1);
if (lean_obj_tag(v_stop_236_) == 0)
{
lean_object* v_list_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_list_237_ = lean_ctor_get(v_xs_234_, 0);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_range_235_, v___x_238_);
v___x_240_ = l_List_toUnboundedSlice___redArg(v_list_237_, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_list_241_; lean_object* v_val_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_list_241_ = lean_ctor_get(v_xs_234_, 0);
v_val_242_ = lean_ctor_get(v_stop_236_, 0);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_range_235_, v___x_243_);
v___x_245_ = l_List_toSlice___redArg(v_list_241_, v___x_244_, v_val_242_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___lam__0___boxed(lean_object* v_xs_246_, lean_object* v_range_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_instSliceableListSliceNat__5___lam__0(v_xs_246_, v_range_247_);
lean_dec(v_range_247_);
lean_dec_ref(v_xs_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5(lean_object* v_00_u03b1_250_){
_start:
{
lean_object* v___f_251_; 
v___f_251_ = ((lean_object*)(l_instSliceableListSliceNat__5___closed__0));
return v___f_251_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___lam__0(lean_object* v_xs_252_, lean_object* v_range_253_){
_start:
{
lean_object* v_list_254_; lean_object* v_stop_255_; lean_object* v___y_257_; 
v_list_254_ = lean_ctor_get(v_xs_252_, 0);
lean_inc(v_list_254_);
v_stop_255_ = lean_ctor_get(v_xs_252_, 1);
lean_inc(v_stop_255_);
lean_dec_ref(v_xs_252_);
if (lean_obj_tag(v_stop_255_) == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_range_253_, v___x_260_);
v___y_257_ = v___x_261_;
goto v___jp_256_;
}
else
{
lean_object* v_val_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_val_262_ = lean_ctor_get(v_stop_255_, 0);
lean_inc(v_val_262_);
lean_dec_ref(v_stop_255_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_range_253_, v___x_263_);
v___x_265_ = lean_nat_dec_le(v_val_262_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec(v_val_262_);
v___y_257_ = v___x_264_;
goto v___jp_256_;
}
else
{
lean_dec(v___x_264_);
v___y_257_ = v_val_262_;
goto v___jp_256_;
}
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = l_List_toSlice___redArg(v_list_254_, v___x_258_, v___y_257_);
lean_dec(v___y_257_);
lean_dec(v_list_254_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___lam__0___boxed(lean_object* v_xs_266_, lean_object* v_range_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_instSliceableListSliceNat__6___lam__0(v_xs_266_, v_range_267_);
lean_dec(v_range_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6(lean_object* v_00_u03b1_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = ((lean_object*)(l_instSliceableListSliceNat__6___closed__0));
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___lam__0(lean_object* v_xs_272_, lean_object* v_range_273_){
_start:
{
lean_object* v_list_274_; lean_object* v_stop_275_; lean_object* v___y_277_; 
v_list_274_ = lean_ctor_get(v_xs_272_, 0);
v_stop_275_ = lean_ctor_get(v_xs_272_, 1);
if (lean_obj_tag(v_stop_275_) == 0)
{
v___y_277_ = v_range_273_;
goto v___jp_276_;
}
else
{
lean_object* v_val_280_; uint8_t v___x_281_; 
v_val_280_ = lean_ctor_get(v_stop_275_, 0);
v___x_281_ = lean_nat_dec_le(v_val_280_, v_range_273_);
if (v___x_281_ == 0)
{
v___y_277_ = v_range_273_;
goto v___jp_276_;
}
else
{
v___y_277_ = v_val_280_;
goto v___jp_276_;
}
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = l_List_toSlice___redArg(v_list_274_, v___x_278_, v___y_277_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___lam__0___boxed(lean_object* v_xs_282_, lean_object* v_range_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_instSliceableListSliceNat__7___lam__0(v_xs_282_, v_range_283_);
lean_dec(v_range_283_);
lean_dec_ref(v_xs_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7(lean_object* v_00_u03b1_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = ((lean_object*)(l_instSliceableListSliceNat__7___closed__0));
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___lam__0(lean_object* v_xs_288_, lean_object* v_x_289_){
_start:
{
lean_inc_ref(v_xs_288_);
return v_xs_288_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___lam__0___boxed(lean_object* v_xs_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_instSliceableListSliceNat__8___lam__0(v_xs_290_, v_x_291_);
lean_dec_ref(v_xs_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8(lean_object* v_00_u03b1_294_){
_start:
{
lean_object* v___f_295_; 
v___f_295_ = ((lean_object*)(l_instSliceableListSliceNat__8___closed__0));
return v___f_295_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Notation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_List_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
