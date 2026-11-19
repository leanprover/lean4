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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__1___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__1___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__2___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__2___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__3___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__4___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__4___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__5___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__5___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__6___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__6___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__7___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__7___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableArrayNatSubarray__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableArrayNatSubarray__8___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableArrayNatSubarray__8___redArg___closed__0 = (const lean_object*)&l_instSliceableArrayNatSubarray__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg();
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__1___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__1___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__2___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__3___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__4___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__4___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__5___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__5___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__6___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__6___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__7___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__7___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableSubarrayNat__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableSubarrayNat__8___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableSubarrayNat__8___redArg___closed__0 = (const lean_object*)&l_instSliceableSubarrayNat__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg();
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___redArg___lam__0(lean_object* v_xs_1_, lean_object* v_range_2_){
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
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___redArg(){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = ((lean_object*)(l_instSliceableArrayNatSubarray___redArg___closed__0));
return v___f_10_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___redArg___boxed(lean_object* v___dummy_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_instSliceableArrayNatSubarray___redArg();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object* v_00_u03b1_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = ((lean_object*)(l_instSliceableArrayNatSubarray___redArg___closed__0));
return v___f_14_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg___lam__0(lean_object* v_xs_15_, lean_object* v_range_16_){
_start:
{
lean_object* v_lower_17_; lean_object* v_upper_18_; lean_object* v___x_19_; 
v_lower_17_ = lean_ctor_get(v_range_16_, 0);
lean_inc(v_lower_17_);
v_upper_18_ = lean_ctor_get(v_range_16_, 1);
lean_inc(v_upper_18_);
lean_dec_ref(v_range_16_);
v___x_19_ = l_Array_toSubarray___redArg(v_xs_15_, v_lower_17_, v_upper_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg(){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = ((lean_object*)(l_instSliceableArrayNatSubarray__1___redArg___closed__0));
return v___f_22_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg___boxed(lean_object* v___dummy_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_instSliceableArrayNatSubarray__1___redArg();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object* v_00_u03b1_25_){
_start:
{
lean_object* v___f_26_; 
v___f_26_ = ((lean_object*)(l_instSliceableArrayNatSubarray__1___redArg___closed__0));
return v___f_26_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg___lam__0(lean_object* v_xs_27_, lean_object* v_range_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_array_get_size(v_xs_27_);
v___x_31_ = lean_nat_dec_le(v_range_28_, v___x_29_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
v___x_32_ = l_Array_toSubarray___redArg(v_xs_27_, v_range_28_, v___x_30_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; 
lean_dec(v_range_28_);
v___x_33_ = l_Array_toSubarray___redArg(v_xs_27_, v___x_29_, v___x_30_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg(){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = ((lean_object*)(l_instSliceableArrayNatSubarray__2___redArg___closed__0));
return v___f_36_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg___boxed(lean_object* v___dummy_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_instSliceableArrayNatSubarray__2___redArg();
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object* v_00_u03b1_39_){
_start:
{
lean_object* v___f_40_; 
v___f_40_ = ((lean_object*)(l_instSliceableArrayNatSubarray__2___redArg___closed__0));
return v___f_40_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___lam__0(lean_object* v_xs_41_, lean_object* v_range_42_){
_start:
{
lean_object* v_lower_43_; lean_object* v_upper_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_lower_43_ = lean_ctor_get(v_range_42_, 0);
v_upper_44_ = lean_ctor_get(v_range_42_, 1);
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_add(v_lower_43_, v___x_45_);
v___x_47_ = lean_nat_add(v_upper_44_, v___x_45_);
v___x_48_ = l_Array_toSubarray___redArg(v_xs_41_, v___x_46_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___lam__0___boxed(lean_object* v_xs_49_, lean_object* v_range_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_instSliceableArrayNatSubarray__3___redArg___lam__0(v_xs_49_, v_range_50_);
lean_dec_ref(v_range_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg(){
_start:
{
lean_object* v___f_54_; 
v___f_54_ = ((lean_object*)(l_instSliceableArrayNatSubarray__3___redArg___closed__0));
return v___f_54_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___boxed(lean_object* v___dummy_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_instSliceableArrayNatSubarray__3___redArg();
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object* v_00_u03b1_57_){
_start:
{
lean_object* v___f_58_; 
v___f_58_ = ((lean_object*)(l_instSliceableArrayNatSubarray__3___redArg___closed__0));
return v___f_58_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg___lam__0(lean_object* v_xs_59_, lean_object* v_range_60_){
_start:
{
lean_object* v_lower_61_; lean_object* v_upper_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_lower_61_ = lean_ctor_get(v_range_60_, 0);
lean_inc(v_lower_61_);
v_upper_62_ = lean_ctor_get(v_range_60_, 1);
lean_inc(v_upper_62_);
lean_dec_ref(v_range_60_);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_add(v_lower_61_, v___x_63_);
lean_dec(v_lower_61_);
v___x_65_ = l_Array_toSubarray___redArg(v_xs_59_, v___x_64_, v_upper_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg(){
_start:
{
lean_object* v___f_68_; 
v___f_68_ = ((lean_object*)(l_instSliceableArrayNatSubarray__4___redArg___closed__0));
return v___f_68_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg___boxed(lean_object* v___dummy_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_instSliceableArrayNatSubarray__4___redArg();
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object* v_00_u03b1_71_){
_start:
{
lean_object* v___f_72_; 
v___f_72_ = ((lean_object*)(l_instSliceableArrayNatSubarray__4___redArg___closed__0));
return v___f_72_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___lam__0(lean_object* v_xs_73_, lean_object* v_range_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_array_get_size(v_xs_73_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_range_74_, v___x_77_);
v___x_79_ = lean_nat_dec_le(v___x_78_, v___x_75_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = l_Array_toSubarray___redArg(v_xs_73_, v___x_78_, v___x_76_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; 
lean_dec(v___x_78_);
v___x_81_ = l_Array_toSubarray___redArg(v_xs_73_, v___x_75_, v___x_76_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___lam__0___boxed(lean_object* v_xs_82_, lean_object* v_range_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_instSliceableArrayNatSubarray__5___redArg___lam__0(v_xs_82_, v_range_83_);
lean_dec(v_range_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg(){
_start:
{
lean_object* v___f_87_; 
v___f_87_ = ((lean_object*)(l_instSliceableArrayNatSubarray__5___redArg___closed__0));
return v___f_87_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___boxed(lean_object* v___dummy_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_instSliceableArrayNatSubarray__5___redArg();
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object* v_00_u03b1_90_){
_start:
{
lean_object* v___f_91_; 
v___f_91_ = ((lean_object*)(l_instSliceableArrayNatSubarray__5___redArg___closed__0));
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___lam__0(lean_object* v_xs_92_, lean_object* v_range_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_add(v_range_93_, v___x_95_);
v___x_97_ = l_Array_toSubarray___redArg(v_xs_92_, v___x_94_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___lam__0___boxed(lean_object* v_xs_98_, lean_object* v_range_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_instSliceableArrayNatSubarray__6___redArg___lam__0(v_xs_98_, v_range_99_);
lean_dec(v_range_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg(){
_start:
{
lean_object* v___f_103_; 
v___f_103_ = ((lean_object*)(l_instSliceableArrayNatSubarray__6___redArg___closed__0));
return v___f_103_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___boxed(lean_object* v___dummy_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_instSliceableArrayNatSubarray__6___redArg();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object* v_00_u03b1_106_){
_start:
{
lean_object* v___f_107_; 
v___f_107_ = ((lean_object*)(l_instSliceableArrayNatSubarray__6___redArg___closed__0));
return v___f_107_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg___lam__0(lean_object* v_xs_108_, lean_object* v_range_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = l_Array_toSubarray___redArg(v_xs_108_, v___x_110_, v_range_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg(){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = ((lean_object*)(l_instSliceableArrayNatSubarray__7___redArg___closed__0));
return v___f_114_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg___boxed(lean_object* v___dummy_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_instSliceableArrayNatSubarray__7___redArg();
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object* v_00_u03b1_117_){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = ((lean_object*)(l_instSliceableArrayNatSubarray__7___redArg___closed__0));
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg___lam__0(lean_object* v_xs_119_, lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_array_get_size(v_xs_119_);
v___x_123_ = l_Array_toSubarray___redArg(v_xs_119_, v___x_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg(){
_start:
{
lean_object* v___f_126_; 
v___f_126_ = ((lean_object*)(l_instSliceableArrayNatSubarray__8___redArg___closed__0));
return v___f_126_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg___boxed(lean_object* v___dummy_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_instSliceableArrayNatSubarray__8___redArg();
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object* v_00_u03b1_129_){
_start:
{
lean_object* v___f_130_; 
v___f_130_ = ((lean_object*)(l_instSliceableArrayNatSubarray__8___redArg___closed__0));
return v___f_130_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___lam__0(lean_object* v_xs_131_, lean_object* v_range_132_){
_start:
{
lean_object* v_array_133_; lean_object* v_start_134_; lean_object* v_stop_135_; lean_object* v_lower_137_; lean_object* v_upper_138_; lean_object* v_lower_142_; lean_object* v_upper_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___y_147_; uint8_t v___x_151_; 
v_array_133_ = lean_ctor_get(v_xs_131_, 0);
lean_inc_ref(v_array_133_);
v_start_134_ = lean_ctor_get(v_xs_131_, 1);
lean_inc(v_start_134_);
v_stop_135_ = lean_ctor_get(v_xs_131_, 2);
lean_inc(v_stop_135_);
lean_dec_ref(v_xs_131_);
v_lower_142_ = lean_ctor_get(v_range_132_, 0);
v_upper_143_ = lean_ctor_get(v_range_132_, 1);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_nat_sub(v_stop_135_, v_start_134_);
lean_dec(v_stop_135_);
v___x_151_ = lean_nat_dec_le(v_lower_142_, v___x_144_);
if (v___x_151_ == 0)
{
v___y_147_ = v_lower_142_;
goto v___jp_146_;
}
else
{
v___y_147_ = v___x_144_;
goto v___jp_146_;
}
v___jp_136_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_nat_add(v_lower_137_, v_start_134_);
v___x_140_ = lean_nat_add(v_upper_138_, v_start_134_);
lean_dec(v_start_134_);
lean_dec(v_upper_138_);
v___x_141_ = l_Array_toSubarray___redArg(v_array_133_, v___x_139_, v___x_140_);
return v___x_141_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_upper_143_, v___x_148_);
v___x_150_ = lean_nat_dec_le(v___x_149_, v___x_145_);
if (v___x_150_ == 0)
{
lean_dec(v___x_149_);
v_lower_137_ = v___y_147_;
v_upper_138_ = v___x_145_;
goto v___jp_136_;
}
else
{
lean_dec(v___x_145_);
v_lower_137_ = v___y_147_;
v_upper_138_ = v___x_149_;
goto v___jp_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___lam__0___boxed(lean_object* v_xs_152_, lean_object* v_range_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_instSliceableSubarrayNat___redArg___lam__0(v_xs_152_, v_range_153_);
lean_dec_ref(v_range_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg(){
_start:
{
lean_object* v___f_157_; 
v___f_157_ = ((lean_object*)(l_instSliceableSubarrayNat___redArg___closed__0));
return v___f_157_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___boxed(lean_object* v___dummy_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_instSliceableSubarrayNat___redArg();
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat(lean_object* v_00_u03b1_160_){
_start:
{
lean_object* v___f_161_; 
v___f_161_ = ((lean_object*)(l_instSliceableSubarrayNat___redArg___closed__0));
return v___f_161_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg___lam__0(lean_object* v_xs_162_, lean_object* v_range_163_){
_start:
{
lean_object* v_array_164_; lean_object* v_start_165_; lean_object* v_stop_166_; lean_object* v_lower_168_; lean_object* v_upper_169_; lean_object* v_lower_173_; lean_object* v_upper_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___y_178_; uint8_t v___x_180_; 
v_array_164_ = lean_ctor_get(v_xs_162_, 0);
lean_inc_ref(v_array_164_);
v_start_165_ = lean_ctor_get(v_xs_162_, 1);
lean_inc(v_start_165_);
v_stop_166_ = lean_ctor_get(v_xs_162_, 2);
lean_inc(v_stop_166_);
lean_dec_ref(v_xs_162_);
v_lower_173_ = lean_ctor_get(v_range_163_, 0);
lean_inc(v_lower_173_);
v_upper_174_ = lean_ctor_get(v_range_163_, 1);
lean_inc(v_upper_174_);
lean_dec_ref(v_range_163_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_nat_sub(v_stop_166_, v_start_165_);
lean_dec(v_stop_166_);
v___x_180_ = lean_nat_dec_le(v_lower_173_, v___x_175_);
if (v___x_180_ == 0)
{
v___y_178_ = v_lower_173_;
goto v___jp_177_;
}
else
{
lean_dec(v_lower_173_);
v___y_178_ = v___x_175_;
goto v___jp_177_;
}
v___jp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_nat_add(v_lower_168_, v_start_165_);
lean_dec(v_lower_168_);
v___x_171_ = lean_nat_add(v_upper_169_, v_start_165_);
lean_dec(v_start_165_);
lean_dec(v_upper_169_);
v___x_172_ = l_Array_toSubarray___redArg(v_array_164_, v___x_170_, v___x_171_);
return v___x_172_;
}
v___jp_177_:
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_le(v_upper_174_, v___x_176_);
if (v___x_179_ == 0)
{
lean_dec(v_upper_174_);
v_lower_168_ = v___y_178_;
v_upper_169_ = v___x_176_;
goto v___jp_167_;
}
else
{
lean_dec(v___x_176_);
v_lower_168_ = v___y_178_;
v_upper_169_ = v_upper_174_;
goto v___jp_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg(){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = ((lean_object*)(l_instSliceableSubarrayNat__1___redArg___closed__0));
return v___f_183_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg___boxed(lean_object* v___dummy_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_instSliceableSubarrayNat__1___redArg();
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1(lean_object* v_00_u03b1_186_){
_start:
{
lean_object* v___f_187_; 
v___f_187_ = ((lean_object*)(l_instSliceableSubarrayNat__1___redArg___closed__0));
return v___f_187_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___lam__0(lean_object* v_xs_188_, lean_object* v_range_189_){
_start:
{
lean_object* v_array_190_; lean_object* v_start_191_; lean_object* v_stop_192_; lean_object* v_lower_194_; lean_object* v_upper_195_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_array_190_ = lean_ctor_get(v_xs_188_, 0);
lean_inc_ref(v_array_190_);
v_start_191_ = lean_ctor_get(v_xs_188_, 1);
lean_inc(v_start_191_);
v_stop_192_ = lean_ctor_get(v_xs_188_, 2);
lean_inc(v_stop_192_);
lean_dec_ref(v_xs_188_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_nat_sub(v_stop_192_, v_start_191_);
lean_dec(v_stop_192_);
v___x_201_ = lean_nat_dec_le(v_range_189_, v___x_199_);
if (v___x_201_ == 0)
{
v_lower_194_ = v_range_189_;
v_upper_195_ = v___x_200_;
goto v___jp_193_;
}
else
{
v_lower_194_ = v___x_199_;
v_upper_195_ = v___x_200_;
goto v___jp_193_;
}
v___jp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_nat_add(v_lower_194_, v_start_191_);
v___x_197_ = lean_nat_add(v_upper_195_, v_start_191_);
lean_dec(v_start_191_);
lean_dec(v_upper_195_);
v___x_198_ = l_Array_toSubarray___redArg(v_array_190_, v___x_196_, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___lam__0___boxed(lean_object* v_xs_202_, lean_object* v_range_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_instSliceableSubarrayNat__2___redArg___lam__0(v_xs_202_, v_range_203_);
lean_dec(v_range_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg(){
_start:
{
lean_object* v___f_207_; 
v___f_207_ = ((lean_object*)(l_instSliceableSubarrayNat__2___redArg___closed__0));
return v___f_207_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___boxed(lean_object* v___dummy_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_instSliceableSubarrayNat__2___redArg();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2(lean_object* v_00_u03b1_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = ((lean_object*)(l_instSliceableSubarrayNat__2___redArg___closed__0));
return v___f_211_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___lam__0(lean_object* v_xs_212_, lean_object* v_range_213_){
_start:
{
lean_object* v_array_214_; lean_object* v_start_215_; lean_object* v_stop_216_; lean_object* v_lower_218_; lean_object* v_upper_219_; lean_object* v_lower_223_; lean_object* v_upper_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___y_229_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_array_214_ = lean_ctor_get(v_xs_212_, 0);
lean_inc_ref(v_array_214_);
v_start_215_ = lean_ctor_get(v_xs_212_, 1);
lean_inc(v_start_215_);
v_stop_216_ = lean_ctor_get(v_xs_212_, 2);
lean_inc(v_stop_216_);
lean_dec_ref(v_xs_212_);
v_lower_223_ = lean_ctor_get(v_range_213_, 0);
v_upper_224_ = lean_ctor_get(v_range_213_, 1);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_nat_sub(v_stop_216_, v_start_215_);
lean_dec(v_stop_216_);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_lower_223_, v___x_227_);
v___x_233_ = lean_nat_dec_le(v___x_232_, v___x_225_);
if (v___x_233_ == 0)
{
v___y_229_ = v___x_232_;
goto v___jp_228_;
}
else
{
lean_dec(v___x_232_);
v___y_229_ = v___x_225_;
goto v___jp_228_;
}
v___jp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_nat_add(v_lower_218_, v_start_215_);
lean_dec(v_lower_218_);
v___x_221_ = lean_nat_add(v_upper_219_, v_start_215_);
lean_dec(v_start_215_);
lean_dec(v_upper_219_);
v___x_222_ = l_Array_toSubarray___redArg(v_array_214_, v___x_220_, v___x_221_);
return v___x_222_;
}
v___jp_228_:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_nat_add(v_upper_224_, v___x_227_);
v___x_231_ = lean_nat_dec_le(v___x_230_, v___x_226_);
if (v___x_231_ == 0)
{
lean_dec(v___x_230_);
v_lower_218_ = v___y_229_;
v_upper_219_ = v___x_226_;
goto v___jp_217_;
}
else
{
lean_dec(v___x_226_);
v_lower_218_ = v___y_229_;
v_upper_219_ = v___x_230_;
goto v___jp_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___lam__0___boxed(lean_object* v_xs_234_, lean_object* v_range_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_instSliceableSubarrayNat__3___redArg___lam__0(v_xs_234_, v_range_235_);
lean_dec_ref(v_range_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg(){
_start:
{
lean_object* v___f_239_; 
v___f_239_ = ((lean_object*)(l_instSliceableSubarrayNat__3___redArg___closed__0));
return v___f_239_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___boxed(lean_object* v___dummy_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_instSliceableSubarrayNat__3___redArg();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3(lean_object* v_00_u03b1_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = ((lean_object*)(l_instSliceableSubarrayNat__3___redArg___closed__0));
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg___lam__0(lean_object* v_xs_244_, lean_object* v_range_245_){
_start:
{
lean_object* v_array_246_; lean_object* v_start_247_; lean_object* v_stop_248_; lean_object* v_lower_250_; lean_object* v_upper_251_; lean_object* v_lower_255_; lean_object* v_upper_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___y_260_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_array_246_ = lean_ctor_get(v_xs_244_, 0);
lean_inc_ref(v_array_246_);
v_start_247_ = lean_ctor_get(v_xs_244_, 1);
lean_inc(v_start_247_);
v_stop_248_ = lean_ctor_get(v_xs_244_, 2);
lean_inc(v_stop_248_);
lean_dec_ref(v_xs_244_);
v_lower_255_ = lean_ctor_get(v_range_245_, 0);
lean_inc(v_lower_255_);
v_upper_256_ = lean_ctor_get(v_range_245_, 1);
lean_inc(v_upper_256_);
lean_dec_ref(v_range_245_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_nat_sub(v_stop_248_, v_start_247_);
lean_dec(v_stop_248_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_lower_255_, v___x_262_);
lean_dec(v_lower_255_);
v___x_264_ = lean_nat_dec_le(v___x_263_, v___x_257_);
if (v___x_264_ == 0)
{
v___y_260_ = v___x_263_;
goto v___jp_259_;
}
else
{
lean_dec(v___x_263_);
v___y_260_ = v___x_257_;
goto v___jp_259_;
}
v___jp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_nat_add(v_lower_250_, v_start_247_);
lean_dec(v_lower_250_);
v___x_253_ = lean_nat_add(v_upper_251_, v_start_247_);
lean_dec(v_start_247_);
lean_dec(v_upper_251_);
v___x_254_ = l_Array_toSubarray___redArg(v_array_246_, v___x_252_, v___x_253_);
return v___x_254_;
}
v___jp_259_:
{
uint8_t v___x_261_; 
v___x_261_ = lean_nat_dec_le(v_upper_256_, v___x_258_);
if (v___x_261_ == 0)
{
lean_dec(v_upper_256_);
v_lower_250_ = v___y_260_;
v_upper_251_ = v___x_258_;
goto v___jp_249_;
}
else
{
lean_dec(v___x_258_);
v_lower_250_ = v___y_260_;
v_upper_251_ = v_upper_256_;
goto v___jp_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg(){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = ((lean_object*)(l_instSliceableSubarrayNat__4___redArg___closed__0));
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg___boxed(lean_object* v___dummy_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_instSliceableSubarrayNat__4___redArg();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4(lean_object* v_00_u03b1_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = ((lean_object*)(l_instSliceableSubarrayNat__4___redArg___closed__0));
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___lam__0(lean_object* v_xs_272_, lean_object* v_range_273_){
_start:
{
lean_object* v_array_274_; lean_object* v_start_275_; lean_object* v_stop_276_; lean_object* v_lower_278_; lean_object* v_upper_279_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_array_274_ = lean_ctor_get(v_xs_272_, 0);
lean_inc_ref(v_array_274_);
v_start_275_ = lean_ctor_get(v_xs_272_, 1);
lean_inc(v_start_275_);
v_stop_276_ = lean_ctor_get(v_xs_272_, 2);
lean_inc(v_stop_276_);
lean_dec_ref(v_xs_272_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_nat_sub(v_stop_276_, v_start_275_);
lean_dec(v_stop_276_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_range_273_, v___x_285_);
v___x_287_ = lean_nat_dec_le(v___x_286_, v___x_283_);
if (v___x_287_ == 0)
{
v_lower_278_ = v___x_286_;
v_upper_279_ = v___x_284_;
goto v___jp_277_;
}
else
{
lean_dec(v___x_286_);
v_lower_278_ = v___x_283_;
v_upper_279_ = v___x_284_;
goto v___jp_277_;
}
v___jp_277_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_nat_add(v_lower_278_, v_start_275_);
lean_dec(v_lower_278_);
v___x_281_ = lean_nat_add(v_upper_279_, v_start_275_);
lean_dec(v_start_275_);
lean_dec(v_upper_279_);
v___x_282_ = l_Array_toSubarray___redArg(v_array_274_, v___x_280_, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___lam__0___boxed(lean_object* v_xs_288_, lean_object* v_range_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_instSliceableSubarrayNat__5___redArg___lam__0(v_xs_288_, v_range_289_);
lean_dec(v_range_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg(){
_start:
{
lean_object* v___f_293_; 
v___f_293_ = ((lean_object*)(l_instSliceableSubarrayNat__5___redArg___closed__0));
return v___f_293_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___boxed(lean_object* v___dummy_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_instSliceableSubarrayNat__5___redArg();
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5(lean_object* v_00_u03b1_296_){
_start:
{
lean_object* v___f_297_; 
v___f_297_ = ((lean_object*)(l_instSliceableSubarrayNat__5___redArg___closed__0));
return v___f_297_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___lam__0(lean_object* v_xs_298_, lean_object* v_range_299_){
_start:
{
lean_object* v_array_300_; lean_object* v_start_301_; lean_object* v_stop_302_; lean_object* v_lower_304_; lean_object* v_upper_305_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_array_300_ = lean_ctor_get(v_xs_298_, 0);
lean_inc_ref(v_array_300_);
v_start_301_ = lean_ctor_get(v_xs_298_, 1);
lean_inc(v_start_301_);
v_stop_302_ = lean_ctor_get(v_xs_298_, 2);
lean_inc(v_stop_302_);
lean_dec_ref(v_xs_298_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_nat_sub(v_stop_302_, v_start_301_);
lean_dec(v_stop_302_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_add(v_range_299_, v___x_311_);
v___x_313_ = lean_nat_dec_le(v___x_312_, v___x_310_);
if (v___x_313_ == 0)
{
lean_dec(v___x_312_);
v_lower_304_ = v___x_309_;
v_upper_305_ = v___x_310_;
goto v___jp_303_;
}
else
{
lean_dec(v___x_310_);
v_lower_304_ = v___x_309_;
v_upper_305_ = v___x_312_;
goto v___jp_303_;
}
v___jp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_nat_add(v_lower_304_, v_start_301_);
v___x_307_ = lean_nat_add(v_upper_305_, v_start_301_);
lean_dec(v_start_301_);
lean_dec(v_upper_305_);
v___x_308_ = l_Array_toSubarray___redArg(v_array_300_, v___x_306_, v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___lam__0___boxed(lean_object* v_xs_314_, lean_object* v_range_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_instSliceableSubarrayNat__6___redArg___lam__0(v_xs_314_, v_range_315_);
lean_dec(v_range_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg(){
_start:
{
lean_object* v___f_319_; 
v___f_319_ = ((lean_object*)(l_instSliceableSubarrayNat__6___redArg___closed__0));
return v___f_319_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___boxed(lean_object* v___dummy_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_instSliceableSubarrayNat__6___redArg();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6(lean_object* v_00_u03b1_322_){
_start:
{
lean_object* v___f_323_; 
v___f_323_ = ((lean_object*)(l_instSliceableSubarrayNat__6___redArg___closed__0));
return v___f_323_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg___lam__0(lean_object* v_xs_324_, lean_object* v_range_325_){
_start:
{
lean_object* v_array_326_; lean_object* v_start_327_; lean_object* v_stop_328_; lean_object* v_lower_330_; lean_object* v_upper_331_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_array_326_ = lean_ctor_get(v_xs_324_, 0);
lean_inc_ref(v_array_326_);
v_start_327_ = lean_ctor_get(v_xs_324_, 1);
lean_inc(v_start_327_);
v_stop_328_ = lean_ctor_get(v_xs_324_, 2);
lean_inc(v_stop_328_);
lean_dec_ref(v_xs_324_);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_nat_sub(v_stop_328_, v_start_327_);
lean_dec(v_stop_328_);
v___x_337_ = lean_nat_dec_le(v_range_325_, v___x_336_);
if (v___x_337_ == 0)
{
lean_dec(v_range_325_);
v_lower_330_ = v___x_335_;
v_upper_331_ = v___x_336_;
goto v___jp_329_;
}
else
{
lean_dec(v___x_336_);
v_lower_330_ = v___x_335_;
v_upper_331_ = v_range_325_;
goto v___jp_329_;
}
v___jp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_nat_add(v_lower_330_, v_start_327_);
v___x_333_ = lean_nat_add(v_upper_331_, v_start_327_);
lean_dec(v_start_327_);
lean_dec(v_upper_331_);
v___x_334_ = l_Array_toSubarray___redArg(v_array_326_, v___x_332_, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg(){
_start:
{
lean_object* v___f_340_; 
v___f_340_ = ((lean_object*)(l_instSliceableSubarrayNat__7___redArg___closed__0));
return v___f_340_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg___boxed(lean_object* v___dummy_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_instSliceableSubarrayNat__7___redArg();
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7(lean_object* v_00_u03b1_343_){
_start:
{
lean_object* v___f_344_; 
v___f_344_ = ((lean_object*)(l_instSliceableSubarrayNat__7___redArg___closed__0));
return v___f_344_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___lam__0(lean_object* v_xs_345_, lean_object* v_x_346_){
_start:
{
lean_inc_ref(v_xs_345_);
return v_xs_345_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___lam__0___boxed(lean_object* v_xs_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_instSliceableSubarrayNat__8___redArg___lam__0(v_xs_347_, v_x_348_);
lean_dec_ref(v_xs_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg(){
_start:
{
lean_object* v___f_352_; 
v___f_352_ = ((lean_object*)(l_instSliceableSubarrayNat__8___redArg___closed__0));
return v___f_352_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___boxed(lean_object* v___dummy_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_instSliceableSubarrayNat__8___redArg();
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8(lean_object* v_00_u03b1_355_){
_start:
{
lean_object* v___f_356_; 
v___f_356_ = ((lean_object*)(l_instSliceableSubarrayNat__8___redArg___closed__0));
return v___f_356_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
