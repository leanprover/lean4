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
lean_object* l_instSliceableArrayNatSubarray___redArg(){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = ((lean_object*)(l_instSliceableArrayNatSubarray___redArg___closed__0));
return v___f_10_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_11_;
v_res_11_ = l_instSliceableArrayNatSubarray___redArg();
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_instSliceableArrayNatSubarray___redArg();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object* v_00_u03b1_14_){
_start:
{
lean_object* v___f_15_; 
v___f_15_ = ((lean_object*)(l_instSliceableArrayNatSubarray___redArg___closed__0));
return v___f_15_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg___lam__0(lean_object* v_xs_16_, lean_object* v_range_17_){
_start:
{
lean_object* v_lower_18_; lean_object* v_upper_19_; lean_object* v___x_20_; 
v_lower_18_ = lean_ctor_get(v_range_17_, 0);
lean_inc(v_lower_18_);
v_upper_19_ = lean_ctor_get(v_range_17_, 1);
lean_inc(v_upper_19_);
lean_dec_ref(v_range_17_);
v___x_20_ = l_Array_toSubarray___redArg(v_xs_16_, v_lower_18_, v_upper_19_);
return v___x_20_;
}
}
lean_object* l_instSliceableArrayNatSubarray__1___redArg(){
_start:
{
lean_object* v___f_23_; 
v___f_23_ = ((lean_object*)(l_instSliceableArrayNatSubarray__1___redArg___closed__0));
return v___f_23_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_24_;
v_res_24_ = l_instSliceableArrayNatSubarray__1___redArg();
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___redArg___boxed(lean_object* v___dummy_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_instSliceableArrayNatSubarray__1___redArg();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object* v_00_u03b1_27_){
_start:
{
lean_object* v___f_28_; 
v___f_28_ = ((lean_object*)(l_instSliceableArrayNatSubarray__1___redArg___closed__0));
return v___f_28_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg___lam__0(lean_object* v_xs_29_, lean_object* v_range_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_array_get_size(v_xs_29_);
v___x_33_ = lean_nat_dec_le(v_range_30_, v___x_31_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = l_Array_toSubarray___redArg(v_xs_29_, v_range_30_, v___x_32_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
lean_dec(v_range_30_);
v___x_35_ = l_Array_toSubarray___redArg(v_xs_29_, v___x_31_, v___x_32_);
return v___x_35_;
}
}
}
lean_object* l_instSliceableArrayNatSubarray__2___redArg(){
_start:
{
lean_object* v___f_38_; 
v___f_38_ = ((lean_object*)(l_instSliceableArrayNatSubarray__2___redArg___closed__0));
return v___f_38_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_39_;
v_res_39_ = l_instSliceableArrayNatSubarray__2___redArg();
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___redArg___boxed(lean_object* v___dummy_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_instSliceableArrayNatSubarray__2___redArg();
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object* v_00_u03b1_42_){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = ((lean_object*)(l_instSliceableArrayNatSubarray__2___redArg___closed__0));
return v___f_43_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___lam__0(lean_object* v_xs_44_, lean_object* v_range_45_){
_start:
{
lean_object* v_lower_46_; lean_object* v_upper_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_lower_46_ = lean_ctor_get(v_range_45_, 0);
v_upper_47_ = lean_ctor_get(v_range_45_, 1);
v___x_48_ = lean_unsigned_to_nat(1u);
v___x_49_ = lean_nat_add(v_lower_46_, v___x_48_);
v___x_50_ = lean_nat_add(v_upper_47_, v___x_48_);
v___x_51_ = l_Array_toSubarray___redArg(v_xs_44_, v___x_49_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___lam__0___boxed(lean_object* v_xs_52_, lean_object* v_range_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_instSliceableArrayNatSubarray__3___redArg___lam__0(v_xs_52_, v_range_53_);
lean_dec_ref(v_range_53_);
return v_res_54_;
}
}
lean_object* l_instSliceableArrayNatSubarray__3___redArg(){
_start:
{
lean_object* v___f_57_; 
v___f_57_ = ((lean_object*)(l_instSliceableArrayNatSubarray__3___redArg___closed__0));
return v___f_57_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l_instSliceableArrayNatSubarray__3___redArg();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___redArg___boxed(lean_object* v___dummy_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_instSliceableArrayNatSubarray__3___redArg();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object* v_00_u03b1_61_){
_start:
{
lean_object* v___f_62_; 
v___f_62_ = ((lean_object*)(l_instSliceableArrayNatSubarray__3___redArg___closed__0));
return v___f_62_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg___lam__0(lean_object* v_xs_63_, lean_object* v_range_64_){
_start:
{
lean_object* v_lower_65_; lean_object* v_upper_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_lower_65_ = lean_ctor_get(v_range_64_, 0);
lean_inc(v_lower_65_);
v_upper_66_ = lean_ctor_get(v_range_64_, 1);
lean_inc(v_upper_66_);
lean_dec_ref(v_range_64_);
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_add(v_lower_65_, v___x_67_);
lean_dec(v_lower_65_);
v___x_69_ = l_Array_toSubarray___redArg(v_xs_63_, v___x_68_, v_upper_66_);
return v___x_69_;
}
}
lean_object* l_instSliceableArrayNatSubarray__4___redArg(){
_start:
{
lean_object* v___f_72_; 
v___f_72_ = ((lean_object*)(l_instSliceableArrayNatSubarray__4___redArg___closed__0));
return v___f_72_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_73_;
v_res_73_ = l_instSliceableArrayNatSubarray__4___redArg();
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___redArg___boxed(lean_object* v___dummy_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_instSliceableArrayNatSubarray__4___redArg();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object* v_00_u03b1_76_){
_start:
{
lean_object* v___f_77_; 
v___f_77_ = ((lean_object*)(l_instSliceableArrayNatSubarray__4___redArg___closed__0));
return v___f_77_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___lam__0(lean_object* v_xs_78_, lean_object* v_range_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_array_get_size(v_xs_78_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_range_79_, v___x_82_);
v___x_84_ = lean_nat_dec_le(v___x_83_, v___x_80_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = l_Array_toSubarray___redArg(v_xs_78_, v___x_83_, v___x_81_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
lean_dec(v___x_83_);
v___x_86_ = l_Array_toSubarray___redArg(v_xs_78_, v___x_80_, v___x_81_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___lam__0___boxed(lean_object* v_xs_87_, lean_object* v_range_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_instSliceableArrayNatSubarray__5___redArg___lam__0(v_xs_87_, v_range_88_);
lean_dec(v_range_88_);
return v_res_89_;
}
}
lean_object* l_instSliceableArrayNatSubarray__5___redArg(){
_start:
{
lean_object* v___f_92_; 
v___f_92_ = ((lean_object*)(l_instSliceableArrayNatSubarray__5___redArg___closed__0));
return v___f_92_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_93_;
v_res_93_ = l_instSliceableArrayNatSubarray__5___redArg();
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___redArg___boxed(lean_object* v___dummy_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_instSliceableArrayNatSubarray__5___redArg();
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object* v_00_u03b1_96_){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = ((lean_object*)(l_instSliceableArrayNatSubarray__5___redArg___closed__0));
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___lam__0(lean_object* v_xs_98_, lean_object* v_range_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_range_99_, v___x_101_);
v___x_103_ = l_Array_toSubarray___redArg(v_xs_98_, v___x_100_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___lam__0___boxed(lean_object* v_xs_104_, lean_object* v_range_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_instSliceableArrayNatSubarray__6___redArg___lam__0(v_xs_104_, v_range_105_);
lean_dec(v_range_105_);
return v_res_106_;
}
}
lean_object* l_instSliceableArrayNatSubarray__6___redArg(){
_start:
{
lean_object* v___f_109_; 
v___f_109_ = ((lean_object*)(l_instSliceableArrayNatSubarray__6___redArg___closed__0));
return v___f_109_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_110_;
v_res_110_ = l_instSliceableArrayNatSubarray__6___redArg();
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___redArg___boxed(lean_object* v___dummy_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_instSliceableArrayNatSubarray__6___redArg();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object* v_00_u03b1_113_){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = ((lean_object*)(l_instSliceableArrayNatSubarray__6___redArg___closed__0));
return v___f_114_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg___lam__0(lean_object* v_xs_115_, lean_object* v_range_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = l_Array_toSubarray___redArg(v_xs_115_, v___x_117_, v_range_116_);
return v___x_118_;
}
}
lean_object* l_instSliceableArrayNatSubarray__7___redArg(){
_start:
{
lean_object* v___f_121_; 
v___f_121_ = ((lean_object*)(l_instSliceableArrayNatSubarray__7___redArg___closed__0));
return v___f_121_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_122_;
v_res_122_ = l_instSliceableArrayNatSubarray__7___redArg();
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___redArg___boxed(lean_object* v___dummy_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_instSliceableArrayNatSubarray__7___redArg();
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object* v_00_u03b1_125_){
_start:
{
lean_object* v___f_126_; 
v___f_126_ = ((lean_object*)(l_instSliceableArrayNatSubarray__7___redArg___closed__0));
return v___f_126_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg___lam__0(lean_object* v_xs_127_, lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_array_get_size(v_xs_127_);
v___x_131_ = l_Array_toSubarray___redArg(v_xs_127_, v___x_129_, v___x_130_);
return v___x_131_;
}
}
lean_object* l_instSliceableArrayNatSubarray__8___redArg(){
_start:
{
lean_object* v___f_134_; 
v___f_134_ = ((lean_object*)(l_instSliceableArrayNatSubarray__8___redArg___closed__0));
return v___f_134_;
}
}
LEAN_EXPORT void l_instSliceableArrayNatSubarray__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_135_;
v_res_135_ = l_instSliceableArrayNatSubarray__8___redArg();
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___redArg___boxed(lean_object* v___dummy_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_instSliceableArrayNatSubarray__8___redArg();
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object* v_00_u03b1_138_){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = ((lean_object*)(l_instSliceableArrayNatSubarray__8___redArg___closed__0));
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___lam__0(lean_object* v_xs_140_, lean_object* v_range_141_){
_start:
{
lean_object* v_array_142_; lean_object* v_start_143_; lean_object* v_stop_144_; lean_object* v_lower_146_; lean_object* v_upper_147_; lean_object* v_lower_151_; lean_object* v_upper_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___y_156_; uint8_t v___x_160_; 
v_array_142_ = lean_ctor_get(v_xs_140_, 0);
lean_inc_ref(v_array_142_);
v_start_143_ = lean_ctor_get(v_xs_140_, 1);
lean_inc(v_start_143_);
v_stop_144_ = lean_ctor_get(v_xs_140_, 2);
lean_inc(v_stop_144_);
lean_dec_ref(v_xs_140_);
v_lower_151_ = lean_ctor_get(v_range_141_, 0);
v_upper_152_ = lean_ctor_get(v_range_141_, 1);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_nat_sub(v_stop_144_, v_start_143_);
lean_dec(v_stop_144_);
v___x_160_ = lean_nat_dec_le(v_lower_151_, v___x_153_);
if (v___x_160_ == 0)
{
v___y_156_ = v_lower_151_;
goto v___jp_155_;
}
else
{
v___y_156_ = v___x_153_;
goto v___jp_155_;
}
v___jp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_nat_add(v_lower_146_, v_start_143_);
v___x_149_ = lean_nat_add(v_upper_147_, v_start_143_);
lean_dec(v_start_143_);
lean_dec(v_upper_147_);
v___x_150_ = l_Array_toSubarray___redArg(v_array_142_, v___x_148_, v___x_149_);
return v___x_150_;
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_upper_152_, v___x_157_);
v___x_159_ = lean_nat_dec_le(v___x_158_, v___x_154_);
if (v___x_159_ == 0)
{
lean_dec(v___x_158_);
v_lower_146_ = v___y_156_;
v_upper_147_ = v___x_154_;
goto v___jp_145_;
}
else
{
lean_dec(v___x_154_);
v_lower_146_ = v___y_156_;
v_upper_147_ = v___x_158_;
goto v___jp_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___lam__0___boxed(lean_object* v_xs_161_, lean_object* v_range_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_instSliceableSubarrayNat___redArg___lam__0(v_xs_161_, v_range_162_);
lean_dec_ref(v_range_162_);
return v_res_163_;
}
}
lean_object* l_instSliceableSubarrayNat___redArg(){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = ((lean_object*)(l_instSliceableSubarrayNat___redArg___closed__0));
return v___f_166_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_167_;
v_res_167_ = l_instSliceableSubarrayNat___redArg();
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat___redArg___boxed(lean_object* v___dummy_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_instSliceableSubarrayNat___redArg();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat(lean_object* v_00_u03b1_170_){
_start:
{
lean_object* v___f_171_; 
v___f_171_ = ((lean_object*)(l_instSliceableSubarrayNat___redArg___closed__0));
return v___f_171_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg___lam__0(lean_object* v_xs_172_, lean_object* v_range_173_){
_start:
{
lean_object* v_array_174_; lean_object* v_start_175_; lean_object* v_stop_176_; lean_object* v_lower_178_; lean_object* v_upper_179_; lean_object* v_lower_183_; lean_object* v_upper_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___y_188_; uint8_t v___x_190_; 
v_array_174_ = lean_ctor_get(v_xs_172_, 0);
lean_inc_ref(v_array_174_);
v_start_175_ = lean_ctor_get(v_xs_172_, 1);
lean_inc(v_start_175_);
v_stop_176_ = lean_ctor_get(v_xs_172_, 2);
lean_inc(v_stop_176_);
lean_dec_ref(v_xs_172_);
v_lower_183_ = lean_ctor_get(v_range_173_, 0);
lean_inc(v_lower_183_);
v_upper_184_ = lean_ctor_get(v_range_173_, 1);
lean_inc(v_upper_184_);
lean_dec_ref(v_range_173_);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_nat_sub(v_stop_176_, v_start_175_);
lean_dec(v_stop_176_);
v___x_190_ = lean_nat_dec_le(v_lower_183_, v___x_185_);
if (v___x_190_ == 0)
{
v___y_188_ = v_lower_183_;
goto v___jp_187_;
}
else
{
lean_dec(v_lower_183_);
v___y_188_ = v___x_185_;
goto v___jp_187_;
}
v___jp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_nat_add(v_lower_178_, v_start_175_);
lean_dec(v_lower_178_);
v___x_181_ = lean_nat_add(v_upper_179_, v_start_175_);
lean_dec(v_start_175_);
lean_dec(v_upper_179_);
v___x_182_ = l_Array_toSubarray___redArg(v_array_174_, v___x_180_, v___x_181_);
return v___x_182_;
}
v___jp_187_:
{
uint8_t v___x_189_; 
v___x_189_ = lean_nat_dec_le(v_upper_184_, v___x_186_);
if (v___x_189_ == 0)
{
lean_dec(v_upper_184_);
v_lower_178_ = v___y_188_;
v_upper_179_ = v___x_186_;
goto v___jp_177_;
}
else
{
lean_dec(v___x_186_);
v_lower_178_ = v___y_188_;
v_upper_179_ = v_upper_184_;
goto v___jp_177_;
}
}
}
}
lean_object* l_instSliceableSubarrayNat__1___redArg(){
_start:
{
lean_object* v___f_193_; 
v___f_193_ = ((lean_object*)(l_instSliceableSubarrayNat__1___redArg___closed__0));
return v___f_193_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_194_;
v_res_194_ = l_instSliceableSubarrayNat__1___redArg();
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1___redArg___boxed(lean_object* v___dummy_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_instSliceableSubarrayNat__1___redArg();
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__1(lean_object* v_00_u03b1_197_){
_start:
{
lean_object* v___f_198_; 
v___f_198_ = ((lean_object*)(l_instSliceableSubarrayNat__1___redArg___closed__0));
return v___f_198_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___lam__0(lean_object* v_xs_199_, lean_object* v_range_200_){
_start:
{
lean_object* v_array_201_; lean_object* v_start_202_; lean_object* v_stop_203_; lean_object* v_lower_205_; lean_object* v_upper_206_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_array_201_ = lean_ctor_get(v_xs_199_, 0);
lean_inc_ref(v_array_201_);
v_start_202_ = lean_ctor_get(v_xs_199_, 1);
lean_inc(v_start_202_);
v_stop_203_ = lean_ctor_get(v_xs_199_, 2);
lean_inc(v_stop_203_);
lean_dec_ref(v_xs_199_);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_nat_sub(v_stop_203_, v_start_202_);
lean_dec(v_stop_203_);
v___x_212_ = lean_nat_dec_le(v_range_200_, v___x_210_);
if (v___x_212_ == 0)
{
v_lower_205_ = v_range_200_;
v_upper_206_ = v___x_211_;
goto v___jp_204_;
}
else
{
v_lower_205_ = v___x_210_;
v_upper_206_ = v___x_211_;
goto v___jp_204_;
}
v___jp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_nat_add(v_lower_205_, v_start_202_);
v___x_208_ = lean_nat_add(v_upper_206_, v_start_202_);
lean_dec(v_start_202_);
lean_dec(v_upper_206_);
v___x_209_ = l_Array_toSubarray___redArg(v_array_201_, v___x_207_, v___x_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___lam__0___boxed(lean_object* v_xs_213_, lean_object* v_range_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_instSliceableSubarrayNat__2___redArg___lam__0(v_xs_213_, v_range_214_);
lean_dec(v_range_214_);
return v_res_215_;
}
}
lean_object* l_instSliceableSubarrayNat__2___redArg(){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = ((lean_object*)(l_instSliceableSubarrayNat__2___redArg___closed__0));
return v___f_218_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_219_;
v_res_219_ = l_instSliceableSubarrayNat__2___redArg();
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2___redArg___boxed(lean_object* v___dummy_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_instSliceableSubarrayNat__2___redArg();
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__2(lean_object* v_00_u03b1_222_){
_start:
{
lean_object* v___f_223_; 
v___f_223_ = ((lean_object*)(l_instSliceableSubarrayNat__2___redArg___closed__0));
return v___f_223_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___lam__0(lean_object* v_xs_224_, lean_object* v_range_225_){
_start:
{
lean_object* v_array_226_; lean_object* v_start_227_; lean_object* v_stop_228_; lean_object* v_lower_230_; lean_object* v_upper_231_; lean_object* v_lower_235_; lean_object* v_upper_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___y_241_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_array_226_ = lean_ctor_get(v_xs_224_, 0);
lean_inc_ref(v_array_226_);
v_start_227_ = lean_ctor_get(v_xs_224_, 1);
lean_inc(v_start_227_);
v_stop_228_ = lean_ctor_get(v_xs_224_, 2);
lean_inc(v_stop_228_);
lean_dec_ref(v_xs_224_);
v_lower_235_ = lean_ctor_get(v_range_225_, 0);
v_upper_236_ = lean_ctor_get(v_range_225_, 1);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_nat_sub(v_stop_228_, v_start_227_);
lean_dec(v_stop_228_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_lower_235_, v___x_239_);
v___x_245_ = lean_nat_dec_le(v___x_244_, v___x_237_);
if (v___x_245_ == 0)
{
v___y_241_ = v___x_244_;
goto v___jp_240_;
}
else
{
lean_dec(v___x_244_);
v___y_241_ = v___x_237_;
goto v___jp_240_;
}
v___jp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_nat_add(v_lower_230_, v_start_227_);
lean_dec(v_lower_230_);
v___x_233_ = lean_nat_add(v_upper_231_, v_start_227_);
lean_dec(v_start_227_);
lean_dec(v_upper_231_);
v___x_234_ = l_Array_toSubarray___redArg(v_array_226_, v___x_232_, v___x_233_);
return v___x_234_;
}
v___jp_240_:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_nat_add(v_upper_236_, v___x_239_);
v___x_243_ = lean_nat_dec_le(v___x_242_, v___x_238_);
if (v___x_243_ == 0)
{
lean_dec(v___x_242_);
v_lower_230_ = v___y_241_;
v_upper_231_ = v___x_238_;
goto v___jp_229_;
}
else
{
lean_dec(v___x_238_);
v_lower_230_ = v___y_241_;
v_upper_231_ = v___x_242_;
goto v___jp_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___lam__0___boxed(lean_object* v_xs_246_, lean_object* v_range_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_instSliceableSubarrayNat__3___redArg___lam__0(v_xs_246_, v_range_247_);
lean_dec_ref(v_range_247_);
return v_res_248_;
}
}
lean_object* l_instSliceableSubarrayNat__3___redArg(){
_start:
{
lean_object* v___f_251_; 
v___f_251_ = ((lean_object*)(l_instSliceableSubarrayNat__3___redArg___closed__0));
return v___f_251_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_252_;
v_res_252_ = l_instSliceableSubarrayNat__3___redArg();
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3___redArg___boxed(lean_object* v___dummy_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_instSliceableSubarrayNat__3___redArg();
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__3(lean_object* v_00_u03b1_255_){
_start:
{
lean_object* v___f_256_; 
v___f_256_ = ((lean_object*)(l_instSliceableSubarrayNat__3___redArg___closed__0));
return v___f_256_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg___lam__0(lean_object* v_xs_257_, lean_object* v_range_258_){
_start:
{
lean_object* v_array_259_; lean_object* v_start_260_; lean_object* v_stop_261_; lean_object* v_lower_263_; lean_object* v_upper_264_; lean_object* v_lower_268_; lean_object* v_upper_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___y_273_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_array_259_ = lean_ctor_get(v_xs_257_, 0);
lean_inc_ref(v_array_259_);
v_start_260_ = lean_ctor_get(v_xs_257_, 1);
lean_inc(v_start_260_);
v_stop_261_ = lean_ctor_get(v_xs_257_, 2);
lean_inc(v_stop_261_);
lean_dec_ref(v_xs_257_);
v_lower_268_ = lean_ctor_get(v_range_258_, 0);
lean_inc(v_lower_268_);
v_upper_269_ = lean_ctor_get(v_range_258_, 1);
lean_inc(v_upper_269_);
lean_dec_ref(v_range_258_);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_nat_sub(v_stop_261_, v_start_260_);
lean_dec(v_stop_261_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_lower_268_, v___x_275_);
lean_dec(v_lower_268_);
v___x_277_ = lean_nat_dec_le(v___x_276_, v___x_270_);
if (v___x_277_ == 0)
{
v___y_273_ = v___x_276_;
goto v___jp_272_;
}
else
{
lean_dec(v___x_276_);
v___y_273_ = v___x_270_;
goto v___jp_272_;
}
v___jp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_nat_add(v_lower_263_, v_start_260_);
lean_dec(v_lower_263_);
v___x_266_ = lean_nat_add(v_upper_264_, v_start_260_);
lean_dec(v_start_260_);
lean_dec(v_upper_264_);
v___x_267_ = l_Array_toSubarray___redArg(v_array_259_, v___x_265_, v___x_266_);
return v___x_267_;
}
v___jp_272_:
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_le(v_upper_269_, v___x_271_);
if (v___x_274_ == 0)
{
lean_dec(v_upper_269_);
v_lower_263_ = v___y_273_;
v_upper_264_ = v___x_271_;
goto v___jp_262_;
}
else
{
lean_dec(v___x_271_);
v_lower_263_ = v___y_273_;
v_upper_264_ = v_upper_269_;
goto v___jp_262_;
}
}
}
}
lean_object* l_instSliceableSubarrayNat__4___redArg(){
_start:
{
lean_object* v___f_280_; 
v___f_280_ = ((lean_object*)(l_instSliceableSubarrayNat__4___redArg___closed__0));
return v___f_280_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_281_;
v_res_281_ = l_instSliceableSubarrayNat__4___redArg();
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4___redArg___boxed(lean_object* v___dummy_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_instSliceableSubarrayNat__4___redArg();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__4(lean_object* v_00_u03b1_284_){
_start:
{
lean_object* v___f_285_; 
v___f_285_ = ((lean_object*)(l_instSliceableSubarrayNat__4___redArg___closed__0));
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___lam__0(lean_object* v_xs_286_, lean_object* v_range_287_){
_start:
{
lean_object* v_array_288_; lean_object* v_start_289_; lean_object* v_stop_290_; lean_object* v_lower_292_; lean_object* v_upper_293_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_array_288_ = lean_ctor_get(v_xs_286_, 0);
lean_inc_ref(v_array_288_);
v_start_289_ = lean_ctor_get(v_xs_286_, 1);
lean_inc(v_start_289_);
v_stop_290_ = lean_ctor_get(v_xs_286_, 2);
lean_inc(v_stop_290_);
lean_dec_ref(v_xs_286_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_nat_sub(v_stop_290_, v_start_289_);
lean_dec(v_stop_290_);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v_range_287_, v___x_299_);
v___x_301_ = lean_nat_dec_le(v___x_300_, v___x_297_);
if (v___x_301_ == 0)
{
v_lower_292_ = v___x_300_;
v_upper_293_ = v___x_298_;
goto v___jp_291_;
}
else
{
lean_dec(v___x_300_);
v_lower_292_ = v___x_297_;
v_upper_293_ = v___x_298_;
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_nat_add(v_lower_292_, v_start_289_);
lean_dec(v_lower_292_);
v___x_295_ = lean_nat_add(v_upper_293_, v_start_289_);
lean_dec(v_start_289_);
lean_dec(v_upper_293_);
v___x_296_ = l_Array_toSubarray___redArg(v_array_288_, v___x_294_, v___x_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___lam__0___boxed(lean_object* v_xs_302_, lean_object* v_range_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_instSliceableSubarrayNat__5___redArg___lam__0(v_xs_302_, v_range_303_);
lean_dec(v_range_303_);
return v_res_304_;
}
}
lean_object* l_instSliceableSubarrayNat__5___redArg(){
_start:
{
lean_object* v___f_307_; 
v___f_307_ = ((lean_object*)(l_instSliceableSubarrayNat__5___redArg___closed__0));
return v___f_307_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_308_;
v_res_308_ = l_instSliceableSubarrayNat__5___redArg();
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5___redArg___boxed(lean_object* v___dummy_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_instSliceableSubarrayNat__5___redArg();
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__5(lean_object* v_00_u03b1_311_){
_start:
{
lean_object* v___f_312_; 
v___f_312_ = ((lean_object*)(l_instSliceableSubarrayNat__5___redArg___closed__0));
return v___f_312_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___lam__0(lean_object* v_xs_313_, lean_object* v_range_314_){
_start:
{
lean_object* v_array_315_; lean_object* v_start_316_; lean_object* v_stop_317_; lean_object* v_lower_319_; lean_object* v_upper_320_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_array_315_ = lean_ctor_get(v_xs_313_, 0);
lean_inc_ref(v_array_315_);
v_start_316_ = lean_ctor_get(v_xs_313_, 1);
lean_inc(v_start_316_);
v_stop_317_ = lean_ctor_get(v_xs_313_, 2);
lean_inc(v_stop_317_);
lean_dec_ref(v_xs_313_);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_nat_sub(v_stop_317_, v_start_316_);
lean_dec(v_stop_317_);
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_add(v_range_314_, v___x_326_);
v___x_328_ = lean_nat_dec_le(v___x_327_, v___x_325_);
if (v___x_328_ == 0)
{
lean_dec(v___x_327_);
v_lower_319_ = v___x_324_;
v_upper_320_ = v___x_325_;
goto v___jp_318_;
}
else
{
lean_dec(v___x_325_);
v_lower_319_ = v___x_324_;
v_upper_320_ = v___x_327_;
goto v___jp_318_;
}
v___jp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_nat_add(v_lower_319_, v_start_316_);
v___x_322_ = lean_nat_add(v_upper_320_, v_start_316_);
lean_dec(v_start_316_);
lean_dec(v_upper_320_);
v___x_323_ = l_Array_toSubarray___redArg(v_array_315_, v___x_321_, v___x_322_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___lam__0___boxed(lean_object* v_xs_329_, lean_object* v_range_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_instSliceableSubarrayNat__6___redArg___lam__0(v_xs_329_, v_range_330_);
lean_dec(v_range_330_);
return v_res_331_;
}
}
lean_object* l_instSliceableSubarrayNat__6___redArg(){
_start:
{
lean_object* v___f_334_; 
v___f_334_ = ((lean_object*)(l_instSliceableSubarrayNat__6___redArg___closed__0));
return v___f_334_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_335_;
v_res_335_ = l_instSliceableSubarrayNat__6___redArg();
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6___redArg___boxed(lean_object* v___dummy_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_instSliceableSubarrayNat__6___redArg();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__6(lean_object* v_00_u03b1_338_){
_start:
{
lean_object* v___f_339_; 
v___f_339_ = ((lean_object*)(l_instSliceableSubarrayNat__6___redArg___closed__0));
return v___f_339_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg___lam__0(lean_object* v_xs_340_, lean_object* v_range_341_){
_start:
{
lean_object* v_array_342_; lean_object* v_start_343_; lean_object* v_stop_344_; lean_object* v_lower_346_; lean_object* v_upper_347_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_array_342_ = lean_ctor_get(v_xs_340_, 0);
lean_inc_ref(v_array_342_);
v_start_343_ = lean_ctor_get(v_xs_340_, 1);
lean_inc(v_start_343_);
v_stop_344_ = lean_ctor_get(v_xs_340_, 2);
lean_inc(v_stop_344_);
lean_dec_ref(v_xs_340_);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_nat_sub(v_stop_344_, v_start_343_);
lean_dec(v_stop_344_);
v___x_353_ = lean_nat_dec_le(v_range_341_, v___x_352_);
if (v___x_353_ == 0)
{
lean_dec(v_range_341_);
v_lower_346_ = v___x_351_;
v_upper_347_ = v___x_352_;
goto v___jp_345_;
}
else
{
lean_dec(v___x_352_);
v_lower_346_ = v___x_351_;
v_upper_347_ = v_range_341_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_nat_add(v_lower_346_, v_start_343_);
v___x_349_ = lean_nat_add(v_upper_347_, v_start_343_);
lean_dec(v_start_343_);
lean_dec(v_upper_347_);
v___x_350_ = l_Array_toSubarray___redArg(v_array_342_, v___x_348_, v___x_349_);
return v___x_350_;
}
}
}
lean_object* l_instSliceableSubarrayNat__7___redArg(){
_start:
{
lean_object* v___f_356_; 
v___f_356_ = ((lean_object*)(l_instSliceableSubarrayNat__7___redArg___closed__0));
return v___f_356_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_357_;
v_res_357_ = l_instSliceableSubarrayNat__7___redArg();
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7___redArg___boxed(lean_object* v___dummy_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_instSliceableSubarrayNat__7___redArg();
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__7(lean_object* v_00_u03b1_360_){
_start:
{
lean_object* v___f_361_; 
v___f_361_ = ((lean_object*)(l_instSliceableSubarrayNat__7___redArg___closed__0));
return v___f_361_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___lam__0(lean_object* v_xs_362_, lean_object* v_x_363_){
_start:
{
lean_inc_ref(v_xs_362_);
return v_xs_362_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___lam__0___boxed(lean_object* v_xs_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_instSliceableSubarrayNat__8___redArg___lam__0(v_xs_364_, v_x_365_);
lean_dec_ref(v_xs_364_);
return v_res_366_;
}
}
lean_object* l_instSliceableSubarrayNat__8___redArg(){
_start:
{
lean_object* v___f_369_; 
v___f_369_ = ((lean_object*)(l_instSliceableSubarrayNat__8___redArg___closed__0));
return v___f_369_;
}
}
LEAN_EXPORT void l_instSliceableSubarrayNat__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_370_;
v_res_370_ = l_instSliceableSubarrayNat__8___redArg();
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8___redArg___boxed(lean_object* v___dummy_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_instSliceableSubarrayNat__8___redArg();
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_instSliceableSubarrayNat__8(lean_object* v_00_u03b1_373_){
_start:
{
lean_object* v___f_374_; 
v___f_374_ = ((lean_object*)(l_instSliceableSubarrayNat__8___redArg___closed__0));
return v___f_374_;
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
