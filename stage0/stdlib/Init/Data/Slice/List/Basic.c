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
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__1___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1(lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_toUnboundedSlice___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__2___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__3___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__4___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__5___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__5___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__6___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__6___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__7___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__7___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListNatListSlice__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListNatListSlice__8___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListNatListSlice__8___redArg___closed__0 = (const lean_object*)&l_instSliceableListNatListSlice__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg();
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__1___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__1___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__2___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__3___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__4___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__5___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__5___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__6___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__6___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__7___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__7___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableListSliceNat__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableListSliceNat__8___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableListSliceNat__8___redArg___closed__0 = (const lean_object*)&l_instSliceableListSliceNat__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg();
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg___lam__0(lean_object* v_xs_45_, lean_object* v_range_46_){
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
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg___lam__0___boxed(lean_object* v_xs_52_, lean_object* v_range_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_instSliceableListNatListSlice___redArg___lam__0(v_xs_52_, v_range_53_);
lean_dec(v_xs_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg(){
_start:
{
lean_object* v___f_57_; 
v___f_57_ = ((lean_object*)(l_instSliceableListNatListSlice___redArg___closed__0));
return v___f_57_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_instSliceableListNatListSlice___redArg();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice(lean_object* v_00_u03b1_60_){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = ((lean_object*)(l_instSliceableListNatListSlice___redArg___closed__0));
return v___f_61_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___lam__0(lean_object* v_xs_62_, lean_object* v_range_63_){
_start:
{
lean_object* v_lower_64_; lean_object* v_upper_65_; lean_object* v___x_66_; 
v_lower_64_ = lean_ctor_get(v_range_63_, 0);
lean_inc(v_lower_64_);
v_upper_65_ = lean_ctor_get(v_range_63_, 1);
lean_inc(v_upper_65_);
lean_dec_ref(v_range_63_);
v___x_66_ = l_List_toSlice___redArg(v_xs_62_, v_lower_64_, v_upper_65_);
lean_dec(v_upper_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___lam__0___boxed(lean_object* v_xs_67_, lean_object* v_range_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_instSliceableListNatListSlice__1___redArg___lam__0(v_xs_67_, v_range_68_);
lean_dec(v_xs_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg(){
_start:
{
lean_object* v___f_72_; 
v___f_72_ = ((lean_object*)(l_instSliceableListNatListSlice__1___redArg___closed__0));
return v___f_72_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___boxed(lean_object* v___dummy_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_instSliceableListNatListSlice__1___redArg();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1(lean_object* v_00_u03b1_75_){
_start:
{
lean_object* v___f_76_; 
v___f_76_ = ((lean_object*)(l_instSliceableListNatListSlice__1___redArg___closed__0));
return v___f_76_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2___redArg(){
_start:
{
lean_object* v___f_79_; 
v___f_79_ = ((lean_object*)(l_instSliceableListNatListSlice__2___redArg___closed__0));
return v___f_79_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2___redArg___boxed(lean_object* v___dummy_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_instSliceableListNatListSlice__2___redArg();
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2(lean_object* v_00_u03b1_82_){
_start:
{
lean_object* v___f_83_; 
v___f_83_ = ((lean_object*)(l_instSliceableListNatListSlice__2___redArg___closed__0));
return v___f_83_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___lam__0(lean_object* v_xs_84_, lean_object* v_range_85_){
_start:
{
lean_object* v_lower_86_; lean_object* v_upper_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_lower_86_ = lean_ctor_get(v_range_85_, 0);
v_upper_87_ = lean_ctor_get(v_range_85_, 1);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_add(v_lower_86_, v___x_88_);
v___x_90_ = lean_nat_add(v_upper_87_, v___x_88_);
v___x_91_ = l_List_toSlice___redArg(v_xs_84_, v___x_89_, v___x_90_);
lean_dec(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___lam__0___boxed(lean_object* v_xs_92_, lean_object* v_range_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_instSliceableListNatListSlice__3___redArg___lam__0(v_xs_92_, v_range_93_);
lean_dec_ref(v_range_93_);
lean_dec(v_xs_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg(){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = ((lean_object*)(l_instSliceableListNatListSlice__3___redArg___closed__0));
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___boxed(lean_object* v___dummy_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_instSliceableListNatListSlice__3___redArg();
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3(lean_object* v_00_u03b1_100_){
_start:
{
lean_object* v___f_101_; 
v___f_101_ = ((lean_object*)(l_instSliceableListNatListSlice__3___redArg___closed__0));
return v___f_101_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___lam__0(lean_object* v_xs_102_, lean_object* v_range_103_){
_start:
{
lean_object* v_lower_104_; lean_object* v_upper_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_lower_104_ = lean_ctor_get(v_range_103_, 0);
v_upper_105_ = lean_ctor_get(v_range_103_, 1);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_lower_104_, v___x_106_);
v___x_108_ = l_List_toSlice___redArg(v_xs_102_, v___x_107_, v_upper_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___lam__0___boxed(lean_object* v_xs_109_, lean_object* v_range_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_instSliceableListNatListSlice__4___redArg___lam__0(v_xs_109_, v_range_110_);
lean_dec_ref(v_range_110_);
lean_dec(v_xs_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg(){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = ((lean_object*)(l_instSliceableListNatListSlice__4___redArg___closed__0));
return v___f_114_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___boxed(lean_object* v___dummy_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_instSliceableListNatListSlice__4___redArg();
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4(lean_object* v_00_u03b1_117_){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = ((lean_object*)(l_instSliceableListNatListSlice__4___redArg___closed__0));
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___lam__0(lean_object* v_xs_119_, lean_object* v_range_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_range_120_, v___x_121_);
v___x_123_ = l_List_toUnboundedSlice___redArg(v_xs_119_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___lam__0___boxed(lean_object* v_xs_124_, lean_object* v_range_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_instSliceableListNatListSlice__5___redArg___lam__0(v_xs_124_, v_range_125_);
lean_dec(v_range_125_);
lean_dec(v_xs_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg(){
_start:
{
lean_object* v___f_129_; 
v___f_129_ = ((lean_object*)(l_instSliceableListNatListSlice__5___redArg___closed__0));
return v___f_129_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___boxed(lean_object* v___dummy_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_instSliceableListNatListSlice__5___redArg();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5(lean_object* v_00_u03b1_132_){
_start:
{
lean_object* v___f_133_; 
v___f_133_ = ((lean_object*)(l_instSliceableListNatListSlice__5___redArg___closed__0));
return v___f_133_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___lam__0(lean_object* v_xs_134_, lean_object* v_range_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_range_135_, v___x_137_);
v___x_139_ = l_List_toSlice___redArg(v_xs_134_, v___x_136_, v___x_138_);
lean_dec(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___lam__0___boxed(lean_object* v_xs_140_, lean_object* v_range_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_instSliceableListNatListSlice__6___redArg___lam__0(v_xs_140_, v_range_141_);
lean_dec(v_range_141_);
lean_dec(v_xs_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg(){
_start:
{
lean_object* v___f_145_; 
v___f_145_ = ((lean_object*)(l_instSliceableListNatListSlice__6___redArg___closed__0));
return v___f_145_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___boxed(lean_object* v___dummy_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_instSliceableListNatListSlice__6___redArg();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6(lean_object* v_00_u03b1_148_){
_start:
{
lean_object* v___f_149_; 
v___f_149_ = ((lean_object*)(l_instSliceableListNatListSlice__6___redArg___closed__0));
return v___f_149_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___lam__0(lean_object* v_xs_150_, lean_object* v_range_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = l_List_toSlice___redArg(v_xs_150_, v___x_152_, v_range_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___lam__0___boxed(lean_object* v_xs_154_, lean_object* v_range_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_instSliceableListNatListSlice__7___redArg___lam__0(v_xs_154_, v_range_155_);
lean_dec(v_range_155_);
lean_dec(v_xs_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg(){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = ((lean_object*)(l_instSliceableListNatListSlice__7___redArg___closed__0));
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___boxed(lean_object* v___dummy_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_instSliceableListNatListSlice__7___redArg();
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7(lean_object* v_00_u03b1_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = ((lean_object*)(l_instSliceableListNatListSlice__7___redArg___closed__0));
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___lam__0(lean_object* v_xs_164_, lean_object* v_x_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = l_List_toUnboundedSlice___redArg(v_xs_164_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___lam__0___boxed(lean_object* v_xs_168_, lean_object* v_x_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_instSliceableListNatListSlice__8___redArg___lam__0(v_xs_168_, v_x_169_);
lean_dec(v_xs_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg(){
_start:
{
lean_object* v___f_173_; 
v___f_173_ = ((lean_object*)(l_instSliceableListNatListSlice__8___redArg___closed__0));
return v___f_173_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___boxed(lean_object* v___dummy_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_instSliceableListNatListSlice__8___redArg();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8(lean_object* v_00_u03b1_176_){
_start:
{
lean_object* v___f_177_; 
v___f_177_ = ((lean_object*)(l_instSliceableListNatListSlice__8___redArg___closed__0));
return v___f_177_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg___lam__0(lean_object* v_xs_178_, lean_object* v_range_179_){
_start:
{
lean_object* v_list_180_; lean_object* v_stop_181_; lean_object* v___y_183_; 
v_list_180_ = lean_ctor_get(v_xs_178_, 0);
lean_inc(v_list_180_);
v_stop_181_ = lean_ctor_get(v_xs_178_, 1);
lean_inc(v_stop_181_);
lean_dec_ref(v_xs_178_);
if (lean_obj_tag(v_stop_181_) == 0)
{
lean_object* v_upper_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_upper_186_ = lean_ctor_get(v_range_179_, 1);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_upper_186_, v___x_187_);
v___y_183_ = v___x_188_;
goto v___jp_182_;
}
else
{
lean_object* v_val_189_; lean_object* v_upper_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_val_189_ = lean_ctor_get(v_stop_181_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v_stop_181_, 1);
v_upper_190_ = lean_ctor_get(v_range_179_, 1);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_upper_190_, v___x_191_);
v___x_193_ = lean_nat_dec_le(v_val_189_, v___x_192_);
if (v___x_193_ == 0)
{
lean_dec(v_val_189_);
v___y_183_ = v___x_192_;
goto v___jp_182_;
}
else
{
lean_dec(v___x_192_);
v___y_183_ = v_val_189_;
goto v___jp_182_;
}
}
v___jp_182_:
{
lean_object* v_lower_184_; lean_object* v___x_185_; 
v_lower_184_ = lean_ctor_get(v_range_179_, 0);
lean_inc(v_lower_184_);
lean_dec_ref(v_range_179_);
v___x_185_ = l_List_toSlice___redArg(v_list_180_, v_lower_184_, v___y_183_);
lean_dec(v___y_183_);
lean_dec(v_list_180_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg(){
_start:
{
lean_object* v___f_196_; 
v___f_196_ = ((lean_object*)(l_instSliceableListSliceNat___redArg___closed__0));
return v___f_196_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg___boxed(lean_object* v___dummy_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_instSliceableListSliceNat___redArg();
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat(lean_object* v_00_u03b1_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = ((lean_object*)(l_instSliceableListSliceNat___redArg___closed__0));
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg___lam__0(lean_object* v_xs_201_, lean_object* v_range_202_){
_start:
{
lean_object* v_list_203_; lean_object* v_stop_204_; lean_object* v___y_206_; 
v_list_203_ = lean_ctor_get(v_xs_201_, 0);
lean_inc(v_list_203_);
v_stop_204_ = lean_ctor_get(v_xs_201_, 1);
lean_inc(v_stop_204_);
lean_dec_ref(v_xs_201_);
if (lean_obj_tag(v_stop_204_) == 0)
{
lean_object* v_upper_209_; 
v_upper_209_ = lean_ctor_get(v_range_202_, 1);
lean_inc(v_upper_209_);
v___y_206_ = v_upper_209_;
goto v___jp_205_;
}
else
{
lean_object* v_val_210_; lean_object* v_upper_211_; uint8_t v___x_212_; 
v_val_210_ = lean_ctor_get(v_stop_204_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v_stop_204_, 1);
v_upper_211_ = lean_ctor_get(v_range_202_, 1);
v___x_212_ = lean_nat_dec_le(v_val_210_, v_upper_211_);
if (v___x_212_ == 0)
{
lean_dec(v_val_210_);
lean_inc(v_upper_211_);
v___y_206_ = v_upper_211_;
goto v___jp_205_;
}
else
{
v___y_206_ = v_val_210_;
goto v___jp_205_;
}
}
v___jp_205_:
{
lean_object* v_lower_207_; lean_object* v___x_208_; 
v_lower_207_ = lean_ctor_get(v_range_202_, 0);
lean_inc(v_lower_207_);
lean_dec_ref(v_range_202_);
v___x_208_ = l_List_toSlice___redArg(v_list_203_, v_lower_207_, v___y_206_);
lean_dec(v___y_206_);
lean_dec(v_list_203_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg(){
_start:
{
lean_object* v___f_215_; 
v___f_215_ = ((lean_object*)(l_instSliceableListSliceNat__1___redArg___closed__0));
return v___f_215_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg___boxed(lean_object* v___dummy_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_instSliceableListSliceNat__1___redArg();
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1(lean_object* v_00_u03b1_218_){
_start:
{
lean_object* v___f_219_; 
v___f_219_ = ((lean_object*)(l_instSliceableListSliceNat__1___redArg___closed__0));
return v___f_219_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___lam__0(lean_object* v_xs_220_, lean_object* v_range_221_){
_start:
{
lean_object* v_stop_222_; 
v_stop_222_ = lean_ctor_get(v_xs_220_, 1);
if (lean_obj_tag(v_stop_222_) == 0)
{
lean_object* v_list_223_; lean_object* v___x_224_; 
v_list_223_ = lean_ctor_get(v_xs_220_, 0);
v___x_224_ = l_List_toUnboundedSlice___redArg(v_list_223_, v_range_221_);
return v___x_224_;
}
else
{
lean_object* v_list_225_; lean_object* v_val_226_; lean_object* v___x_227_; 
v_list_225_ = lean_ctor_get(v_xs_220_, 0);
v_val_226_ = lean_ctor_get(v_stop_222_, 0);
v___x_227_ = l_List_toSlice___redArg(v_list_225_, v_range_221_, v_val_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___lam__0___boxed(lean_object* v_xs_228_, lean_object* v_range_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_instSliceableListSliceNat__2___redArg___lam__0(v_xs_228_, v_range_229_);
lean_dec_ref(v_xs_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg(){
_start:
{
lean_object* v___f_233_; 
v___f_233_ = ((lean_object*)(l_instSliceableListSliceNat__2___redArg___closed__0));
return v___f_233_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___boxed(lean_object* v___dummy_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_instSliceableListSliceNat__2___redArg();
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2(lean_object* v_00_u03b1_236_){
_start:
{
lean_object* v___f_237_; 
v___f_237_ = ((lean_object*)(l_instSliceableListSliceNat__2___redArg___closed__0));
return v___f_237_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___lam__0(lean_object* v_xs_238_, lean_object* v_range_239_){
_start:
{
lean_object* v_list_240_; lean_object* v_stop_241_; lean_object* v___y_243_; 
v_list_240_ = lean_ctor_get(v_xs_238_, 0);
lean_inc(v_list_240_);
v_stop_241_ = lean_ctor_get(v_xs_238_, 1);
lean_inc(v_stop_241_);
lean_dec_ref(v_xs_238_);
if (lean_obj_tag(v_stop_241_) == 0)
{
lean_object* v_upper_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_upper_248_ = lean_ctor_get(v_range_239_, 1);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_upper_248_, v___x_249_);
v___y_243_ = v___x_250_;
goto v___jp_242_;
}
else
{
lean_object* v_val_251_; lean_object* v_upper_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_val_251_ = lean_ctor_get(v_stop_241_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v_stop_241_, 1);
v_upper_252_ = lean_ctor_get(v_range_239_, 1);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_upper_252_, v___x_253_);
v___x_255_ = lean_nat_dec_le(v_val_251_, v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v_val_251_);
v___y_243_ = v___x_254_;
goto v___jp_242_;
}
else
{
lean_dec(v___x_254_);
v___y_243_ = v_val_251_;
goto v___jp_242_;
}
}
v___jp_242_:
{
lean_object* v_lower_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_lower_244_ = lean_ctor_get(v_range_239_, 0);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_add(v_lower_244_, v___x_245_);
v___x_247_ = l_List_toSlice___redArg(v_list_240_, v___x_246_, v___y_243_);
lean_dec(v___y_243_);
lean_dec(v_list_240_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___lam__0___boxed(lean_object* v_xs_256_, lean_object* v_range_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_instSliceableListSliceNat__3___redArg___lam__0(v_xs_256_, v_range_257_);
lean_dec_ref(v_range_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg(){
_start:
{
lean_object* v___f_261_; 
v___f_261_ = ((lean_object*)(l_instSliceableListSliceNat__3___redArg___closed__0));
return v___f_261_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___boxed(lean_object* v___dummy_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_instSliceableListSliceNat__3___redArg();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3(lean_object* v_00_u03b1_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = ((lean_object*)(l_instSliceableListSliceNat__3___redArg___closed__0));
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___lam__0(lean_object* v_xs_266_, lean_object* v_range_267_){
_start:
{
lean_object* v_list_268_; lean_object* v_stop_269_; lean_object* v___y_271_; 
v_list_268_ = lean_ctor_get(v_xs_266_, 0);
v_stop_269_ = lean_ctor_get(v_xs_266_, 1);
if (lean_obj_tag(v_stop_269_) == 0)
{
lean_object* v_upper_276_; 
v_upper_276_ = lean_ctor_get(v_range_267_, 1);
v___y_271_ = v_upper_276_;
goto v___jp_270_;
}
else
{
lean_object* v_val_277_; lean_object* v_upper_278_; uint8_t v___x_279_; 
v_val_277_ = lean_ctor_get(v_stop_269_, 0);
v_upper_278_ = lean_ctor_get(v_range_267_, 1);
v___x_279_ = lean_nat_dec_le(v_val_277_, v_upper_278_);
if (v___x_279_ == 0)
{
v___y_271_ = v_upper_278_;
goto v___jp_270_;
}
else
{
v___y_271_ = v_val_277_;
goto v___jp_270_;
}
}
v___jp_270_:
{
lean_object* v_lower_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_lower_272_ = lean_ctor_get(v_range_267_, 0);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_lower_272_, v___x_273_);
v___x_275_ = l_List_toSlice___redArg(v_list_268_, v___x_274_, v___y_271_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___lam__0___boxed(lean_object* v_xs_280_, lean_object* v_range_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_instSliceableListSliceNat__4___redArg___lam__0(v_xs_280_, v_range_281_);
lean_dec_ref(v_range_281_);
lean_dec_ref(v_xs_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg(){
_start:
{
lean_object* v___f_285_; 
v___f_285_ = ((lean_object*)(l_instSliceableListSliceNat__4___redArg___closed__0));
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___boxed(lean_object* v___dummy_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_instSliceableListSliceNat__4___redArg();
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4(lean_object* v_00_u03b1_288_){
_start:
{
lean_object* v___f_289_; 
v___f_289_ = ((lean_object*)(l_instSliceableListSliceNat__4___redArg___closed__0));
return v___f_289_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___lam__0(lean_object* v_xs_290_, lean_object* v_range_291_){
_start:
{
lean_object* v_stop_292_; 
v_stop_292_ = lean_ctor_get(v_xs_290_, 1);
if (lean_obj_tag(v_stop_292_) == 0)
{
lean_object* v_list_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_list_293_ = lean_ctor_get(v_xs_290_, 0);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_range_291_, v___x_294_);
v___x_296_ = l_List_toUnboundedSlice___redArg(v_list_293_, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v_list_297_; lean_object* v_val_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_list_297_ = lean_ctor_get(v_xs_290_, 0);
v_val_298_ = lean_ctor_get(v_stop_292_, 0);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v_range_291_, v___x_299_);
v___x_301_ = l_List_toSlice___redArg(v_list_297_, v___x_300_, v_val_298_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___lam__0___boxed(lean_object* v_xs_302_, lean_object* v_range_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_instSliceableListSliceNat__5___redArg___lam__0(v_xs_302_, v_range_303_);
lean_dec(v_range_303_);
lean_dec_ref(v_xs_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg(){
_start:
{
lean_object* v___f_307_; 
v___f_307_ = ((lean_object*)(l_instSliceableListSliceNat__5___redArg___closed__0));
return v___f_307_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___boxed(lean_object* v___dummy_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_instSliceableListSliceNat__5___redArg();
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5(lean_object* v_00_u03b1_310_){
_start:
{
lean_object* v___f_311_; 
v___f_311_ = ((lean_object*)(l_instSliceableListSliceNat__5___redArg___closed__0));
return v___f_311_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___lam__0(lean_object* v_xs_312_, lean_object* v_range_313_){
_start:
{
lean_object* v_list_314_; lean_object* v_stop_315_; lean_object* v___y_317_; 
v_list_314_ = lean_ctor_get(v_xs_312_, 0);
lean_inc(v_list_314_);
v_stop_315_ = lean_ctor_get(v_xs_312_, 1);
lean_inc(v_stop_315_);
lean_dec_ref(v_xs_312_);
if (lean_obj_tag(v_stop_315_) == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_range_313_, v___x_320_);
v___y_317_ = v___x_321_;
goto v___jp_316_;
}
else
{
lean_object* v_val_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_val_322_ = lean_ctor_get(v_stop_315_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_stop_315_, 1);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_add(v_range_313_, v___x_323_);
v___x_325_ = lean_nat_dec_le(v_val_322_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec(v_val_322_);
v___y_317_ = v___x_324_;
goto v___jp_316_;
}
else
{
lean_dec(v___x_324_);
v___y_317_ = v_val_322_;
goto v___jp_316_;
}
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_List_toSlice___redArg(v_list_314_, v___x_318_, v___y_317_);
lean_dec(v___y_317_);
lean_dec(v_list_314_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___lam__0___boxed(lean_object* v_xs_326_, lean_object* v_range_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_instSliceableListSliceNat__6___redArg___lam__0(v_xs_326_, v_range_327_);
lean_dec(v_range_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg(){
_start:
{
lean_object* v___f_331_; 
v___f_331_ = ((lean_object*)(l_instSliceableListSliceNat__6___redArg___closed__0));
return v___f_331_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___boxed(lean_object* v___dummy_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_instSliceableListSliceNat__6___redArg();
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6(lean_object* v_00_u03b1_334_){
_start:
{
lean_object* v___f_335_; 
v___f_335_ = ((lean_object*)(l_instSliceableListSliceNat__6___redArg___closed__0));
return v___f_335_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___lam__0(lean_object* v_xs_336_, lean_object* v_range_337_){
_start:
{
lean_object* v_list_338_; lean_object* v_stop_339_; lean_object* v___y_341_; 
v_list_338_ = lean_ctor_get(v_xs_336_, 0);
v_stop_339_ = lean_ctor_get(v_xs_336_, 1);
if (lean_obj_tag(v_stop_339_) == 0)
{
v___y_341_ = v_range_337_;
goto v___jp_340_;
}
else
{
lean_object* v_val_344_; uint8_t v___x_345_; 
v_val_344_ = lean_ctor_get(v_stop_339_, 0);
v___x_345_ = lean_nat_dec_le(v_val_344_, v_range_337_);
if (v___x_345_ == 0)
{
v___y_341_ = v_range_337_;
goto v___jp_340_;
}
else
{
v___y_341_ = v_val_344_;
goto v___jp_340_;
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = l_List_toSlice___redArg(v_list_338_, v___x_342_, v___y_341_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___lam__0___boxed(lean_object* v_xs_346_, lean_object* v_range_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_instSliceableListSliceNat__7___redArg___lam__0(v_xs_346_, v_range_347_);
lean_dec(v_range_347_);
lean_dec_ref(v_xs_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg(){
_start:
{
lean_object* v___f_351_; 
v___f_351_ = ((lean_object*)(l_instSliceableListSliceNat__7___redArg___closed__0));
return v___f_351_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___boxed(lean_object* v___dummy_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_instSliceableListSliceNat__7___redArg();
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7(lean_object* v_00_u03b1_354_){
_start:
{
lean_object* v___f_355_; 
v___f_355_ = ((lean_object*)(l_instSliceableListSliceNat__7___redArg___closed__0));
return v___f_355_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___lam__0(lean_object* v_xs_356_, lean_object* v_x_357_){
_start:
{
lean_inc_ref(v_xs_356_);
return v_xs_356_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___lam__0___boxed(lean_object* v_xs_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_instSliceableListSliceNat__8___redArg___lam__0(v_xs_358_, v_x_359_);
lean_dec_ref(v_xs_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg(){
_start:
{
lean_object* v___f_363_; 
v___f_363_ = ((lean_object*)(l_instSliceableListSliceNat__8___redArg___closed__0));
return v___f_363_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___boxed(lean_object* v___dummy_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_instSliceableListSliceNat__8___redArg();
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8(lean_object* v_00_u03b1_366_){
_start:
{
lean_object* v___f_367_; 
v___f_367_ = ((lean_object*)(l_instSliceableListSliceNat__8___redArg___closed__0));
return v___f_367_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Notation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
