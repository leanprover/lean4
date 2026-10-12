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
lean_object* l_instSliceableListNatListSlice___redArg(){
_start:
{
lean_object* v___f_57_; 
v___f_57_ = ((lean_object*)(l_instSliceableListNatListSlice___redArg___closed__0));
return v___f_57_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l_instSliceableListNatListSlice___redArg();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice___redArg___boxed(lean_object* v___dummy_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_instSliceableListNatListSlice___redArg();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice(lean_object* v_00_u03b1_61_){
_start:
{
lean_object* v___f_62_; 
v___f_62_ = ((lean_object*)(l_instSliceableListNatListSlice___redArg___closed__0));
return v___f_62_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___lam__0(lean_object* v_xs_63_, lean_object* v_range_64_){
_start:
{
lean_object* v_lower_65_; lean_object* v_upper_66_; lean_object* v___x_67_; 
v_lower_65_ = lean_ctor_get(v_range_64_, 0);
lean_inc(v_lower_65_);
v_upper_66_ = lean_ctor_get(v_range_64_, 1);
lean_inc(v_upper_66_);
lean_dec_ref(v_range_64_);
v___x_67_ = l_List_toSlice___redArg(v_xs_63_, v_lower_65_, v_upper_66_);
lean_dec(v_upper_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___lam__0___boxed(lean_object* v_xs_68_, lean_object* v_range_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_instSliceableListNatListSlice__1___redArg___lam__0(v_xs_68_, v_range_69_);
lean_dec(v_xs_68_);
return v_res_70_;
}
}
lean_object* l_instSliceableListNatListSlice__1___redArg(){
_start:
{
lean_object* v___f_73_; 
v___f_73_ = ((lean_object*)(l_instSliceableListNatListSlice__1___redArg___closed__0));
return v___f_73_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_74_;
v_res_74_ = l_instSliceableListNatListSlice__1___redArg();
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_instSliceableListNatListSlice__1___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__1(lean_object* v_00_u03b1_77_){
_start:
{
lean_object* v___f_78_; 
v___f_78_ = ((lean_object*)(l_instSliceableListNatListSlice__1___redArg___closed__0));
return v___f_78_;
}
}
lean_object* l_instSliceableListNatListSlice__2___redArg(){
_start:
{
lean_object* v___f_81_; 
v___f_81_ = ((lean_object*)(l_instSliceableListNatListSlice__2___redArg___closed__0));
return v___f_81_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_82_;
v_res_82_ = l_instSliceableListNatListSlice__2___redArg();
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_instSliceableListNatListSlice__2___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__2(lean_object* v_00_u03b1_85_){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = ((lean_object*)(l_instSliceableListNatListSlice__2___redArg___closed__0));
return v___f_86_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___lam__0(lean_object* v_xs_87_, lean_object* v_range_88_){
_start:
{
lean_object* v_lower_89_; lean_object* v_upper_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_lower_89_ = lean_ctor_get(v_range_88_, 0);
v_upper_90_ = lean_ctor_get(v_range_88_, 1);
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v_lower_89_, v___x_91_);
v___x_93_ = lean_nat_add(v_upper_90_, v___x_91_);
v___x_94_ = l_List_toSlice___redArg(v_xs_87_, v___x_92_, v___x_93_);
lean_dec(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___lam__0___boxed(lean_object* v_xs_95_, lean_object* v_range_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_instSliceableListNatListSlice__3___redArg___lam__0(v_xs_95_, v_range_96_);
lean_dec_ref(v_range_96_);
lean_dec(v_xs_95_);
return v_res_97_;
}
}
lean_object* l_instSliceableListNatListSlice__3___redArg(){
_start:
{
lean_object* v___f_100_; 
v___f_100_ = ((lean_object*)(l_instSliceableListNatListSlice__3___redArg___closed__0));
return v___f_100_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_101_;
v_res_101_ = l_instSliceableListNatListSlice__3___redArg();
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3___redArg___boxed(lean_object* v___dummy_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_instSliceableListNatListSlice__3___redArg();
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__3(lean_object* v_00_u03b1_104_){
_start:
{
lean_object* v___f_105_; 
v___f_105_ = ((lean_object*)(l_instSliceableListNatListSlice__3___redArg___closed__0));
return v___f_105_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___lam__0(lean_object* v_xs_106_, lean_object* v_range_107_){
_start:
{
lean_object* v_lower_108_; lean_object* v_upper_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_lower_108_ = lean_ctor_get(v_range_107_, 0);
v_upper_109_ = lean_ctor_get(v_range_107_, 1);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_lower_108_, v___x_110_);
v___x_112_ = l_List_toSlice___redArg(v_xs_106_, v___x_111_, v_upper_109_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___lam__0___boxed(lean_object* v_xs_113_, lean_object* v_range_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_instSliceableListNatListSlice__4___redArg___lam__0(v_xs_113_, v_range_114_);
lean_dec_ref(v_range_114_);
lean_dec(v_xs_113_);
return v_res_115_;
}
}
lean_object* l_instSliceableListNatListSlice__4___redArg(){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = ((lean_object*)(l_instSliceableListNatListSlice__4___redArg___closed__0));
return v___f_118_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_119_;
v_res_119_ = l_instSliceableListNatListSlice__4___redArg();
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4___redArg___boxed(lean_object* v___dummy_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_instSliceableListNatListSlice__4___redArg();
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__4(lean_object* v_00_u03b1_122_){
_start:
{
lean_object* v___f_123_; 
v___f_123_ = ((lean_object*)(l_instSliceableListNatListSlice__4___redArg___closed__0));
return v___f_123_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___lam__0(lean_object* v_xs_124_, lean_object* v_range_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_range_125_, v___x_126_);
v___x_128_ = l_List_toUnboundedSlice___redArg(v_xs_124_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___lam__0___boxed(lean_object* v_xs_129_, lean_object* v_range_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_instSliceableListNatListSlice__5___redArg___lam__0(v_xs_129_, v_range_130_);
lean_dec(v_range_130_);
lean_dec(v_xs_129_);
return v_res_131_;
}
}
lean_object* l_instSliceableListNatListSlice__5___redArg(){
_start:
{
lean_object* v___f_134_; 
v___f_134_ = ((lean_object*)(l_instSliceableListNatListSlice__5___redArg___closed__0));
return v___f_134_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_135_;
v_res_135_ = l_instSliceableListNatListSlice__5___redArg();
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5___redArg___boxed(lean_object* v___dummy_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_instSliceableListNatListSlice__5___redArg();
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__5(lean_object* v_00_u03b1_138_){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = ((lean_object*)(l_instSliceableListNatListSlice__5___redArg___closed__0));
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___lam__0(lean_object* v_xs_140_, lean_object* v_range_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v_range_141_, v___x_143_);
v___x_145_ = l_List_toSlice___redArg(v_xs_140_, v___x_142_, v___x_144_);
lean_dec(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___lam__0___boxed(lean_object* v_xs_146_, lean_object* v_range_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_instSliceableListNatListSlice__6___redArg___lam__0(v_xs_146_, v_range_147_);
lean_dec(v_range_147_);
lean_dec(v_xs_146_);
return v_res_148_;
}
}
lean_object* l_instSliceableListNatListSlice__6___redArg(){
_start:
{
lean_object* v___f_151_; 
v___f_151_ = ((lean_object*)(l_instSliceableListNatListSlice__6___redArg___closed__0));
return v___f_151_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_152_;
v_res_152_ = l_instSliceableListNatListSlice__6___redArg();
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6___redArg___boxed(lean_object* v___dummy_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_instSliceableListNatListSlice__6___redArg();
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__6(lean_object* v_00_u03b1_155_){
_start:
{
lean_object* v___f_156_; 
v___f_156_ = ((lean_object*)(l_instSliceableListNatListSlice__6___redArg___closed__0));
return v___f_156_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___lam__0(lean_object* v_xs_157_, lean_object* v_range_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = l_List_toSlice___redArg(v_xs_157_, v___x_159_, v_range_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___lam__0___boxed(lean_object* v_xs_161_, lean_object* v_range_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_instSliceableListNatListSlice__7___redArg___lam__0(v_xs_161_, v_range_162_);
lean_dec(v_range_162_);
lean_dec(v_xs_161_);
return v_res_163_;
}
}
lean_object* l_instSliceableListNatListSlice__7___redArg(){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = ((lean_object*)(l_instSliceableListNatListSlice__7___redArg___closed__0));
return v___f_166_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_167_;
v_res_167_ = l_instSliceableListNatListSlice__7___redArg();
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7___redArg___boxed(lean_object* v___dummy_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_instSliceableListNatListSlice__7___redArg();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__7(lean_object* v_00_u03b1_170_){
_start:
{
lean_object* v___f_171_; 
v___f_171_ = ((lean_object*)(l_instSliceableListNatListSlice__7___redArg___closed__0));
return v___f_171_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___lam__0(lean_object* v_xs_172_, lean_object* v_x_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_List_toUnboundedSlice___redArg(v_xs_172_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___lam__0___boxed(lean_object* v_xs_176_, lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_instSliceableListNatListSlice__8___redArg___lam__0(v_xs_176_, v_x_177_);
lean_dec(v_xs_176_);
return v_res_178_;
}
}
lean_object* l_instSliceableListNatListSlice__8___redArg(){
_start:
{
lean_object* v___f_181_; 
v___f_181_ = ((lean_object*)(l_instSliceableListNatListSlice__8___redArg___closed__0));
return v___f_181_;
}
}
LEAN_EXPORT void l_instSliceableListNatListSlice__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_182_;
v_res_182_ = l_instSliceableListNatListSlice__8___redArg();
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8___redArg___boxed(lean_object* v___dummy_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_instSliceableListNatListSlice__8___redArg();
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListNatListSlice__8(lean_object* v_00_u03b1_185_){
_start:
{
lean_object* v___f_186_; 
v___f_186_ = ((lean_object*)(l_instSliceableListNatListSlice__8___redArg___closed__0));
return v___f_186_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg___lam__0(lean_object* v_xs_187_, lean_object* v_range_188_){
_start:
{
lean_object* v_list_189_; lean_object* v_stop_190_; lean_object* v___y_192_; 
v_list_189_ = lean_ctor_get(v_xs_187_, 0);
lean_inc(v_list_189_);
v_stop_190_ = lean_ctor_get(v_xs_187_, 1);
lean_inc(v_stop_190_);
lean_dec_ref(v_xs_187_);
if (lean_obj_tag(v_stop_190_) == 0)
{
lean_object* v_upper_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_upper_195_ = lean_ctor_get(v_range_188_, 1);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_upper_195_, v___x_196_);
v___y_192_ = v___x_197_;
goto v___jp_191_;
}
else
{
lean_object* v_val_198_; lean_object* v_upper_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_val_198_ = lean_ctor_get(v_stop_190_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v_stop_190_, 1);
v_upper_199_ = lean_ctor_get(v_range_188_, 1);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_upper_199_, v___x_200_);
v___x_202_ = lean_nat_dec_le(v_val_198_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec(v_val_198_);
v___y_192_ = v___x_201_;
goto v___jp_191_;
}
else
{
lean_dec(v___x_201_);
v___y_192_ = v_val_198_;
goto v___jp_191_;
}
}
v___jp_191_:
{
lean_object* v_lower_193_; lean_object* v___x_194_; 
v_lower_193_ = lean_ctor_get(v_range_188_, 0);
lean_inc(v_lower_193_);
lean_dec_ref(v_range_188_);
v___x_194_ = l_List_toSlice___redArg(v_list_189_, v_lower_193_, v___y_192_);
lean_dec(v___y_192_);
lean_dec(v_list_189_);
return v___x_194_;
}
}
}
lean_object* l_instSliceableListSliceNat___redArg(){
_start:
{
lean_object* v___f_205_; 
v___f_205_ = ((lean_object*)(l_instSliceableListSliceNat___redArg___closed__0));
return v___f_205_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_206_;
v_res_206_ = l_instSliceableListSliceNat___redArg();
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat___redArg___boxed(lean_object* v___dummy_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_instSliceableListSliceNat___redArg();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat(lean_object* v_00_u03b1_209_){
_start:
{
lean_object* v___f_210_; 
v___f_210_ = ((lean_object*)(l_instSliceableListSliceNat___redArg___closed__0));
return v___f_210_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg___lam__0(lean_object* v_xs_211_, lean_object* v_range_212_){
_start:
{
lean_object* v_list_213_; lean_object* v_stop_214_; lean_object* v___y_216_; 
v_list_213_ = lean_ctor_get(v_xs_211_, 0);
lean_inc(v_list_213_);
v_stop_214_ = lean_ctor_get(v_xs_211_, 1);
lean_inc(v_stop_214_);
lean_dec_ref(v_xs_211_);
if (lean_obj_tag(v_stop_214_) == 0)
{
lean_object* v_upper_219_; 
v_upper_219_ = lean_ctor_get(v_range_212_, 1);
lean_inc(v_upper_219_);
v___y_216_ = v_upper_219_;
goto v___jp_215_;
}
else
{
lean_object* v_val_220_; lean_object* v_upper_221_; uint8_t v___x_222_; 
v_val_220_ = lean_ctor_get(v_stop_214_, 0);
lean_inc(v_val_220_);
lean_dec_ref_known(v_stop_214_, 1);
v_upper_221_ = lean_ctor_get(v_range_212_, 1);
v___x_222_ = lean_nat_dec_le(v_val_220_, v_upper_221_);
if (v___x_222_ == 0)
{
lean_dec(v_val_220_);
lean_inc(v_upper_221_);
v___y_216_ = v_upper_221_;
goto v___jp_215_;
}
else
{
v___y_216_ = v_val_220_;
goto v___jp_215_;
}
}
v___jp_215_:
{
lean_object* v_lower_217_; lean_object* v___x_218_; 
v_lower_217_ = lean_ctor_get(v_range_212_, 0);
lean_inc(v_lower_217_);
lean_dec_ref(v_range_212_);
v___x_218_ = l_List_toSlice___redArg(v_list_213_, v_lower_217_, v___y_216_);
lean_dec(v___y_216_);
lean_dec(v_list_213_);
return v___x_218_;
}
}
}
lean_object* l_instSliceableListSliceNat__1___redArg(){
_start:
{
lean_object* v___f_225_; 
v___f_225_ = ((lean_object*)(l_instSliceableListSliceNat__1___redArg___closed__0));
return v___f_225_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_226_;
v_res_226_ = l_instSliceableListSliceNat__1___redArg();
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1___redArg___boxed(lean_object* v___dummy_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_instSliceableListSliceNat__1___redArg();
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__1(lean_object* v_00_u03b1_229_){
_start:
{
lean_object* v___f_230_; 
v___f_230_ = ((lean_object*)(l_instSliceableListSliceNat__1___redArg___closed__0));
return v___f_230_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___lam__0(lean_object* v_xs_231_, lean_object* v_range_232_){
_start:
{
lean_object* v_stop_233_; 
v_stop_233_ = lean_ctor_get(v_xs_231_, 1);
if (lean_obj_tag(v_stop_233_) == 0)
{
lean_object* v_list_234_; lean_object* v___x_235_; 
v_list_234_ = lean_ctor_get(v_xs_231_, 0);
v___x_235_ = l_List_toUnboundedSlice___redArg(v_list_234_, v_range_232_);
return v___x_235_;
}
else
{
lean_object* v_list_236_; lean_object* v_val_237_; lean_object* v___x_238_; 
v_list_236_ = lean_ctor_get(v_xs_231_, 0);
v_val_237_ = lean_ctor_get(v_stop_233_, 0);
v___x_238_ = l_List_toSlice___redArg(v_list_236_, v_range_232_, v_val_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___lam__0___boxed(lean_object* v_xs_239_, lean_object* v_range_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_instSliceableListSliceNat__2___redArg___lam__0(v_xs_239_, v_range_240_);
lean_dec_ref(v_xs_239_);
return v_res_241_;
}
}
lean_object* l_instSliceableListSliceNat__2___redArg(){
_start:
{
lean_object* v___f_244_; 
v___f_244_ = ((lean_object*)(l_instSliceableListSliceNat__2___redArg___closed__0));
return v___f_244_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_245_;
v_res_245_ = l_instSliceableListSliceNat__2___redArg();
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2___redArg___boxed(lean_object* v___dummy_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_instSliceableListSliceNat__2___redArg();
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__2(lean_object* v_00_u03b1_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = ((lean_object*)(l_instSliceableListSliceNat__2___redArg___closed__0));
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___lam__0(lean_object* v_xs_250_, lean_object* v_range_251_){
_start:
{
lean_object* v_list_252_; lean_object* v_stop_253_; lean_object* v___y_255_; 
v_list_252_ = lean_ctor_get(v_xs_250_, 0);
lean_inc(v_list_252_);
v_stop_253_ = lean_ctor_get(v_xs_250_, 1);
lean_inc(v_stop_253_);
lean_dec_ref(v_xs_250_);
if (lean_obj_tag(v_stop_253_) == 0)
{
lean_object* v_upper_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_upper_260_ = lean_ctor_get(v_range_251_, 1);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_upper_260_, v___x_261_);
v___y_255_ = v___x_262_;
goto v___jp_254_;
}
else
{
lean_object* v_val_263_; lean_object* v_upper_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_val_263_ = lean_ctor_get(v_stop_253_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v_stop_253_, 1);
v_upper_264_ = lean_ctor_get(v_range_251_, 1);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_upper_264_, v___x_265_);
v___x_267_ = lean_nat_dec_le(v_val_263_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_val_263_);
v___y_255_ = v___x_266_;
goto v___jp_254_;
}
else
{
lean_dec(v___x_266_);
v___y_255_ = v_val_263_;
goto v___jp_254_;
}
}
v___jp_254_:
{
lean_object* v_lower_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_lower_256_ = lean_ctor_get(v_range_251_, 0);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_lower_256_, v___x_257_);
v___x_259_ = l_List_toSlice___redArg(v_list_252_, v___x_258_, v___y_255_);
lean_dec(v___y_255_);
lean_dec(v_list_252_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___lam__0___boxed(lean_object* v_xs_268_, lean_object* v_range_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_instSliceableListSliceNat__3___redArg___lam__0(v_xs_268_, v_range_269_);
lean_dec_ref(v_range_269_);
return v_res_270_;
}
}
lean_object* l_instSliceableListSliceNat__3___redArg(){
_start:
{
lean_object* v___f_273_; 
v___f_273_ = ((lean_object*)(l_instSliceableListSliceNat__3___redArg___closed__0));
return v___f_273_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_274_;
v_res_274_ = l_instSliceableListSliceNat__3___redArg();
stack->m_obj
 = v_res_274_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3___redArg___boxed(lean_object* v___dummy_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_instSliceableListSliceNat__3___redArg();
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__3(lean_object* v_00_u03b1_277_){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = ((lean_object*)(l_instSliceableListSliceNat__3___redArg___closed__0));
return v___f_278_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___lam__0(lean_object* v_xs_279_, lean_object* v_range_280_){
_start:
{
lean_object* v_list_281_; lean_object* v_stop_282_; lean_object* v___y_284_; 
v_list_281_ = lean_ctor_get(v_xs_279_, 0);
v_stop_282_ = lean_ctor_get(v_xs_279_, 1);
if (lean_obj_tag(v_stop_282_) == 0)
{
lean_object* v_upper_289_; 
v_upper_289_ = lean_ctor_get(v_range_280_, 1);
v___y_284_ = v_upper_289_;
goto v___jp_283_;
}
else
{
lean_object* v_val_290_; lean_object* v_upper_291_; uint8_t v___x_292_; 
v_val_290_ = lean_ctor_get(v_stop_282_, 0);
v_upper_291_ = lean_ctor_get(v_range_280_, 1);
v___x_292_ = lean_nat_dec_le(v_val_290_, v_upper_291_);
if (v___x_292_ == 0)
{
v___y_284_ = v_upper_291_;
goto v___jp_283_;
}
else
{
v___y_284_ = v_val_290_;
goto v___jp_283_;
}
}
v___jp_283_:
{
lean_object* v_lower_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_lower_285_ = lean_ctor_get(v_range_280_, 0);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_lower_285_, v___x_286_);
v___x_288_ = l_List_toSlice___redArg(v_list_281_, v___x_287_, v___y_284_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___lam__0___boxed(lean_object* v_xs_293_, lean_object* v_range_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_instSliceableListSliceNat__4___redArg___lam__0(v_xs_293_, v_range_294_);
lean_dec_ref(v_range_294_);
lean_dec_ref(v_xs_293_);
return v_res_295_;
}
}
lean_object* l_instSliceableListSliceNat__4___redArg(){
_start:
{
lean_object* v___f_298_; 
v___f_298_ = ((lean_object*)(l_instSliceableListSliceNat__4___redArg___closed__0));
return v___f_298_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_299_;
v_res_299_ = l_instSliceableListSliceNat__4___redArg();
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4___redArg___boxed(lean_object* v___dummy_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_instSliceableListSliceNat__4___redArg();
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__4(lean_object* v_00_u03b1_302_){
_start:
{
lean_object* v___f_303_; 
v___f_303_ = ((lean_object*)(l_instSliceableListSliceNat__4___redArg___closed__0));
return v___f_303_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___lam__0(lean_object* v_xs_304_, lean_object* v_range_305_){
_start:
{
lean_object* v_stop_306_; 
v_stop_306_ = lean_ctor_get(v_xs_304_, 1);
if (lean_obj_tag(v_stop_306_) == 0)
{
lean_object* v_list_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_list_307_ = lean_ctor_get(v_xs_304_, 0);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_range_305_, v___x_308_);
v___x_310_ = l_List_toUnboundedSlice___redArg(v_list_307_, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v_list_311_; lean_object* v_val_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_list_311_ = lean_ctor_get(v_xs_304_, 0);
v_val_312_ = lean_ctor_get(v_stop_306_, 0);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_range_305_, v___x_313_);
v___x_315_ = l_List_toSlice___redArg(v_list_311_, v___x_314_, v_val_312_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___lam__0___boxed(lean_object* v_xs_316_, lean_object* v_range_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_instSliceableListSliceNat__5___redArg___lam__0(v_xs_316_, v_range_317_);
lean_dec(v_range_317_);
lean_dec_ref(v_xs_316_);
return v_res_318_;
}
}
lean_object* l_instSliceableListSliceNat__5___redArg(){
_start:
{
lean_object* v___f_321_; 
v___f_321_ = ((lean_object*)(l_instSliceableListSliceNat__5___redArg___closed__0));
return v___f_321_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_322_;
v_res_322_ = l_instSliceableListSliceNat__5___redArg();
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5___redArg___boxed(lean_object* v___dummy_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_instSliceableListSliceNat__5___redArg();
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__5(lean_object* v_00_u03b1_325_){
_start:
{
lean_object* v___f_326_; 
v___f_326_ = ((lean_object*)(l_instSliceableListSliceNat__5___redArg___closed__0));
return v___f_326_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___lam__0(lean_object* v_xs_327_, lean_object* v_range_328_){
_start:
{
lean_object* v_list_329_; lean_object* v_stop_330_; lean_object* v___y_332_; 
v_list_329_ = lean_ctor_get(v_xs_327_, 0);
lean_inc(v_list_329_);
v_stop_330_ = lean_ctor_get(v_xs_327_, 1);
lean_inc(v_stop_330_);
lean_dec_ref(v_xs_327_);
if (lean_obj_tag(v_stop_330_) == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_range_328_, v___x_335_);
v___y_332_ = v___x_336_;
goto v___jp_331_;
}
else
{
lean_object* v_val_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_val_337_ = lean_ctor_get(v_stop_330_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v_stop_330_, 1);
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_range_328_, v___x_338_);
v___x_340_ = lean_nat_dec_le(v_val_337_, v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v_val_337_);
v___y_332_ = v___x_339_;
goto v___jp_331_;
}
else
{
lean_dec(v___x_339_);
v___y_332_ = v_val_337_;
goto v___jp_331_;
}
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = l_List_toSlice___redArg(v_list_329_, v___x_333_, v___y_332_);
lean_dec(v___y_332_);
lean_dec(v_list_329_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___lam__0___boxed(lean_object* v_xs_341_, lean_object* v_range_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_instSliceableListSliceNat__6___redArg___lam__0(v_xs_341_, v_range_342_);
lean_dec(v_range_342_);
return v_res_343_;
}
}
lean_object* l_instSliceableListSliceNat__6___redArg(){
_start:
{
lean_object* v___f_346_; 
v___f_346_ = ((lean_object*)(l_instSliceableListSliceNat__6___redArg___closed__0));
return v___f_346_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_347_;
v_res_347_ = l_instSliceableListSliceNat__6___redArg();
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6___redArg___boxed(lean_object* v___dummy_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_instSliceableListSliceNat__6___redArg();
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__6(lean_object* v_00_u03b1_350_){
_start:
{
lean_object* v___f_351_; 
v___f_351_ = ((lean_object*)(l_instSliceableListSliceNat__6___redArg___closed__0));
return v___f_351_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___lam__0(lean_object* v_xs_352_, lean_object* v_range_353_){
_start:
{
lean_object* v_list_354_; lean_object* v_stop_355_; lean_object* v___y_357_; 
v_list_354_ = lean_ctor_get(v_xs_352_, 0);
v_stop_355_ = lean_ctor_get(v_xs_352_, 1);
if (lean_obj_tag(v_stop_355_) == 0)
{
v___y_357_ = v_range_353_;
goto v___jp_356_;
}
else
{
lean_object* v_val_360_; uint8_t v___x_361_; 
v_val_360_ = lean_ctor_get(v_stop_355_, 0);
v___x_361_ = lean_nat_dec_le(v_val_360_, v_range_353_);
if (v___x_361_ == 0)
{
v___y_357_ = v_range_353_;
goto v___jp_356_;
}
else
{
v___y_357_ = v_val_360_;
goto v___jp_356_;
}
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = l_List_toSlice___redArg(v_list_354_, v___x_358_, v___y_357_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___lam__0___boxed(lean_object* v_xs_362_, lean_object* v_range_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_instSliceableListSliceNat__7___redArg___lam__0(v_xs_362_, v_range_363_);
lean_dec(v_range_363_);
lean_dec_ref(v_xs_362_);
return v_res_364_;
}
}
lean_object* l_instSliceableListSliceNat__7___redArg(){
_start:
{
lean_object* v___f_367_; 
v___f_367_ = ((lean_object*)(l_instSliceableListSliceNat__7___redArg___closed__0));
return v___f_367_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_368_;
v_res_368_ = l_instSliceableListSliceNat__7___redArg();
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7___redArg___boxed(lean_object* v___dummy_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_instSliceableListSliceNat__7___redArg();
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__7(lean_object* v_00_u03b1_371_){
_start:
{
lean_object* v___f_372_; 
v___f_372_ = ((lean_object*)(l_instSliceableListSliceNat__7___redArg___closed__0));
return v___f_372_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___lam__0(lean_object* v_xs_373_, lean_object* v_x_374_){
_start:
{
lean_inc_ref(v_xs_373_);
return v_xs_373_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___lam__0___boxed(lean_object* v_xs_375_, lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_instSliceableListSliceNat__8___redArg___lam__0(v_xs_375_, v_x_376_);
lean_dec_ref(v_xs_375_);
return v_res_377_;
}
}
lean_object* l_instSliceableListSliceNat__8___redArg(){
_start:
{
lean_object* v___f_380_; 
v___f_380_ = ((lean_object*)(l_instSliceableListSliceNat__8___redArg___closed__0));
return v___f_380_;
}
}
LEAN_EXPORT void l_instSliceableListSliceNat__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_381_;
v_res_381_ = l_instSliceableListSliceNat__8___redArg();
stack->m_obj
 = v_res_381_;
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8___redArg___boxed(lean_object* v___dummy_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_instSliceableListSliceNat__8___redArg();
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_instSliceableListSliceNat__8(lean_object* v_00_u03b1_384_){
_start:
{
lean_object* v___f_385_; 
v___f_385_ = ((lean_object*)(l_instSliceableListSliceNat__8___redArg___closed__0));
return v___f_385_;
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
