// Lean compiler output
// Module: Std.Data.Iterators.Combinators.DropWhile
// Imports: public import Std.Data.Iterators.Combinators.Monadic.DropWhile
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
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___redArg(uint8_t v_dropping_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3_, 0, v_it_2_);
lean_ctor_set_uint8(v___x_3_, sizeof(void*)*1, v_dropping_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___redArg___boxed(lean_object* v_dropping_4_, lean_object* v_it_5_){
_start:
{
uint8_t v_dropping_boxed_6_; lean_object* v_res_7_; 
v_dropping_boxed_6_ = lean_unbox(v_dropping_4_);
v_res_7_ = l_Std_Iter_Intermediate_dropWhile___redArg(v_dropping_boxed_6_, v_it_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile(lean_object* v_00_u03b2_8_, lean_object* v_00_u03b1_9_, lean_object* v_P_10_, uint8_t v_dropping_11_, lean_object* v_it_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_13_, 0, v_it_12_);
lean_ctor_set_uint8(v___x_13_, sizeof(void*)*1, v_dropping_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___boxed(lean_object* v_00_u03b2_14_, lean_object* v_00_u03b1_15_, lean_object* v_P_16_, lean_object* v_dropping_17_, lean_object* v_it_18_){
_start:
{
uint8_t v_dropping_boxed_19_; lean_object* v_res_20_; 
v_dropping_boxed_19_ = lean_unbox(v_dropping_17_);
v_res_20_ = l_Std_Iter_Intermediate_dropWhile(v_00_u03b2_14_, v_00_u03b1_15_, v_P_16_, v_dropping_boxed_19_, v_it_18_);
lean_dec_ref(v_P_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile___redArg(lean_object* v_it_21_){
_start:
{
uint8_t v___x_22_; lean_object* v___x_23_; 
v___x_22_ = 1;
v___x_23_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_23_, 0, v_it_21_);
lean_ctor_set_uint8(v___x_23_, sizeof(void*)*1, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_P_26_, lean_object* v_it_27_){
_start:
{
uint8_t v___x_28_; lean_object* v___x_29_; 
v___x_28_ = 1;
v___x_29_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_29_, 0, v_it_27_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*1, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_P_32_, lean_object* v_it_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Iter_dropWhile(v_00_u03b1_30_, v_00_u03b2_31_, v_P_32_, v_it_33_);
lean_dec_ref(v_P_32_);
return v_res_34_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
}
#ifdef __cplusplus
}
#endif
