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
lean_object* l_Std_Iter_Intermediate_dropWhile___redArg(uint8_t v_dropping_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3_, 0, v_it_2_);
lean_ctor_set_uint8(v___x_3_, sizeof(void*)*1, v_dropping_1_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Iter_Intermediate_dropWhile___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_dropping_1_ = stack[0].m_num;
lean_object* v_it_2_ = stack[1].m_obj;
lean_object* v_res_4_;
v_res_4_ = l_Std_Iter_Intermediate_dropWhile___redArg(v_dropping_1_, v_it_2_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___redArg___boxed(lean_object* v_dropping_5_, lean_object* v_it_6_){
_start:
{
uint8_t v_dropping_boxed_7_; lean_object* v_res_8_; 
v_dropping_boxed_7_ = lean_unbox(v_dropping_5_);
v_res_8_ = l_Std_Iter_Intermediate_dropWhile___redArg(v_dropping_boxed_7_, v_it_6_);
return v_res_8_;
}
}
lean_object* l_Std_Iter_Intermediate_dropWhile(lean_object* v_00_u03b2_9_, lean_object* v_00_u03b1_10_, lean_object* v_P_11_, uint8_t v_dropping_12_, lean_object* v_it_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_14_, 0, v_it_13_);
lean_ctor_set_uint8(v___x_14_, sizeof(void*)*1, v_dropping_12_);
return v___x_14_;
}
}
LEAN_EXPORT void l_Std_Iter_Intermediate_dropWhile_0interp(lean_interpreter_value* stack)
{
lean_object* v_P_11_ = stack[2].m_obj;
uint8_t v_dropping_12_ = stack[3].m_num;
lean_object* v_it_13_ = stack[4].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Std_Iter_Intermediate_dropWhile(lean_box(0), lean_box(0), v_P_11_, v_dropping_12_, v_it_13_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_dropWhile___boxed(lean_object* v_00_u03b2_16_, lean_object* v_00_u03b1_17_, lean_object* v_P_18_, lean_object* v_dropping_19_, lean_object* v_it_20_){
_start:
{
uint8_t v_dropping_boxed_21_; lean_object* v_res_22_; 
v_dropping_boxed_21_ = lean_unbox(v_dropping_19_);
v_res_22_ = l_Std_Iter_Intermediate_dropWhile(v_00_u03b2_16_, v_00_u03b1_17_, v_P_18_, v_dropping_boxed_21_, v_it_20_);
lean_dec_ref(v_P_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile___redArg(lean_object* v_it_23_){
_start:
{
uint8_t v___x_24_; lean_object* v___x_25_; 
v___x_24_ = 1;
v___x_25_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_25_, 0, v_it_23_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*1, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_P_28_, lean_object* v_it_29_){
_start:
{
uint8_t v___x_30_; lean_object* v___x_31_; 
v___x_30_ = 1;
v___x_31_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_31_, 0, v_it_29_);
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*1, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_dropWhile___boxed(lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_P_34_, lean_object* v_it_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Iter_dropWhile(v_00_u03b1_32_, v_00_u03b2_33_, v_P_34_, v_it_35_);
lean_dec_ref(v_P_34_);
return v_res_36_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
