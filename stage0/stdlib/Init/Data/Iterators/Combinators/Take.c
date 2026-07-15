// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Take
// Imports: public import Init.Data.Iterators.Combinators.Monadic.Take
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
LEAN_EXPORT lean_object* l_Std_Iter_take___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_take___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_take(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_take___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toTake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toTake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toTake___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_take___redArg(lean_object* v_n_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_add(v_n_1_, v___x_3_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v_it_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_take___redArg___boxed(lean_object* v_n_6_, lean_object* v_it_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_Iter_take___redArg(v_n_6_, v_it_7_);
lean_dec(v_n_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_take(lean_object* v_00_u03b1_9_, lean_object* v_00_u03b2_10_, lean_object* v_inst_11_, lean_object* v_n_12_, lean_object* v_it_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_add(v_n_12_, v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_it_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_take___boxed(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_inst_19_, lean_object* v_n_20_, lean_object* v_it_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Iter_take(v_00_u03b1_17_, v_00_u03b2_18_, v_inst_19_, v_n_20_, v_it_21_);
lean_dec(v_n_20_);
lean_dec(v_inst_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTake___redArg(lean_object* v_it_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v_it_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTake(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_it_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_it_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTake___boxed(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_it_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Iter_toTake(v_00_u03b1_33_, v_00_u03b2_34_, v_inst_35_, v_inst_36_, v_it_37_);
lean_dec(v_inst_35_);
return v_res_38_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Take(builtin);
}
#ifdef __cplusplus
}
#endif
