// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Stream
// Imports: public import Init.Data.Stream public import Init.Data.Iterators.Consumers.Monadic.Access
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
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; lean_object* v_val_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v_val_4_ = lean_apply_2(v_inst_1_, v_it_2_, v___x_3_);
if (lean_obj_tag(v_val_4_) == 0)
{
lean_object* v_it_5_; lean_object* v_out_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_14_; 
v_it_5_ = lean_ctor_get(v_val_4_, 0);
v_out_6_ = lean_ctor_get(v_val_4_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_val_4_);
if (v_isSharedCheck_14_ == 0)
{
v___x_8_ = v_val_4_;
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_out_6_);
lean_inc(v_it_5_);
lean_dec(v_val_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_11_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_it_5_);
lean_ctor_set(v___x_8_, 0, v_out_6_);
v___x_11_ = v___x_8_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_out_6_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_it_5_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
lean_object* v___x_12_; 
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
}
else
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg(lean_object* v_inst_16_){
_start:
{
lean_object* v___f_17_; 
v___f_17_ = lean_alloc_closure((void*)(l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_17_, 0, v_inst_16_);
return v___f_17_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v___f_23_; 
v___f_23_ = lean_alloc_closure((void*)(l_Std_instStreamIterOfProductiveOfIteratorAccessId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_23_, 0, v_inst_22_);
return v___f_23_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamIterOfProductiveOfIteratorAccessId___boxed(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_instStreamIterOfProductiveOfIteratorAccessId(v_00_u03b1_24_, v_00_u03b2_25_, v_inst_26_, v_inst_27_, v_inst_28_);
lean_dec(v_inst_26_);
return v_res_29_;
}
}
lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Stream(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Stream(builtin);
}
#ifdef __cplusplus
}
#endif
