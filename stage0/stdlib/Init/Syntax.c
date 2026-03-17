// Lean compiler output
// Module: Init.Syntax
// Imports: public import Init.Prelude import Init.Data.Array.Set
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setArgs(lean_object* v_stx_1_, lean_object* v_args_2_){
_start:
{
if (lean_obj_tag(v_stx_1_) == 1)
{
lean_object* v_info_3_; lean_object* v_kind_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_info_3_ = lean_ctor_get(v_stx_1_, 0);
v_kind_4_ = lean_ctor_get(v_stx_1_, 1);
v_isSharedCheck_11_ = !lean_is_exclusive(v_stx_1_);
if (v_isSharedCheck_11_ == 0)
{
lean_object* v_unused_12_; 
v_unused_12_ = lean_ctor_get(v_stx_1_, 2);
lean_dec(v_unused_12_);
v___x_6_ = v_stx_1_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_kind_4_);
lean_inc(v_info_3_);
lean_dec(v_stx_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 2, v_args_2_);
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_info_3_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_kind_4_);
lean_ctor_set(v_reuseFailAlloc_10_, 2, v_args_2_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_dec_ref(v_args_2_);
return v_stx_1_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setArg(lean_object* v_stx_13_, lean_object* v_i_14_, lean_object* v_arg_15_){
_start:
{
if (lean_obj_tag(v_stx_13_) == 1)
{
lean_object* v_info_16_; lean_object* v_kind_17_; lean_object* v_args_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v_info_16_ = lean_ctor_get(v_stx_13_, 0);
v_kind_17_ = lean_ctor_get(v_stx_13_, 1);
v_args_18_ = lean_ctor_get(v_stx_13_, 2);
v___x_19_ = lean_array_get_size(v_args_18_);
v___x_20_ = lean_nat_dec_lt(v_i_14_, v___x_19_);
if (v___x_20_ == 0)
{
lean_dec(v_arg_15_);
return v_stx_13_;
}
else
{
lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
lean_inc_ref(v_args_18_);
lean_inc(v_kind_17_);
lean_inc(v_info_16_);
v_isSharedCheck_28_ = !lean_is_exclusive(v_stx_13_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; lean_object* v_unused_30_; lean_object* v_unused_31_; 
v_unused_29_ = lean_ctor_get(v_stx_13_, 2);
lean_dec(v_unused_29_);
v_unused_30_ = lean_ctor_get(v_stx_13_, 1);
lean_dec(v_unused_30_);
v_unused_31_ = lean_ctor_get(v_stx_13_, 0);
lean_dec(v_unused_31_);
v___x_22_ = v_stx_13_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_dec(v_stx_13_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = lean_array_fset(v_args_18_, v_i_14_, v_arg_15_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 2, v___x_24_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_info_16_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_kind_17_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_dec(v_arg_15_);
return v_stx_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setArg___boxed(lean_object* v_stx_32_, lean_object* v_i_33_, lean_object* v_arg_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Syntax_setArg(v_stx_32_, v_i_33_, v_arg_34_);
lean_dec(v_i_33_);
return v_res_35_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
