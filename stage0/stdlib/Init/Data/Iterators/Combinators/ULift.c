// Lean compiler output
// Module: Init.Data.Iterators.Combinators.ULift
// Imports: public import Init.Data.Iterators.Combinators.Monadic.ULift
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ULiftIterator_modifyStep___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ULiftIterator_modifyStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_uLift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_uLift___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_uLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_uLift___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ULiftIterator_modifyStep___redArg(lean_object* v_step_1_){
_start:
{
switch(lean_obj_tag(v_step_1_))
{
case 0:
{
lean_object* v_it_2_; lean_object* v_out_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_10_; 
v_it_2_ = lean_ctor_get(v_step_1_, 0);
v_out_3_ = lean_ctor_get(v_step_1_, 1);
v_isSharedCheck_10_ = !lean_is_exclusive(v_step_1_);
if (v_isSharedCheck_10_ == 0)
{
v___x_5_ = v_step_1_;
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_out_3_);
lean_inc(v_it_2_);
lean_dec(v_step_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_9_; 
v_reuseFailAlloc_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_9_, 0, v_it_2_);
lean_ctor_set(v_reuseFailAlloc_9_, 1, v_out_3_);
v___x_8_ = v_reuseFailAlloc_9_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
return v___x_8_;
}
}
}
case 1:
{
lean_object* v_it_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_it_11_ = lean_ctor_get(v_step_1_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v_step_1_);
if (v_isSharedCheck_18_ == 0)
{
v___x_13_ = v_step_1_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_it_11_);
lean_dec(v_step_1_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
if (v_isShared_14_ == 0)
{
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_it_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
default: 
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(2);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ULiftIterator_modifyStep(lean_object* v_00_u03b1_20_, lean_object* v_00_u03b2_21_, lean_object* v_step_22_){
_start:
{
switch(lean_obj_tag(v_step_22_))
{
case 0:
{
lean_object* v_it_23_; lean_object* v_out_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
v_it_23_ = lean_ctor_get(v_step_22_, 0);
v_out_24_ = lean_ctor_get(v_step_22_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_step_22_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v_step_22_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_out_24_);
lean_inc(v_it_23_);
lean_dec(v_step_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_it_23_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_out_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
case 1:
{
lean_object* v_it_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_it_32_ = lean_ctor_get(v_step_22_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v_step_22_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v_step_22_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_it_32_);
lean_dec(v_step_22_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_it_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
default: 
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(2);
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_uLift___redArg(lean_object* v_it_41_){
_start:
{
lean_inc(v_it_41_);
return v_it_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_uLift___redArg___boxed(lean_object* v_it_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Iter_uLift___redArg(v_it_42_);
lean_dec(v_it_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_uLift(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_it_46_){
_start:
{
lean_inc(v_it_46_);
return v_it_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_uLift___boxed(lean_object* v_00_u03b1_47_, lean_object* v_00_u03b2_48_, lean_object* v_it_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Iter_uLift(v_00_u03b1_47_, v_00_u03b2_48_, v_it_49_);
lean_dec(v_it_49_);
return v_res_50_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_ULift(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_ULift(builtin);
}
#ifdef __cplusplus
}
#endif
