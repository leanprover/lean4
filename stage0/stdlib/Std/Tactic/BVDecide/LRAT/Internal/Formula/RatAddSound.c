// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult import Init.ByCases import Init.Data.Array.Range import Init.Data.Int.OfNat import Init.Data.Nat.Linear
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(uint8_t v_a_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_, lean_object* v_h__4_5_){
_start:
{
switch(v_a_1_)
{
case 0:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
case 1:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v___x_8_ = lean_box(0);
v___x_9_ = lean_apply_1(v_h__2_3_, v___x_8_);
return v___x_9_;
}
case 2:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_apply_1(v_h__3_4_, v___x_10_);
return v___x_11_;
}
default: 
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_12_ = lean_box(0);
v___x_13_ = lean_apply_1(v_h__4_5_, v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(lean_object* v_a_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_, lean_object* v_h__3_17_, lean_object* v_h__4_18_){
_start:
{
uint8_t v_a_46__boxed_19_; lean_object* v_res_20_; 
v_a_46__boxed_19_ = lean_unbox(v_a_14_);
v_res_20_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_19_, v_h__1_15_, v_h__2_16_, v_h__3_17_, v_h__4_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object* v_motive_21_, uint8_t v_a_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_, lean_object* v_h__3_25_, lean_object* v_h__4_26_){
_start:
{
switch(v_a_22_)
{
case 0:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_h__4_26_);
lean_dec(v_h__3_25_);
lean_dec(v_h__2_24_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_apply_1(v_h__1_23_, v___x_27_);
return v___x_28_;
}
case 1:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_h__4_26_);
lean_dec(v_h__3_25_);
lean_dec(v_h__1_23_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_apply_1(v_h__2_24_, v___x_29_);
return v___x_30_;
}
case 2:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__4_26_);
lean_dec(v_h__2_24_);
lean_dec(v_h__1_23_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_1(v_h__3_25_, v___x_31_);
return v___x_32_;
}
default: 
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_25_);
lean_dec(v_h__2_24_);
lean_dec(v_h__1_23_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__4_26_, v___x_33_);
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object* v_motive_35_, lean_object* v_a_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_, lean_object* v_h__3_39_, lean_object* v_h__4_40_){
_start:
{
uint8_t v_a_65__boxed_41_; lean_object* v_res_42_; 
v_a_65__boxed_41_ = lean_unbox(v_a_36_);
v_res_42_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_35_, v_a_65__boxed_41_, v_h__1_37_, v_h__2_38_, v_h__3_39_, v_h__4_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(lean_object* v_cOpt_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_cOpt_43_) == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_45_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_apply_1(v_h__1_44_, v___x_46_);
return v___x_47_;
}
else
{
lean_object* v_val_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_44_);
v_val_48_ = lean_ctor_get(v_cOpt_43_, 0);
lean_inc(v_val_48_);
lean_dec_ref(v_cOpt_43_);
v___x_49_ = lean_apply_1(v_h__2_45_, v_val_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(lean_object* v_n_50_, lean_object* v_motive_51_, lean_object* v_cOpt_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_cOpt_52_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_54_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__1_53_, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v_val_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_53_);
v_val_57_ = lean_ctor_get(v_cOpt_52_, 0);
lean_inc(v_val_57_);
lean_dec_ref(v_cOpt_52_);
v___x_58_ = lean_apply_1(v_h__2_54_, v_val_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(lean_object* v_n_59_, lean_object* v_motive_60_, lean_object* v_cOpt_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(v_n_59_, v_motive_60_, v_cOpt_61_, v_h__1_62_, v_h__2_63_);
lean_dec(v_n_59_);
return v_res_64_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
}
#ifdef __cplusplus
}
#endif
