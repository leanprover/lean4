// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound import Init.ByCases import Init.Data.Int.OfNat import Init.Data.Nat.Linear
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object* v_f_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v_clauses_3_; lean_object* v_rupUnits_4_; lean_object* v_ratUnits_5_; lean_object* v_assignments_6_; lean_object* v___x_7_; 
v_clauses_3_ = lean_ctor_get(v_f_1_, 0);
lean_inc_ref(v_clauses_3_);
v_rupUnits_4_ = lean_ctor_get(v_f_1_, 1);
lean_inc_ref(v_rupUnits_4_);
v_ratUnits_5_ = lean_ctor_get(v_f_1_, 2);
lean_inc_ref(v_ratUnits_5_);
v_assignments_6_ = lean_ctor_get(v_f_1_, 3);
lean_inc_ref(v_assignments_6_);
lean_dec_ref(v_f_1_);
v___x_7_ = lean_apply_4(v_h__1_2_, v_clauses_3_, v_rupUnits_4_, v_ratUnits_5_, v_assignments_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object* v_n_8_, lean_object* v_motive_9_, lean_object* v_f_10_, lean_object* v_h__1_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(v_f_10_, v_h__1_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object* v_n_13_, lean_object* v_motive_14_, lean_object* v_f_15_, lean_object* v_h__1_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_13_, v_motive_14_, v_f_15_, v_h__1_16_);
lean_dec(v_n_13_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___redArg(lean_object* v_f_18_, lean_object* v_ratHint_19_, lean_object* v_h__1_20_){
_start:
{
lean_object* v_clauses_21_; lean_object* v_rupUnits_22_; lean_object* v_ratUnits_23_; lean_object* v_assignments_24_; lean_object* v_fst_25_; lean_object* v_snd_26_; lean_object* v___x_27_; 
v_clauses_21_ = lean_ctor_get(v_f_18_, 0);
lean_inc_ref(v_clauses_21_);
v_rupUnits_22_ = lean_ctor_get(v_f_18_, 1);
lean_inc_ref(v_rupUnits_22_);
v_ratUnits_23_ = lean_ctor_get(v_f_18_, 2);
lean_inc_ref(v_ratUnits_23_);
v_assignments_24_ = lean_ctor_get(v_f_18_, 3);
lean_inc_ref(v_assignments_24_);
lean_dec_ref(v_f_18_);
v_fst_25_ = lean_ctor_get(v_ratHint_19_, 0);
lean_inc(v_fst_25_);
v_snd_26_ = lean_ctor_get(v_ratHint_19_, 1);
lean_inc(v_snd_26_);
lean_dec_ref(v_ratHint_19_);
v___x_27_ = lean_apply_6(v_h__1_20_, v_clauses_21_, v_rupUnits_22_, v_ratUnits_23_, v_assignments_24_, v_fst_25_, v_snd_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(lean_object* v_n_28_, lean_object* v_motive_29_, lean_object* v_f_30_, lean_object* v_ratHint_31_, lean_object* v_h__1_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___redArg(v_f_30_, v_ratHint_31_, v_h__1_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___boxed(lean_object* v_n_34_, lean_object* v_motive_35_, lean_object* v_f_36_, lean_object* v_ratHint_37_, lean_object* v_h__1_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(v_n_34_, v_motive_35_, v_f_36_, v_ratHint_37_, v_h__1_38_);
lean_dec(v_n_34_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___redArg(lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_41_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_apply_1(v_h__2_42_, v___x_43_);
return v___x_44_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_42_);
v_val_45_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_val_45_);
lean_dec_ref(v_x_40_);
v___x_46_ = lean_apply_1(v_h__1_41_, v_val_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(lean_object* v_n_47_, lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___redArg(v_x_49_, v_h__1_50_, v_h__2_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___boxed(lean_object* v_n_53_, lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(v_n_53_, v_motive_54_, v_x_55_, v_h__1_56_, v_h__2_57_);
lean_dec(v_n_53_);
return v_res_58_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
}
#ifdef __cplusplus
}
#endif
