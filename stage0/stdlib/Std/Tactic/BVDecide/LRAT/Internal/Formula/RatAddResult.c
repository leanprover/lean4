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
lean_object* v_clauses_12_; lean_object* v_rupUnits_13_; lean_object* v_ratUnits_14_; lean_object* v_assignments_15_; lean_object* v___x_16_; 
v_clauses_12_ = lean_ctor_get(v_f_10_, 0);
lean_inc_ref(v_clauses_12_);
v_rupUnits_13_ = lean_ctor_get(v_f_10_, 1);
lean_inc_ref(v_rupUnits_13_);
v_ratUnits_14_ = lean_ctor_get(v_f_10_, 2);
lean_inc_ref(v_ratUnits_14_);
v_assignments_15_ = lean_ctor_get(v_f_10_, 3);
lean_inc_ref(v_assignments_15_);
lean_dec_ref(v_f_10_);
v___x_16_ = lean_apply_4(v_h__1_11_, v_clauses_12_, v_rupUnits_13_, v_ratUnits_14_, v_assignments_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object* v_n_17_, lean_object* v_motive_18_, lean_object* v_f_19_, lean_object* v_h__1_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_17_, v_motive_18_, v_f_19_, v_h__1_20_);
lean_dec(v_n_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___redArg(lean_object* v_f_22_, lean_object* v_ratHint_23_, lean_object* v_h__1_24_){
_start:
{
lean_object* v_clauses_25_; lean_object* v_rupUnits_26_; lean_object* v_ratUnits_27_; lean_object* v_assignments_28_; lean_object* v_fst_29_; lean_object* v_snd_30_; lean_object* v___x_31_; 
v_clauses_25_ = lean_ctor_get(v_f_22_, 0);
lean_inc_ref(v_clauses_25_);
v_rupUnits_26_ = lean_ctor_get(v_f_22_, 1);
lean_inc_ref(v_rupUnits_26_);
v_ratUnits_27_ = lean_ctor_get(v_f_22_, 2);
lean_inc_ref(v_ratUnits_27_);
v_assignments_28_ = lean_ctor_get(v_f_22_, 3);
lean_inc_ref(v_assignments_28_);
lean_dec_ref(v_f_22_);
v_fst_29_ = lean_ctor_get(v_ratHint_23_, 0);
lean_inc(v_fst_29_);
v_snd_30_ = lean_ctor_get(v_ratHint_23_, 1);
lean_inc(v_snd_30_);
lean_dec_ref(v_ratHint_23_);
v___x_31_ = lean_apply_6(v_h__1_24_, v_clauses_25_, v_rupUnits_26_, v_ratUnits_27_, v_assignments_28_, v_fst_29_, v_snd_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(lean_object* v_n_32_, lean_object* v_motive_33_, lean_object* v_f_34_, lean_object* v_ratHint_35_, lean_object* v_h__1_36_){
_start:
{
lean_object* v_clauses_37_; lean_object* v_rupUnits_38_; lean_object* v_ratUnits_39_; lean_object* v_assignments_40_; lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_43_; 
v_clauses_37_ = lean_ctor_get(v_f_34_, 0);
lean_inc_ref(v_clauses_37_);
v_rupUnits_38_ = lean_ctor_get(v_f_34_, 1);
lean_inc_ref(v_rupUnits_38_);
v_ratUnits_39_ = lean_ctor_get(v_f_34_, 2);
lean_inc_ref(v_ratUnits_39_);
v_assignments_40_ = lean_ctor_get(v_f_34_, 3);
lean_inc_ref(v_assignments_40_);
lean_dec_ref(v_f_34_);
v_fst_41_ = lean_ctor_get(v_ratHint_35_, 0);
lean_inc(v_fst_41_);
v_snd_42_ = lean_ctor_get(v_ratHint_35_, 1);
lean_inc(v_snd_42_);
lean_dec_ref(v_ratHint_35_);
v___x_43_ = lean_apply_6(v_h__1_36_, v_clauses_37_, v_rupUnits_38_, v_ratUnits_39_, v_assignments_40_, v_fst_41_, v_snd_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___boxed(lean_object* v_n_44_, lean_object* v_motive_45_, lean_object* v_f_46_, lean_object* v_ratHint_47_, lean_object* v_h__1_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(v_n_44_, v_motive_45_, v_f_46_, v_ratHint_47_, v_h__1_48_);
lean_dec(v_n_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___redArg(lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_51_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__2_52_, v___x_53_);
return v___x_54_;
}
else
{
lean_object* v_val_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_52_);
v_val_55_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_val_55_);
lean_dec_ref(v_x_50_);
v___x_56_ = lean_apply_1(v_h__1_51_, v_val_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(lean_object* v_n_57_, lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_60_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__2_61_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v_val_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_61_);
v_val_64_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_val_64_);
lean_dec_ref(v_x_59_);
v___x_65_ = lean_apply_1(v_h__1_60_, v_val_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___boxed(lean_object* v_n_66_, lean_object* v_motive_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(v_n_66_, v_motive_67_, v_x_68_, v_h__1_69_, v_h__2_70_);
lean_dec(v_n_66_);
return v_res_71_;
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
