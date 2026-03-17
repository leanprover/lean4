// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas public import Init.GrindInstances.ToInt import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Linear import Init.Data.Nat.Simproc
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; 
v_fst_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_x_2_);
v___x_6_ = lean_apply_3(v_h__1_3_, v_x_1_, v_fst_4_, v_snd_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(lean_object* v_n_7_, lean_object* v_motive_8_, lean_object* v_x_9_, lean_object* v_x_10_, lean_object* v_h__1_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(v_x_9_, v_x_10_, v_h__1_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___boxed(lean_object* v_n_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(v_n_13_, v_motive_14_, v_x_15_, v_x_16_, v_h__1_17_);
lean_dec(v_n_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object* v_f_19_, lean_object* v_h__1_20_){
_start:
{
lean_object* v_clauses_21_; lean_object* v_rupUnits_22_; lean_object* v_ratUnits_23_; lean_object* v_assignments_24_; lean_object* v___x_25_; 
v_clauses_21_ = lean_ctor_get(v_f_19_, 0);
lean_inc_ref(v_clauses_21_);
v_rupUnits_22_ = lean_ctor_get(v_f_19_, 1);
lean_inc_ref(v_rupUnits_22_);
v_ratUnits_23_ = lean_ctor_get(v_f_19_, 2);
lean_inc_ref(v_ratUnits_23_);
v_assignments_24_ = lean_ctor_get(v_f_19_, 3);
lean_inc_ref(v_assignments_24_);
lean_dec_ref(v_f_19_);
v___x_25_ = lean_apply_4(v_h__1_20_, v_clauses_21_, v_rupUnits_22_, v_ratUnits_23_, v_assignments_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object* v_n_26_, lean_object* v_motive_27_, lean_object* v_f_28_, lean_object* v_h__1_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(v_f_28_, v_h__1_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object* v_n_31_, lean_object* v_motive_32_, lean_object* v_f_33_, lean_object* v_h__1_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_31_, v_motive_32_, v_f_33_, v_h__1_34_);
lean_dec(v_n_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(lean_object* v_x_36_, lean_object* v_h__1_37_){
_start:
{
lean_object* v_snd_38_; lean_object* v_snd_39_; lean_object* v_fst_40_; lean_object* v_fst_41_; lean_object* v_fst_42_; lean_object* v_snd_43_; lean_object* v___x_44_; 
v_snd_38_ = lean_ctor_get(v_x_36_, 1);
lean_inc(v_snd_38_);
v_snd_39_ = lean_ctor_get(v_snd_38_, 1);
lean_inc(v_snd_39_);
v_fst_40_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_fst_40_);
lean_dec_ref(v_x_36_);
v_fst_41_ = lean_ctor_get(v_snd_38_, 0);
lean_inc(v_fst_41_);
lean_dec(v_snd_38_);
v_fst_42_ = lean_ctor_get(v_snd_39_, 0);
lean_inc(v_fst_42_);
v_snd_43_ = lean_ctor_get(v_snd_39_, 1);
lean_inc(v_snd_43_);
lean_dec(v_snd_39_);
v___x_44_ = lean_apply_4(v_h__1_37_, v_fst_40_, v_fst_41_, v_fst_42_, v_snd_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(lean_object* v_n_45_, lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_h__1_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(v_x_47_, v_h__1_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___boxed(lean_object* v_n_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(v_n_50_, v_motive_51_, v_x_52_, v_h__1_53_);
lean_dec(v_n_50_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_, lean_object* v_h__3_58_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_57_);
lean_dec(v_h__1_56_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__3_58_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_val_61_; 
lean_dec(v_h__3_58_);
v_val_61_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_61_);
lean_dec_ref(v_x_55_);
if (lean_obj_tag(v_val_61_) == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_56_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__2_57_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v_val_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_57_);
v_val_64_ = lean_ctor_get(v_val_61_, 0);
lean_inc(v_val_64_);
lean_dec_ref(v_val_61_);
v___x_65_ = lean_apply_1(v_h__1_56_, v_val_64_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object* v_n_66_, lean_object* v_motive_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(v_x_68_, v_h__1_69_, v_h__2_70_, v_h__3_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object* v_n_73_, lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_73_, v_motive_74_, v_x_75_, v_h__1_76_, v_h__2_77_, v_h__3_78_);
lean_dec(v_n_73_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_, lean_object* v_h__3_83_, lean_object* v_h__4_84_){
_start:
{
switch(lean_obj_tag(v_x_80_))
{
case 0:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_h__4_84_);
lean_dec(v_h__3_83_);
lean_dec(v_h__2_82_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_apply_1(v_h__1_81_, v___x_85_);
return v___x_86_;
}
case 1:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_h__4_84_);
lean_dec(v_h__3_83_);
lean_dec(v_h__1_81_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_apply_1(v_h__2_82_, v___x_87_);
return v___x_88_;
}
case 2:
{
lean_object* v_l_89_; lean_object* v_fst_90_; lean_object* v_snd_91_; lean_object* v___x_92_; 
lean_dec(v_h__4_84_);
lean_dec(v_h__2_82_);
lean_dec(v_h__1_81_);
v_l_89_ = lean_ctor_get(v_x_80_, 0);
lean_inc_ref(v_l_89_);
lean_dec_ref(v_x_80_);
v_fst_90_ = lean_ctor_get(v_l_89_, 0);
lean_inc(v_fst_90_);
v_snd_91_ = lean_ctor_get(v_l_89_, 1);
lean_inc(v_snd_91_);
lean_dec_ref(v_l_89_);
v___x_92_ = lean_apply_2(v_h__3_83_, v_fst_90_, v_snd_91_);
return v___x_92_;
}
default: 
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_h__3_83_);
lean_dec(v_h__2_82_);
lean_dec(v_h__1_81_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_apply_1(v_h__4_84_, v___x_93_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object* v_n_95_, lean_object* v_motive_96_, lean_object* v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_, lean_object* v_h__3_100_, lean_object* v_h__4_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(v_x_97_, v_h__1_98_, v_h__2_99_, v_h__3_100_, v_h__4_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object* v_n_103_, lean_object* v_motive_104_, lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_, lean_object* v_h__4_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_103_, v_motive_104_, v_x_105_, v_h__1_106_, v_h__2_107_, v_h__3_108_, v_h__4_109_);
lean_dec(v_n_103_);
return v_res_110_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
}
#ifdef __cplusplus
}
#endif
