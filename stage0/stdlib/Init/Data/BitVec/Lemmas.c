// Lean compiler output
// Module: Init.Data.BitVec.Lemmas
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.BitVec.BasicAux public import Init.Data.Fin.Lemmas public import Init.Data.List.BasicAux import Init.Data.List.Lemmas import Init.Data.List.TakeDrop import Init.Data.List.Nat.TakeDrop public import Init.Data.BitVec.Basic import Init.ByCases import Init.Data.BitVec.Bootstrap import Init.Data.Int.Bitwise.Lemmas import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Data.Nat.Simproc import Init.TacticsExtra
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_take___redArg(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenListFast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenListFast___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux(lean_object* v_n_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(0u);
return v___x_3_;
}
else
{
lean_object* v_tail_4_; 
v_tail_4_ = lean_ctor_get(v_x_2_, 1);
if (lean_obj_tag(v_tail_4_) == 0)
{
lean_object* v_head_5_; 
v_head_5_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_5_);
lean_dec_ref_known(v_x_2_, 2);
return v_head_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_mid_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_6_ = l_List_lengthTR___redArg(v_x_2_);
v___x_7_ = lean_unsigned_to_nat(1u);
v_mid_8_ = lean_nat_shiftr(v___x_6_, v___x_7_);
lean_dec(v___x_6_);
lean_inc_ref(v_x_2_);
v___x_9_ = l_List_take___redArg(v_mid_8_, v_x_2_);
v___x_10_ = l_BitVec_flattenList_toNatAux(v_n_1_, v___x_9_);
v___x_11_ = l_List_drop___redArg(v_mid_8_, v_x_2_);
lean_dec_ref_known(v_x_2_, 2);
v___x_12_ = l_List_lengthTR___redArg(v___x_11_);
v___x_13_ = lean_nat_mul(v_n_1_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_nat_shiftl(v___x_10_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_10_);
v___x_15_ = l_BitVec_flattenList_toNatAux(v_n_1_, v___x_11_);
v___x_16_ = lean_nat_lor(v___x_14_, v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_14_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux___boxed(lean_object* v_n_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_BitVec_flattenList_toNatAux(v_n_17_, v_x_18_);
lean_dec(v_n_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___redArg(lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_, lean_object* v_h__3_23_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__3_23_);
lean_dec(v_h__2_22_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__1_21_, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_tail_26_; 
lean_dec(v_h__1_21_);
v_tail_26_ = lean_ctor_get(v_x_20_, 1);
if (lean_obj_tag(v_tail_26_) == 0)
{
lean_object* v_head_27_; lean_object* v___x_28_; 
lean_dec(v_h__3_23_);
v_head_27_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_head_27_);
lean_dec_ref_known(v_x_20_, 2);
v___x_28_ = lean_apply_1(v_h__2_22_, v_head_27_);
return v___x_28_;
}
else
{
lean_object* v_head_29_; lean_object* v_head_30_; lean_object* v_tail_31_; lean_object* v___x_32_; 
lean_inc_ref(v_tail_26_);
lean_dec(v_h__2_22_);
v_head_29_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_head_29_);
lean_dec_ref_known(v_x_20_, 2);
v_head_30_ = lean_ctor_get(v_tail_26_, 0);
lean_inc(v_head_30_);
v_tail_31_ = lean_ctor_get(v_tail_26_, 1);
lean_inc(v_tail_31_);
lean_dec_ref_known(v_tail_26_, 2);
v___x_32_ = lean_apply_3(v_h__3_23_, v_head_29_, v_head_30_, v_tail_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(lean_object* v_n_33_, lean_object* v_motive_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__3_38_);
lean_dec(v_h__2_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__1_36_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_tail_41_; 
lean_dec(v_h__1_36_);
v_tail_41_ = lean_ctor_get(v_x_35_, 1);
if (lean_obj_tag(v_tail_41_) == 0)
{
lean_object* v_head_42_; lean_object* v___x_43_; 
lean_dec(v_h__3_38_);
v_head_42_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_head_42_);
lean_dec_ref_known(v_x_35_, 2);
v___x_43_ = lean_apply_1(v_h__2_37_, v_head_42_);
return v___x_43_;
}
else
{
lean_object* v_head_44_; lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v___x_47_; 
lean_inc_ref(v_tail_41_);
lean_dec(v_h__2_37_);
v_head_44_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_head_44_);
lean_dec_ref_known(v_x_35_, 2);
v_head_45_ = lean_ctor_get(v_tail_41_, 0);
lean_inc(v_head_45_);
v_tail_46_ = lean_ctor_get(v_tail_41_, 1);
lean_inc(v_tail_46_);
lean_dec_ref_known(v_tail_41_, 2);
v___x_47_ = lean_apply_3(v_h__3_38_, v_head_44_, v_head_45_, v_tail_46_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___boxed(lean_object* v_n_48_, lean_object* v_motive_49_, lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_, lean_object* v_h__3_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(v_n_48_, v_motive_49_, v_x_50_, v_h__1_51_, v_h__2_52_, v_h__3_53_);
lean_dec(v_n_48_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast(lean_object* v_n_55_, lean_object* v_xs_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = l_List_lengthTR___redArg(v_xs_56_);
v___x_58_ = lean_nat_mul(v_n_55_, v___x_57_);
lean_dec(v___x_57_);
v___x_59_ = l_BitVec_flattenList_toNatAux(v_n_55_, v_xs_56_);
v___x_60_ = l_BitVec_ofNat(v___x_58_, v___x_59_);
lean_dec(v___x_59_);
lean_dec(v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast___boxed(lean_object* v_n_61_, lean_object* v_xs_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_BitVec_flattenListFast(v_n_61_, v_xs_62_);
lean_dec(v_n_61_);
return v_res_63_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
