// Lean compiler output
// Module: Init.Data.List.Nat.Basic
// Imports: public import Init.Data.List.MinMax import Init.Data.Bool import Init.Data.List.Count import Init.Data.Nat.Lemmas import Init.Data.Nat.Internal.Linear import Init.Data.Nat.MinMax import Init.Data.Option.Lemmas import Init.Omega
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_2_);
v_head_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_6_);
v_tail_7_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref_known(v_x_1_, 2);
v___x_8_ = lean_apply_2(v_h__2_3_, v_head_6_, v_tail_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_h__2_13_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_apply_1(v_h__1_12_, v___x_14_);
return v___x_15_;
}
else
{
lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_12_);
v_head_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_tail_17_);
lean_dec_ref_known(v_x_11_, 2);
v___x_18_ = lean_apply_2(v_h__2_13_, v_head_16_, v_tail_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_21_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_20_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v_val_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_20_);
v_val_24_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_val_24_);
lean_dec_ref_known(v_x_19_, 1);
v___x_25_ = lean_apply_1(v_h__2_21_, v_val_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__2_30_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_1(v_h__1_29_, v___x_31_);
return v___x_32_;
}
else
{
lean_object* v_val_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_29_);
v_val_33_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_val_33_);
lean_dec_ref_known(v_x_28_, 1);
v___x_34_ = lean_apply_1(v_h__2_30_, v_val_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_){
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
lean_object* v_head_44_; lean_object* v___x_45_; 
lean_inc(v_tail_41_);
lean_dec(v_h__2_37_);
v_head_44_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_head_44_);
lean_dec_ref_known(v_x_35_, 2);
v___x_45_ = lean_apply_3(v_h__3_38_, v_head_44_, v_tail_41_, lean_box(0));
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_46_, lean_object* v_motive_47_, lean_object* v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_apply_1(v_h__1_49_, v___x_52_);
return v___x_53_;
}
else
{
lean_object* v_tail_54_; 
lean_dec(v_h__1_49_);
v_tail_54_ = lean_ctor_get(v_x_48_, 1);
if (lean_obj_tag(v_tail_54_) == 0)
{
lean_object* v_head_55_; lean_object* v___x_56_; 
lean_dec(v_h__3_51_);
v_head_55_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_head_55_);
lean_dec_ref_known(v_x_48_, 2);
v___x_56_ = lean_apply_1(v_h__2_50_, v_head_55_);
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v___x_58_; 
lean_inc(v_tail_54_);
lean_dec(v_h__2_50_);
v_head_57_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_head_57_);
lean_dec_ref_known(v_x_48_, 2);
v___x_58_ = lean_apply_3(v_h__3_51_, v_head_57_, v_tail_54_, lean_box(0));
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter___redArg(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_64_; 
lean_dec(v_h__3_63_);
lean_dec(v_h__2_62_);
v___x_64_ = lean_apply_1(v_h__1_61_, v_x_60_);
return v___x_64_;
}
else
{
lean_object* v_head_65_; lean_object* v_tail_66_; lean_object* v_zero_67_; uint8_t v_isZero_68_; 
lean_dec(v_h__1_61_);
v_head_65_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_head_65_);
v_tail_66_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_tail_66_);
lean_dec_ref_known(v_x_59_, 2);
v_zero_67_ = lean_unsigned_to_nat(0u);
v_isZero_68_ = lean_nat_dec_eq(v_x_60_, v_zero_67_);
if (v_isZero_68_ == 1)
{
lean_object* v___x_69_; 
lean_dec(v_h__3_63_);
lean_dec(v_x_60_);
v___x_69_ = lean_apply_2(v_h__2_62_, v_head_65_, v_tail_66_);
return v___x_69_;
}
else
{
lean_object* v_one_70_; lean_object* v_n_71_; lean_object* v___x_72_; 
lean_dec(v_h__2_62_);
v_one_70_ = lean_unsigned_to_nat(1u);
v_n_71_ = lean_nat_sub(v_x_60_, v_one_70_);
lean_dec(v_x_60_);
v___x_72_ = lean_apply_3(v_h__3_63_, v_head_65_, v_tail_66_, v_n_71_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter(lean_object* v_00_u03b1_73_, lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_, lean_object* v_h__3_79_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_80_; 
lean_dec(v_h__3_79_);
lean_dec(v_h__2_78_);
v___x_80_ = lean_apply_1(v_h__1_77_, v_x_76_);
return v___x_80_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; lean_object* v_zero_83_; uint8_t v_isZero_84_; 
lean_dec(v_h__1_77_);
v_head_81_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_head_81_);
v_tail_82_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_tail_82_);
lean_dec_ref_known(v_x_75_, 2);
v_zero_83_ = lean_unsigned_to_nat(0u);
v_isZero_84_ = lean_nat_dec_eq(v_x_76_, v_zero_83_);
if (v_isZero_84_ == 1)
{
lean_object* v___x_85_; 
lean_dec(v_h__3_79_);
lean_dec(v_x_76_);
v___x_85_ = lean_apply_2(v_h__2_78_, v_head_81_, v_tail_82_);
return v___x_85_;
}
else
{
lean_object* v_one_86_; lean_object* v_n_87_; lean_object* v___x_88_; 
lean_dec(v_h__2_78_);
v_one_86_ = lean_unsigned_to_nat(1u);
v_n_87_ = lean_nat_sub(v_x_76_, v_one_86_);
lean_dec(v_x_76_);
v___x_88_ = lean_apply_3(v_h__3_79_, v_head_81_, v_tail_82_, v_n_87_);
return v___x_88_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
