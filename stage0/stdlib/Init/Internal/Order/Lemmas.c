// Lean compiler output
// Module: Init.Internal.Order.Lemmas
// Imports: import all Init.Data.List.Control import all Init.Data.Option.Basic import all Init.Data.Array.Basic public import Init.Internal.Order.Basic public import Init.Data.List.Monadic import Init.Data.Array.Bootstrap
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
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_i_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_i_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_i_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* v_i_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_i_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b1_14_, lean_object* v_as_15_, lean_object* v_motive_16_, lean_object* v_i_17_, lean_object* v_h_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_17_, v_h__1_19_, v_h__2_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_as_23_, lean_object* v_motive_24_, lean_object* v_i_25_, lean_object* v_h_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_22_, v_as_23_, v_motive_24_, v_i_25_, v_h_26_, v_h__1_27_, v_h__2_28_);
lean_dec(v_i_25_);
lean_dec_ref(v_as_23_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
lean_object* v_zero_33_; uint8_t v_isZero_34_; 
v_zero_33_ = lean_unsigned_to_nat(0u);
v_isZero_34_ = lean_nat_dec_eq(v_i_30_, v_zero_33_);
if (v_isZero_34_ == 1)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_32_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__1_31_, v___x_35_);
return v___x_36_;
}
else
{
lean_object* v_one_37_; lean_object* v_n_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_31_);
v_one_37_ = lean_unsigned_to_nat(1u);
v_n_38_ = lean_nat_sub(v_i_30_, v_one_37_);
v___x_39_ = lean_apply_1(v_h__2_32_, v_n_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_40_, v_h__1_41_, v_h__2_42_);
lean_dec(v_i_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_44_, lean_object* v_i_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_45_, v_h__1_46_, v_h__2_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_49_, lean_object* v_i_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_49_, v_i_50_, v_h__1_51_, v_h__2_52_);
lean_dec(v_i_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(lean_object* v_i_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
lean_object* v_zero_57_; uint8_t v_isZero_58_; 
v_zero_57_ = lean_unsigned_to_nat(0u);
v_isZero_58_ = lean_nat_dec_eq(v_i_54_, v_zero_57_);
if (v_isZero_58_ == 1)
{
lean_object* v___x_59_; 
lean_dec(v_h__2_56_);
v___x_59_ = lean_apply_1(v_h__1_55_, lean_box(0));
return v___x_59_;
}
else
{
lean_object* v_one_60_; lean_object* v_n_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_55_);
v_one_60_ = lean_unsigned_to_nat(1u);
v_n_61_ = lean_nat_sub(v_i_54_, v_one_60_);
v___x_62_ = lean_apply_2(v_h__2_56_, v_n_61_, lean_box(0));
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object* v_i_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(v_i_63_, v_h__1_64_, v_h__2_65_);
lean_dec(v_i_63_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(lean_object* v_00_u03b1_67_, lean_object* v_as_68_, lean_object* v_j_69_, lean_object* v_motive_70_, lean_object* v_i_71_, lean_object* v_inv_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(v_i_71_, v_h__1_73_, v_h__2_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object* v_00_u03b1_76_, lean_object* v_as_77_, lean_object* v_j_78_, lean_object* v_motive_79_, lean_object* v_i_80_, lean_object* v_inv_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(v_00_u03b1_76_, v_as_77_, v_j_78_, v_motive_79_, v_i_80_, v_inv_81_, v_h__1_82_, v_h__2_83_);
lean_dec(v_i_80_);
lean_dec(v_j_78_);
lean_dec_ref(v_as_77_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
lean_object* v_zero_88_; uint8_t v_isZero_89_; 
v_zero_88_ = lean_unsigned_to_nat(0u);
v_isZero_89_ = lean_nat_dec_eq(v_x_85_, v_zero_88_);
if (v_isZero_89_ == 1)
{
lean_object* v___x_90_; 
lean_dec(v_h__2_87_);
v___x_90_ = lean_apply_1(v_h__1_86_, lean_box(0));
return v___x_90_;
}
else
{
lean_object* v_one_91_; lean_object* v_n_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_86_);
v_one_91_ = lean_unsigned_to_nat(1u);
v_n_92_ = lean_nat_sub(v_x_85_, v_one_91_);
v___x_93_ = lean_apply_2(v_h__2_87_, v_n_92_, lean_box(0));
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_94_, v_h__1_95_, v_h__2_96_);
lean_dec(v_x_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_98_, lean_object* v_xs_99_, lean_object* v_motive_100_, lean_object* v_x_101_, lean_object* v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_101_, v_h__1_103_, v_h__2_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_106_, lean_object* v_xs_107_, lean_object* v_motive_108_, lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_106_, v_xs_107_, v_motive_108_, v_x_109_, v_x_110_, v_h__1_111_, v_h__2_112_);
lean_dec(v_x_109_);
lean_dec_ref(v_xs_107_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object* v_r_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (lean_obj_tag(v_r_114_) == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_115_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_1(v_h__2_116_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_116_);
v_val_119_ = lean_ctor_get(v_r_114_, 0);
lean_inc(v_val_119_);
lean_dec_ref(v_r_114_);
v___x_120_ = lean_apply_1(v_h__1_115_, v_val_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* v_00_u03b2_121_, lean_object* v_motive_122_, lean_object* v_r_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(v_r_123_, v_h__1_124_, v_h__2_125_);
return v___x_126_;
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Internal_Order_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Internal_Order_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Internal_Order_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Internal_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Internal_Order_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
