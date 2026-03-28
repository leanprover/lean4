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
lean_object* v_zero_21_; uint8_t v_isZero_22_; 
v_zero_21_ = lean_unsigned_to_nat(0u);
v_isZero_22_ = lean_nat_dec_eq(v_i_17_, v_zero_21_);
if (v_isZero_22_ == 1)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_20_);
v___x_23_ = lean_apply_1(v_h__1_19_, lean_box(0));
return v___x_23_;
}
else
{
lean_object* v_one_24_; lean_object* v_n_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_19_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_n_25_ = lean_nat_sub(v_i_17_, v_one_24_);
v___x_26_ = lean_apply_2(v_h__2_20_, v_n_25_, lean_box(0));
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_as_28_, lean_object* v_motive_29_, lean_object* v_i_30_, lean_object* v_h_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_27_, v_as_28_, v_motive_29_, v_i_30_, v_h_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_i_30_);
lean_dec_ref(v_as_28_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
lean_object* v_zero_38_; uint8_t v_isZero_39_; 
v_zero_38_ = lean_unsigned_to_nat(0u);
v_isZero_39_ = lean_nat_dec_eq(v_i_35_, v_zero_38_);
if (v_isZero_39_ == 1)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_37_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_36_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_one_42_; lean_object* v_n_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_36_);
v_one_42_ = lean_unsigned_to_nat(1u);
v_n_43_ = lean_nat_sub(v_i_35_, v_one_42_);
v___x_44_ = lean_apply_1(v_h__2_37_, v_n_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_45_, v_h__1_46_, v_h__2_47_);
lean_dec(v_i_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_49_, lean_object* v_i_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
lean_object* v_zero_53_; uint8_t v_isZero_54_; 
v_zero_53_ = lean_unsigned_to_nat(0u);
v_isZero_54_ = lean_nat_dec_eq(v_i_50_, v_zero_53_);
if (v_isZero_54_ == 1)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_52_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__1_51_, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v_one_57_; lean_object* v_n_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_51_);
v_one_57_ = lean_unsigned_to_nat(1u);
v_n_58_ = lean_nat_sub(v_i_50_, v_one_57_);
v___x_59_ = lean_apply_1(v_h__2_52_, v_n_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_60_, lean_object* v_i_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_60_, v_i_61_, v_h__1_62_, v_h__2_63_);
lean_dec(v_i_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(lean_object* v_i_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
lean_object* v_zero_68_; uint8_t v_isZero_69_; 
v_zero_68_ = lean_unsigned_to_nat(0u);
v_isZero_69_ = lean_nat_dec_eq(v_i_65_, v_zero_68_);
if (v_isZero_69_ == 1)
{
lean_object* v___x_70_; 
lean_dec(v_h__2_67_);
v___x_70_ = lean_apply_1(v_h__1_66_, lean_box(0));
return v___x_70_;
}
else
{
lean_object* v_one_71_; lean_object* v_n_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_66_);
v_one_71_ = lean_unsigned_to_nat(1u);
v_n_72_ = lean_nat_sub(v_i_65_, v_one_71_);
v___x_73_ = lean_apply_2(v_h__2_67_, v_n_72_, lean_box(0));
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(lean_object* v_i_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(v_i_74_, v_h__1_75_, v_h__2_76_);
lean_dec(v_i_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(lean_object* v_00_u03b1_78_, lean_object* v_as_79_, lean_object* v_j_80_, lean_object* v_motive_81_, lean_object* v_i_82_, lean_object* v_inv_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
lean_object* v_zero_86_; uint8_t v_isZero_87_; 
v_zero_86_ = lean_unsigned_to_nat(0u);
v_isZero_87_ = lean_nat_dec_eq(v_i_82_, v_zero_86_);
if (v_isZero_87_ == 1)
{
lean_object* v___x_88_; 
lean_dec(v_h__2_85_);
v___x_88_ = lean_apply_1(v_h__1_84_, lean_box(0));
return v___x_88_;
}
else
{
lean_object* v_one_89_; lean_object* v_n_90_; lean_object* v___x_91_; 
lean_dec(v_h__1_84_);
v_one_89_ = lean_unsigned_to_nat(1u);
v_n_90_ = lean_nat_sub(v_i_82_, v_one_89_);
v___x_91_ = lean_apply_2(v_h__2_85_, v_n_90_, lean_box(0));
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___boxed(lean_object* v_00_u03b1_92_, lean_object* v_as_93_, lean_object* v_j_94_, lean_object* v_motive_95_, lean_object* v_i_96_, lean_object* v_inv_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(v_00_u03b1_92_, v_as_93_, v_j_94_, v_motive_95_, v_i_96_, v_inv_97_, v_h__1_98_, v_h__2_99_);
lean_dec(v_i_96_);
lean_dec(v_j_94_);
lean_dec_ref(v_as_93_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
lean_object* v_zero_104_; uint8_t v_isZero_105_; 
v_zero_104_ = lean_unsigned_to_nat(0u);
v_isZero_105_ = lean_nat_dec_eq(v_x_101_, v_zero_104_);
if (v_isZero_105_ == 1)
{
lean_object* v___x_106_; 
lean_dec(v_h__2_103_);
v___x_106_ = lean_apply_1(v_h__1_102_, lean_box(0));
return v___x_106_;
}
else
{
lean_object* v_one_107_; lean_object* v_n_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_102_);
v_one_107_ = lean_unsigned_to_nat(1u);
v_n_108_ = lean_nat_sub(v_x_101_, v_one_107_);
v___x_109_ = lean_apply_2(v_h__2_103_, v_n_108_, lean_box(0));
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_110_, v_h__1_111_, v_h__2_112_);
lean_dec(v_x_110_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_114_, lean_object* v_xs_115_, lean_object* v_motive_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
lean_object* v_zero_121_; uint8_t v_isZero_122_; 
v_zero_121_ = lean_unsigned_to_nat(0u);
v_isZero_122_ = lean_nat_dec_eq(v_x_117_, v_zero_121_);
if (v_isZero_122_ == 1)
{
lean_object* v___x_123_; 
lean_dec(v_h__2_120_);
v___x_123_ = lean_apply_1(v_h__1_119_, lean_box(0));
return v___x_123_;
}
else
{
lean_object* v_one_124_; lean_object* v_n_125_; lean_object* v___x_126_; 
lean_dec(v_h__1_119_);
v_one_124_ = lean_unsigned_to_nat(1u);
v_n_125_ = lean_nat_sub(v_x_117_, v_one_124_);
v___x_126_ = lean_apply_2(v_h__2_120_, v_n_125_, lean_box(0));
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_127_, lean_object* v_xs_128_, lean_object* v_motive_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_127_, v_xs_128_, v_motive_129_, v_x_130_, v_x_131_, v_h__1_132_, v_h__2_133_);
lean_dec(v_x_130_);
lean_dec_ref(v_xs_128_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object* v_r_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
if (lean_obj_tag(v_r_135_) == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__1_136_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__2_137_, v___x_138_);
return v___x_139_;
}
else
{
lean_object* v_val_140_; lean_object* v___x_141_; 
lean_dec(v_h__2_137_);
v_val_140_ = lean_ctor_get(v_r_135_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v_r_135_);
v___x_141_ = lean_apply_1(v_h__1_136_, v_val_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* v_00_u03b2_142_, lean_object* v_motive_143_, lean_object* v_r_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
if (lean_obj_tag(v_r_144_) == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_145_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_1(v_h__2_146_, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_150_; 
lean_dec(v_h__2_146_);
v_val_149_ = lean_ctor_get(v_r_144_, 0);
lean_inc(v_val_149_);
lean_dec_ref(v_r_144_);
v___x_150_ = lean_apply_1(v_h__1_145_, v_val_149_);
return v___x_150_;
}
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
