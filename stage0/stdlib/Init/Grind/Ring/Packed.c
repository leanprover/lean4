// Lean compiler output
// Module: Init.Grind.Ring.Packed
// Imports: public import Init.Grind.Ring.CommSolver public import Init.Grind.Ring.CommSemiringAdapter import Init.Omega import Init.Grind.Ordered.Order import Init.WFTactics import Init.ByCases import Init.Data.List.Lemmas import Init.Data.Nat.Lemmas
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_dsum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_dsum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Packed_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Packed_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Grind_CommRing_PPoly_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_k_7_; lean_object* v___x_8_; 
v_k_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_k_7_);
return v___x_8_;
}
else
{
lean_object* v_k_9_; lean_object* v_d_10_; lean_object* v_v_11_; lean_object* v_p_12_; lean_object* v___x_13_; 
v_k_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_9_);
v_d_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_d_10_);
v_v_11_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_v_11_);
v_p_12_ = lean_ctor_get(v_t_5_, 3);
lean_inc_ref(v_p_12_);
lean_dec_ref_known(v_t_5_, 4);
v___x_13_ = lean_apply_4(v_k_6_, v_k_9_, v_d_10_, v_v_11_, v_p_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Grind_CommRing_PPoly_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Grind_CommRing_PPoly_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_num_elim___redArg(lean_object* v_t_26_, lean_object* v_num_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Grind_CommRing_PPoly_ctorElim___redArg(v_t_26_, v_num_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_num_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_num_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Grind_CommRing_PPoly_ctorElim___redArg(v_t_30_, v_num_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_add_elim___redArg(lean_object* v_t_34_, lean_object* v_add_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Grind_CommRing_PPoly_ctorElim___redArg(v_t_34_, v_add_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_add_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_add_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Grind_CommRing_PPoly_ctorElim___redArg(v_t_38_, v_add_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_dsum(lean_object* v_B_42_, lean_object* v_v_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_dec_lt(v___x_44_, v_B_42_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
v___x_46_ = lean_unsigned_to_nat(0u);
return v___x_46_;
}
else
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v_v_43_);
if (v___x_48_ == 0)
{
return v___x_47_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_nat_mod(v_v_43_, v_B_42_);
v___x_50_ = lean_nat_div(v_v_43_, v_B_42_);
v___x_51_ = l_Lean_Grind_CommRing_PPoly_dsum(v_B_42_, v___x_50_);
lean_dec(v___x_50_);
v___x_52_ = lean_nat_add(v___x_49_, v___x_51_);
lean_dec(v___x_51_);
lean_dec(v___x_49_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_dsum___boxed(lean_object* v_B_53_, lean_object* v_v_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Grind_CommRing_PPoly_dsum(v_B_53_, v_v_54_);
lean_dec(v_v_54_);
lean_dec(v_B_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Packed_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter___redArg(lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v_k_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_58_);
v_k_59_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_k_59_);
lean_dec_ref_known(v_x_56_, 1);
v___x_60_ = lean_apply_1(v_h__1_57_, v_k_59_);
return v___x_60_;
}
else
{
lean_object* v_k_61_; lean_object* v_d_62_; lean_object* v_v_63_; lean_object* v_p_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_57_);
v_k_61_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_k_61_);
v_d_62_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_d_62_);
v_v_63_ = lean_ctor_get(v_x_56_, 2);
lean_inc(v_v_63_);
v_p_64_ = lean_ctor_get(v_x_56_, 3);
lean_inc_ref(v_p_64_);
lean_dec_ref_known(v_x_56_, 4);
v___x_65_ = lean_apply_4(v_h__2_58_, v_k_61_, v_d_62_, v_v_63_, v_p_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Packed_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter(lean_object* v_motive_66_, lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v_k_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_69_);
v_k_70_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_k_70_);
lean_dec_ref_known(v_x_67_, 1);
v___x_71_ = lean_apply_1(v_h__1_68_, v_k_70_);
return v___x_71_;
}
else
{
lean_object* v_k_72_; lean_object* v_d_73_; lean_object* v_v_74_; lean_object* v_p_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_68_);
v_k_72_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_k_72_);
v_d_73_ = lean_ctor_get(v_x_67_, 1);
lean_inc(v_d_73_);
v_v_74_ = lean_ctor_get(v_x_67_, 2);
lean_inc(v_v_74_);
v_p_75_ = lean_ctor_get(v_x_67_, 3);
lean_inc_ref(v_p_75_);
lean_dec_ref_known(v_x_67_, 4);
v___x_76_ = lean_apply_4(v_h__2_69_, v_k_72_, v_d_73_, v_v_74_, v_p_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl(lean_object* v_x_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_tag_nat(v_x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl___boxed(lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl(v_x_79_);
lean_dec_ref(v_x_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(lean_object* v_t_81_, lean_object* v_k_82_){
_start:
{
if (lean_obj_tag(v_t_81_) == 0)
{
lean_object* v_k_83_; lean_object* v_m_84_; lean_object* v_D_85_; lean_object* v_p_86_; lean_object* v___x_87_; 
v_k_83_ = lean_ctor_get(v_t_81_, 0);
lean_inc(v_k_83_);
v_m_84_ = lean_ctor_get(v_t_81_, 1);
lean_inc(v_m_84_);
v_D_85_ = lean_ctor_get(v_t_81_, 2);
lean_inc(v_D_85_);
v_p_86_ = lean_ctor_get(v_t_81_, 3);
lean_inc_ref(v_p_86_);
lean_dec_ref_known(v_t_81_, 4);
v___x_87_ = lean_apply_4(v_k_82_, v_k_83_, v_m_84_, v_D_85_, v_p_86_);
return v___x_87_;
}
else
{
lean_object* v_a_88_; lean_object* v_b_89_; lean_object* v___x_90_; 
v_a_88_ = lean_ctor_get(v_t_81_, 0);
lean_inc_ref(v_a_88_);
v_b_89_ = lean_ctor_get(v_t_81_, 1);
lean_inc_ref(v_b_89_);
lean_dec_ref_known(v_t_81_, 2);
v___x_90_ = lean_apply_2(v_k_82_, v_a_88_, v_b_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim(lean_object* v_motive_91_, lean_object* v_ctorIdx_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_k_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_93_, v_k_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim___boxed(lean_object* v_motive_97_, lean_object* v_ctorIdx_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_k_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Grind_CommRing_PSumTree_ctorElim(v_motive_97_, v_ctorIdx_98_, v_t_99_, v_h_100_, v_k_101_);
lean_dec(v_ctorIdx_98_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_leaf_elim___redArg(lean_object* v_t_103_, lean_object* v_leaf_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_103_, v_leaf_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_leaf_elim(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_leaf_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_107_, v_leaf_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_node_elim___redArg(lean_object* v_t_111_, lean_object* v_node_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_111_, v_node_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_node_elim(lean_object* v_motive_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_node_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_115_, v_node_117_);
return v___x_118_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_Packed(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_Packed(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Order(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_Packed(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Packed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_Packed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_Packed(builtin);
}
#ifdef __cplusplus
}
#endif
