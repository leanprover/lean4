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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl(lean_object* v_x_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_tag_nat(v_x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl___boxed(lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Grind_CommRing_PSumTree_ctorIdx___impl(v_x_58_);
lean_dec_ref(v_x_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(lean_object* v_t_60_, lean_object* v_k_61_){
_start:
{
if (lean_obj_tag(v_t_60_) == 0)
{
lean_object* v_k_62_; lean_object* v_m_63_; lean_object* v_D_64_; lean_object* v_p_65_; lean_object* v___x_66_; 
v_k_62_ = lean_ctor_get(v_t_60_, 0);
lean_inc(v_k_62_);
v_m_63_ = lean_ctor_get(v_t_60_, 1);
lean_inc(v_m_63_);
v_D_64_ = lean_ctor_get(v_t_60_, 2);
lean_inc(v_D_64_);
v_p_65_ = lean_ctor_get(v_t_60_, 3);
lean_inc_ref(v_p_65_);
lean_dec_ref_known(v_t_60_, 4);
v___x_66_ = lean_apply_4(v_k_61_, v_k_62_, v_m_63_, v_D_64_, v_p_65_);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v_b_68_; lean_object* v___x_69_; 
v_a_67_ = lean_ctor_get(v_t_60_, 0);
lean_inc_ref(v_a_67_);
v_b_68_ = lean_ctor_get(v_t_60_, 1);
lean_inc_ref(v_b_68_);
lean_dec_ref_known(v_t_60_, 2);
v___x_69_ = lean_apply_2(v_k_61_, v_a_67_, v_b_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim(lean_object* v_motive_70_, lean_object* v_ctorIdx_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_k_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_72_, v_k_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_ctorElim___boxed(lean_object* v_motive_76_, lean_object* v_ctorIdx_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_k_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Grind_CommRing_PSumTree_ctorElim(v_motive_76_, v_ctorIdx_77_, v_t_78_, v_h_79_, v_k_80_);
lean_dec(v_ctorIdx_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_leaf_elim___redArg(lean_object* v_t_82_, lean_object* v_leaf_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_82_, v_leaf_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_leaf_elim(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_leaf_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_86_, v_leaf_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_node_elim___redArg(lean_object* v_t_90_, lean_object* v_node_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_90_, v_node_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PSumTree_node_elim(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_node_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Grind_CommRing_PSumTree_ctorElim___redArg(v_t_94_, v_node_96_);
return v___x_97_;
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
