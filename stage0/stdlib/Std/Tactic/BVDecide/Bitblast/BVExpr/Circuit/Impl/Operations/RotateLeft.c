// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(lean_object* v_w_1_, lean_object* v_input_2_, lean_object* v_distance_3_, lean_object* v_curr_4_, lean_object* v_s_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_lt(v_curr_4_, v_w_1_);
if (v___x_6_ == 0)
{
lean_dec(v_curr_4_);
return v_s_5_;
}
else
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_nat_mod(v_distance_3_, v_w_1_);
v___x_8_ = lean_nat_dec_lt(v_curr_4_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v_ref_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_s_22_; 
v___x_9_ = lean_nat_sub(v_curr_4_, v___x_7_);
lean_dec(v___x_7_);
v_ref_10_ = lean_array_fget_borrowed(v_input_2_, v___x_9_);
lean_dec(v___x_9_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_land(v___x_11_, v_ref_10_);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_dec_eq(v___x_12_, v___x_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_nat_shiftr(v_ref_10_, v___x_11_);
v___x_16_ = lean_bool_not(v___x_14_);
v___x_17_ = lean_nat_add(v_curr_4_, v___x_11_);
lean_dec(v_curr_4_);
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = lean_nat_mul(v___x_15_, v___x_18_);
lean_dec(v___x_15_);
v___x_20_ = lean_bool_to_nat(v___x_16_);
v___x_21_ = lean_nat_lor(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v_s_22_ = lean_array_push(v_s_5_, v___x_21_);
v_curr_4_ = v___x_17_;
v_s_5_ = v_s_22_;
goto _start;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_ref_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v_s_38_; 
v___x_24_ = lean_nat_sub(v_w_1_, v___x_7_);
lean_dec(v___x_7_);
v___x_25_ = lean_nat_add(v___x_24_, v_curr_4_);
lean_dec(v___x_24_);
v_ref_26_ = lean_array_fget_borrowed(v_input_2_, v___x_25_);
lean_dec(v___x_25_);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_land(v___x_27_, v_ref_26_);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_nat_dec_eq(v___x_28_, v___x_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_nat_shiftr(v_ref_26_, v___x_27_);
v___x_32_ = lean_bool_not(v___x_30_);
v___x_33_ = lean_nat_add(v_curr_4_, v___x_27_);
lean_dec(v_curr_4_);
v___x_34_ = lean_unsigned_to_nat(2u);
v___x_35_ = lean_nat_mul(v___x_31_, v___x_34_);
lean_dec(v___x_31_);
v___x_36_ = lean_bool_to_nat(v___x_32_);
v___x_37_ = lean_nat_lor(v___x_35_, v___x_36_);
lean_dec(v___x_35_);
v_s_38_ = lean_array_push(v_s_5_, v___x_37_);
v_curr_4_ = v___x_33_;
v_s_5_ = v_s_38_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg___boxed(lean_object* v_w_40_, lean_object* v_input_41_, lean_object* v_distance_42_, lean_object* v_curr_43_, lean_object* v_s_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(v_w_40_, v_input_41_, v_distance_42_, v_curr_43_, v_s_44_);
lean_dec(v_distance_42_);
lean_dec_ref(v_input_41_);
lean_dec(v_w_40_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_w_49_, lean_object* v_aig_50_, lean_object* v_input_51_, lean_object* v_distance_52_, lean_object* v_curr_53_, lean_object* v_hcurr_54_, lean_object* v_s_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(v_w_49_, v_input_51_, v_distance_52_, v_curr_53_, v_s_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___boxed(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_w_60_, lean_object* v_aig_61_, lean_object* v_input_62_, lean_object* v_distance_63_, lean_object* v_curr_64_, lean_object* v_hcurr_65_, lean_object* v_s_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(v_00_u03b1_57_, v_inst_58_, v_inst_59_, v_w_60_, v_aig_61_, v_input_62_, v_distance_63_, v_curr_64_, v_hcurr_65_, v_s_66_);
lean_dec(v_distance_63_);
lean_dec_ref(v_input_62_);
lean_dec_ref(v_aig_61_);
lean_dec(v_w_60_);
lean_dec_ref(v_inst_59_);
lean_dec_ref(v_inst_58_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(lean_object* v_w_68_, lean_object* v_aig_69_, lean_object* v_target_70_){
_start:
{
lean_object* v_vec_71_; lean_object* v_distance_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_82_; 
v_vec_71_ = lean_ctor_get(v_target_70_, 0);
v_distance_72_ = lean_ctor_get(v_target_70_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_target_70_);
if (v_isSharedCheck_82_ == 0)
{
v___x_74_ = v_target_70_;
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_distance_72_);
lean_inc(v_vec_71_);
lean_dec(v_target_70_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_mk_empty_array_with_capacity(v_w_68_);
v___x_78_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(v_w_68_, v_vec_71_, v_distance_72_, v___x_76_, v___x_77_);
lean_dec(v_distance_72_);
lean_dec_ref(v_vec_71_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v___x_78_);
lean_ctor_set(v___x_74_, 0, v_aig_69_);
v___x_80_ = v___x_74_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_aig_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg___boxed(lean_object* v_w_83_, lean_object* v_aig_84_, lean_object* v_target_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(v_w_83_, v_aig_84_, v_target_85_);
lean_dec(v_w_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_w_90_, lean_object* v_aig_91_, lean_object* v_target_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(v_w_90_, v_aig_91_, v_target_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___boxed(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_w_97_, lean_object* v_aig_98_, lean_object* v_target_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(v_00_u03b1_94_, v_inst_95_, v_inst_96_, v_w_97_, v_aig_98_, v_target_99_);
lean_dec(v_w_97_);
lean_dec_ref(v_inst_96_);
lean_dec_ref(v_inst_95_);
return v_res_100_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin);
}
#ifdef __cplusplus
}
#endif
