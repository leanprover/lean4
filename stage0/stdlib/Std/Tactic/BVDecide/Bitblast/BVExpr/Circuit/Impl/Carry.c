// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add import Init.Omega
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry_0__Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry_0__Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry_0__Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_lhs_5_, lean_object* v_rhs_6_, lean_object* v_curr_7_, lean_object* v_cin_8_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_lt(v_curr_7_, v_w_3_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_curr_7_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_aig_4_);
lean_ctor_set(v___x_10_, 1, v_cin_8_);
return v___x_10_;
}
else
{
lean_object* v_ref_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; lean_object* v_lin_18_; lean_object* v_ref_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; uint8_t v___x_23_; lean_object* v_rin_24_; lean_object* v___x_25_; lean_object* v_res_26_; lean_object* v_aig_27_; lean_object* v_ref_28_; lean_object* v___x_29_; 
v_ref_11_ = lean_array_fget_borrowed(v_lhs_5_, v_curr_7_);
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_land(v___x_12_, v_ref_11_);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_dec_eq(v___x_13_, v___x_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_nat_shiftr(v_ref_11_, v___x_12_);
v___x_17_ = lean_bool_not(v___x_15_);
v_lin_18_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_lin_18_, 0, v___x_16_);
lean_ctor_set_uint8(v_lin_18_, sizeof(void*)*1, v___x_17_);
v_ref_19_ = lean_array_fget_borrowed(v_rhs_6_, v_curr_7_);
v___x_20_ = lean_nat_shiftr(v_ref_19_, v___x_12_);
v___x_21_ = lean_nat_land(v___x_12_, v_ref_19_);
v___x_22_ = lean_nat_dec_eq(v___x_21_, v___x_14_);
lean_dec(v___x_21_);
v___x_23_ = lean_bool_not(v___x_22_);
v_rin_24_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_rin_24_, 0, v___x_20_);
lean_ctor_set_uint8(v_rin_24_, sizeof(void*)*1, v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_25_, 0, v_lin_18_);
lean_ctor_set(v___x_25_, 1, v_rin_24_);
lean_ctor_set(v___x_25_, 2, v_cin_8_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_26_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_1_, v_inst_2_, v_aig_4_, v___x_25_);
v_aig_27_ = lean_ctor_get(v_res_26_, 0);
lean_inc_ref(v_aig_27_);
v_ref_28_ = lean_ctor_get(v_res_26_, 1);
lean_inc_ref(v_ref_28_);
lean_dec_ref(v_res_26_);
v___x_29_ = lean_nat_add(v_curr_7_, v___x_12_);
lean_dec(v_curr_7_);
v_aig_4_ = v_aig_27_;
v_curr_7_ = v___x_29_;
v_cin_8_ = v_ref_28_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg___boxed(lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_w_33_, lean_object* v_aig_34_, lean_object* v_lhs_35_, lean_object* v_rhs_36_, lean_object* v_curr_37_, lean_object* v_cin_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(v_inst_31_, v_inst_32_, v_w_33_, v_aig_34_, v_lhs_35_, v_rhs_36_, v_curr_37_, v_cin_38_);
lean_dec_ref(v_rhs_36_);
lean_dec_ref(v_lhs_35_);
lean_dec(v_w_33_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_w_43_, lean_object* v_aig_44_, lean_object* v_lhs_45_, lean_object* v_rhs_46_, lean_object* v_curr_47_, lean_object* v_cin_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(v_inst_41_, v_inst_42_, v_w_43_, v_aig_44_, v_lhs_45_, v_rhs_46_, v_curr_47_, v_cin_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___boxed(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_w_53_, lean_object* v_aig_54_, lean_object* v_lhs_55_, lean_object* v_rhs_56_, lean_object* v_curr_57_, lean_object* v_cin_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(v_00_u03b1_50_, v_inst_51_, v_inst_52_, v_w_53_, v_aig_54_, v_lhs_55_, v_rhs_56_, v_curr_57_, v_cin_58_);
lean_dec_ref(v_rhs_56_);
lean_dec_ref(v_lhs_55_);
lean_dec(v_w_53_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_aig_62_, lean_object* v_input_63_){
_start:
{
lean_object* v_vec_64_; lean_object* v_w_65_; lean_object* v_cin_66_; lean_object* v_lhs_67_; lean_object* v_rhs_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_vec_64_ = lean_ctor_get(v_input_63_, 1);
lean_inc_ref(v_vec_64_);
v_w_65_ = lean_ctor_get(v_input_63_, 0);
lean_inc(v_w_65_);
v_cin_66_ = lean_ctor_get(v_input_63_, 2);
lean_inc_ref(v_cin_66_);
lean_dec_ref(v_input_63_);
v_lhs_67_ = lean_ctor_get(v_vec_64_, 0);
lean_inc_ref(v_lhs_67_);
v_rhs_68_ = lean_ctor_get(v_vec_64_, 1);
lean_inc_ref(v_rhs_68_);
lean_dec_ref(v_vec_64_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(v_inst_60_, v_inst_61_, v_w_65_, v_aig_62_, v_lhs_67_, v_rhs_68_, v___x_69_, v_cin_66_);
lean_dec_ref(v_rhs_68_);
lean_dec_ref(v_lhs_67_);
lean_dec(v_w_65_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_aig_74_, lean_object* v_input_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(v_inst_72_, v_inst_73_, v_aig_74_, v_input_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry_0__Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_match__1_splitter___redArg(lean_object* v_input_77_, lean_object* v_h__1_78_){
_start:
{
lean_object* v_vec_79_; lean_object* v_w_80_; lean_object* v_cin_81_; lean_object* v_lhs_82_; lean_object* v_rhs_83_; lean_object* v___x_84_; 
v_vec_79_ = lean_ctor_get(v_input_77_, 1);
lean_inc_ref(v_vec_79_);
v_w_80_ = lean_ctor_get(v_input_77_, 0);
lean_inc(v_w_80_);
v_cin_81_ = lean_ctor_get(v_input_77_, 2);
lean_inc_ref(v_cin_81_);
lean_dec_ref(v_input_77_);
v_lhs_82_ = lean_ctor_get(v_vec_79_, 0);
lean_inc_ref(v_lhs_82_);
v_rhs_83_ = lean_ctor_get(v_vec_79_, 1);
lean_inc_ref(v_rhs_83_);
lean_dec_ref(v_vec_79_);
v___x_84_ = lean_apply_4(v_h__1_78_, v_w_80_, v_lhs_82_, v_rhs_83_, v_cin_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry_0__Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_match__1_splitter(lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_aig_88_, lean_object* v_motive_89_, lean_object* v_input_90_, lean_object* v_h__1_91_){
_start:
{
lean_object* v_vec_92_; lean_object* v_w_93_; lean_object* v_cin_94_; lean_object* v_lhs_95_; lean_object* v_rhs_96_; lean_object* v___x_97_; 
v_vec_92_ = lean_ctor_get(v_input_90_, 1);
lean_inc_ref(v_vec_92_);
v_w_93_ = lean_ctor_get(v_input_90_, 0);
lean_inc(v_w_93_);
v_cin_94_ = lean_ctor_get(v_input_90_, 2);
lean_inc_ref(v_cin_94_);
lean_dec_ref(v_input_90_);
v_lhs_95_ = lean_ctor_get(v_vec_92_, 0);
lean_inc_ref(v_lhs_95_);
v_rhs_96_ = lean_ctor_get(v_vec_92_, 1);
lean_inc_ref(v_rhs_96_);
lean_dec_ref(v_vec_92_);
v___x_97_ = lean_apply_4(v_h__1_91_, v_w_93_, v_lhs_95_, v_rhs_96_, v_cin_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry_0__Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_match__1_splitter___boxed(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_aig_101_, lean_object* v_motive_102_, lean_object* v_input_103_, lean_object* v_h__1_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry_0__Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_match__1_splitter(v_00_u03b1_98_, v_inst_99_, v_inst_100_, v_aig_101_, v_motive_102_, v_input_103_, v_h__1_104_);
lean_dec_ref(v_aig_101_);
lean_dec_ref(v_inst_100_);
lean_dec_ref(v_inst_99_);
return v_res_105_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
}
#ifdef __cplusplus
}
#endif
