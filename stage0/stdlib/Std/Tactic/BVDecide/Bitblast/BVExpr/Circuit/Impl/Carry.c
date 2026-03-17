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
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_lhs_5_, lean_object* v_rhs_6_, lean_object* v_curr_7_, lean_object* v_cin_8_){
_start:
{
lean_object* v___y_10_; lean_object* v___y_11_; uint8_t v___x_19_; lean_object* v___y_21_; 
v___x_19_ = lean_nat_dec_lt(v_curr_7_, v_w_3_);
if (v___x_19_ == 0)
{
lean_object* v___x_31_; 
lean_dec(v_curr_7_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v_aig_4_);
lean_ctor_set(v___x_31_, 1, v_cin_8_);
return v___x_31_;
}
else
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_ref_32_ = lean_array_fget_borrowed(v_lhs_5_, v_curr_7_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_shiftr(v_ref_32_, v___x_33_);
v___x_35_ = lean_nat_land(v___x_33_, v_ref_32_);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_dec_eq(v___x_35_, v___x_36_);
lean_dec(v___x_35_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_38_, 0, v___x_34_);
lean_ctor_set_uint8(v___x_38_, sizeof(void*)*1, v___x_19_);
v___y_21_ = v___x_38_;
goto v___jp_20_;
}
else
{
uint8_t v___x_39_; lean_object* v___x_40_; 
v___x_39_ = 0;
v___x_40_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_40_, 0, v___x_34_);
lean_ctor_set_uint8(v___x_40_, sizeof(void*)*1, v___x_39_);
v___y_21_ = v___x_40_;
goto v___jp_20_;
}
}
v___jp_9_:
{
lean_object* v___x_12_; lean_object* v_res_13_; lean_object* v_aig_14_; lean_object* v_ref_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___y_10_);
lean_ctor_set(v___x_12_, 1, v___y_11_);
lean_ctor_set(v___x_12_, 2, v_cin_8_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_13_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_1_, v_inst_2_, v_aig_4_, v___x_12_);
v_aig_14_ = lean_ctor_get(v_res_13_, 0);
lean_inc_ref(v_aig_14_);
v_ref_15_ = lean_ctor_get(v_res_13_, 1);
lean_inc_ref(v_ref_15_);
lean_dec_ref(v_res_13_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_curr_7_, v___x_16_);
lean_dec(v_curr_7_);
v_aig_4_ = v_aig_14_;
v_curr_7_ = v___x_17_;
v_cin_8_ = v_ref_15_;
goto _start;
}
v___jp_20_:
{
lean_object* v_ref_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v_ref_22_ = lean_array_fget_borrowed(v_rhs_6_, v_curr_7_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_shiftr(v_ref_22_, v___x_23_);
v___x_25_ = lean_nat_land(v___x_23_, v_ref_22_);
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_nat_dec_eq(v___x_25_, v___x_26_);
lean_dec(v___x_25_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_28_, 0, v___x_24_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*1, v___x_19_);
v___y_10_ = v___y_21_;
v___y_11_ = v___x_28_;
goto v___jp_9_;
}
else
{
uint8_t v___x_29_; lean_object* v___x_30_; 
v___x_29_ = 0;
v___x_30_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_30_, 0, v___x_24_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*1, v___x_29_);
v___y_10_ = v___y_21_;
v___y_11_ = v___x_30_;
goto v___jp_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg___boxed(lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_w_43_, lean_object* v_aig_44_, lean_object* v_lhs_45_, lean_object* v_rhs_46_, lean_object* v_curr_47_, lean_object* v_cin_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(v_inst_41_, v_inst_42_, v_w_43_, v_aig_44_, v_lhs_45_, v_rhs_46_, v_curr_47_, v_cin_48_);
lean_dec_ref(v_rhs_46_);
lean_dec_ref(v_lhs_45_);
lean_dec(v_w_43_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_w_53_, lean_object* v_aig_54_, lean_object* v_lhs_55_, lean_object* v_rhs_56_, lean_object* v_curr_57_, lean_object* v_cin_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(v_inst_51_, v_inst_52_, v_w_53_, v_aig_54_, v_lhs_55_, v_rhs_56_, v_curr_57_, v_cin_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___boxed(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_w_63_, lean_object* v_aig_64_, lean_object* v_lhs_65_, lean_object* v_rhs_66_, lean_object* v_curr_67_, lean_object* v_cin_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(v_00_u03b1_60_, v_inst_61_, v_inst_62_, v_w_63_, v_aig_64_, v_lhs_65_, v_rhs_66_, v_curr_67_, v_cin_68_);
lean_dec_ref(v_rhs_66_);
lean_dec_ref(v_lhs_65_);
lean_dec(v_w_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_aig_72_, lean_object* v_input_73_){
_start:
{
lean_object* v_vec_74_; lean_object* v_w_75_; lean_object* v_cin_76_; lean_object* v_lhs_77_; lean_object* v_rhs_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_vec_74_ = lean_ctor_get(v_input_73_, 1);
lean_inc_ref(v_vec_74_);
v_w_75_ = lean_ctor_get(v_input_73_, 0);
lean_inc(v_w_75_);
v_cin_76_ = lean_ctor_get(v_input_73_, 2);
lean_inc_ref(v_cin_76_);
lean_dec_ref(v_input_73_);
v_lhs_77_ = lean_ctor_get(v_vec_74_, 0);
lean_inc_ref(v_lhs_77_);
v_rhs_78_ = lean_ctor_get(v_vec_74_, 1);
lean_inc_ref(v_rhs_78_);
lean_dec_ref(v_vec_74_);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(v_inst_70_, v_inst_71_, v_w_75_, v_aig_72_, v_lhs_77_, v_rhs_78_, v___x_79_, v_cin_76_);
lean_dec_ref(v_rhs_78_);
lean_dec_ref(v_lhs_77_);
lean_dec(v_w_75_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_aig_84_, lean_object* v_input_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(v_inst_82_, v_inst_83_, v_aig_84_, v_input_85_);
return v___x_86_;
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
