// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_input_5_){
_start:
{
lean_object* v_lhs_6_; lean_object* v_rhs_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_41_; 
v_lhs_6_ = lean_ctor_get(v_input_5_, 0);
v_rhs_7_ = lean_ctor_get(v_input_5_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_input_5_);
if (v_isSharedCheck_41_ == 0)
{
v___x_9_ = v_input_5_;
v_isShared_10_ = v_isSharedCheck_41_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_rhs_7_);
lean_inc(v_lhs_6_);
lean_dec(v_input_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_41_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_zero_13_; lean_object* v___x_15_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = l_BitVec_ofNat(v_w_3_, v___x_11_);
v_zero_13_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_3_, v___x_12_);
lean_dec(v___x_12_);
lean_inc_ref(v_zero_13_);
lean_inc_ref(v_rhs_7_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 1, v_zero_13_);
lean_ctor_set(v___x_9_, 0, v_rhs_7_);
v___x_15_ = v___x_9_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_rhs_7_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_zero_13_);
v___x_15_ = v_reuseFailAlloc_40_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v_res_16_; lean_object* v_aig_17_; lean_object* v_ref_18_; lean_object* v_res_19_; lean_object* v_aig_20_; lean_object* v_r_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_38_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_16_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_4_, v___x_15_);
lean_dec_ref(v___x_15_);
v_aig_17_ = lean_ctor_get(v_res_16_, 0);
lean_inc_ref(v_aig_17_);
v_ref_18_ = lean_ctor_get(v_res_16_, 1);
lean_inc_ref(v_ref_18_);
lean_dec_ref(v_res_16_);
lean_inc_ref(v_zero_13_);
lean_inc(v_w_3_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_19_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_17_, v_w_3_, v_lhs_6_, v_rhs_7_, v_w_3_, v___x_11_, v_zero_13_, v_zero_13_);
v_aig_20_ = lean_ctor_get(v_res_19_, 0);
v_r_21_ = lean_ctor_get(v_res_19_, 2);
v_isSharedCheck_38_ = !lean_is_exclusive(v_res_19_);
if (v_isSharedCheck_38_ == 0)
{
lean_object* v_unused_39_; 
v_unused_39_ = lean_ctor_get(v_res_19_, 1);
lean_dec(v_unused_39_);
v___x_23_ = v_res_19_;
v_isShared_24_ = v_isSharedCheck_38_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_r_21_);
lean_inc(v_aig_20_);
lean_dec(v_res_19_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_38_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_gate_25_; uint8_t v_invert_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_37_; 
v_gate_25_ = lean_ctor_get(v_ref_18_, 0);
v_invert_26_ = lean_ctor_get_uint8(v_ref_18_, sizeof(void*)*1);
v_isSharedCheck_37_ = !lean_is_exclusive(v_ref_18_);
if (v_isSharedCheck_37_ == 0)
{
v___x_28_ = v_ref_18_;
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_gate_25_);
lean_dec(v_ref_18_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v_discr_31_; 
if (v_isShared_29_ == 0)
{
v_discr_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_gate_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_36_, sizeof(void*)*1, v_invert_26_);
v_discr_31_ = v_reuseFailAlloc_36_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_33_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v_lhs_6_);
lean_ctor_set(v___x_23_, 0, v_discr_31_);
v___x_33_ = v___x_23_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_discr_31_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_lhs_6_);
lean_ctor_set(v_reuseFailAlloc_35_, 2, v_r_21_);
v___x_33_ = v_reuseFailAlloc_35_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_20_, v___x_33_);
lean_dec(v_w_3_);
return v___x_34_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_w_45_, lean_object* v_aig_46_, lean_object* v_input_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(v_inst_43_, v_inst_44_, v_w_45_, v_aig_46_, v_input_47_);
return v___x_48_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
}
#ifdef __cplusplus
}
#endif
