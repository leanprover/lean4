// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const public import Std.Sat.AIG.If import Init.Omega
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
lean_object* l_BitVec_instNatCast___lam__0(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_x_5_, lean_object* v_curr_6_, lean_object* v_acc_7_){
_start:
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_lt(v_curr_6_, v_w_3_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec(v_curr_6_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_aig_4_);
lean_ctor_set(v___x_9_, 1, v_acc_7_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_lhs_16_; lean_object* v___y_18_; lean_object* v_ref_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_10_ = l_BitVec_instNatCast___lam__0(v_w_3_, v_w_3_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = l_BitVec_ofNat(v_w_3_, v___x_11_);
v___x_13_ = l_BitVec_sub(v_w_3_, v___x_10_, v___x_12_);
lean_dec(v___x_12_);
lean_dec(v___x_10_);
v___x_14_ = l_BitVec_instNatCast___lam__0(v_w_3_, v_curr_6_);
v___x_15_ = l_BitVec_sub(v_w_3_, v___x_13_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_13_);
v_lhs_16_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_3_, v___x_15_);
lean_dec(v___x_15_);
v_ref_25_ = lean_array_fget_borrowed(v_x_5_, v_curr_6_);
v___x_26_ = lean_nat_shiftr(v_ref_25_, v___x_11_);
v___x_27_ = lean_nat_land(v___x_11_, v_ref_25_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_dec_eq(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_30_, 0, v___x_26_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*1, v___x_8_);
v___y_18_ = v___x_30_;
goto v___jp_17_;
}
else
{
uint8_t v___x_31_; lean_object* v___x_32_; 
v___x_31_ = 0;
v___x_32_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_32_, 0, v___x_26_);
lean_ctor_set_uint8(v___x_32_, sizeof(void*)*1, v___x_31_);
v___y_18_ = v___x_32_;
goto v___jp_17_;
}
v___jp_17_:
{
lean_object* v___x_19_; lean_object* v_res_20_; lean_object* v_aig_21_; lean_object* v_vec_22_; lean_object* v___x_23_; 
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___y_18_);
lean_ctor_set(v___x_19_, 1, v_lhs_16_);
lean_ctor_set(v___x_19_, 2, v_acc_7_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_20_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_4_, v___x_19_);
v_aig_21_ = lean_ctor_get(v_res_20_, 0);
lean_inc_ref(v_aig_21_);
v_vec_22_ = lean_ctor_get(v_res_20_, 1);
lean_inc_ref(v_vec_22_);
lean_dec_ref(v_res_20_);
v___x_23_ = lean_nat_add(v_curr_6_, v___x_11_);
lean_dec(v_curr_6_);
v_aig_4_ = v_aig_21_;
v_curr_6_ = v___x_23_;
v_acc_7_ = v_vec_22_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg___boxed(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_w_35_, lean_object* v_aig_36_, lean_object* v_x_37_, lean_object* v_curr_38_, lean_object* v_acc_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(v_inst_33_, v_inst_34_, v_w_35_, v_aig_36_, v_x_37_, v_curr_38_, v_acc_39_);
lean_dec_ref(v_x_37_);
lean_dec(v_w_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_w_44_, lean_object* v_aig_45_, lean_object* v_x_46_, lean_object* v_curr_47_, lean_object* v_acc_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(v_inst_42_, v_inst_43_, v_w_44_, v_aig_45_, v_x_46_, v_curr_47_, v_acc_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___boxed(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_w_53_, lean_object* v_aig_54_, lean_object* v_x_55_, lean_object* v_curr_56_, lean_object* v_acc_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(v_00_u03b1_50_, v_inst_51_, v_inst_52_, v_w_53_, v_aig_54_, v_x_55_, v_curr_56_, v_acc_57_);
lean_dec_ref(v_x_55_);
lean_dec(v_w_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_w_61_, lean_object* v_aig_62_, lean_object* v_x_63_){
_start:
{
lean_object* v___x_64_; lean_object* v_wconst_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = l_BitVec_instNatCast___lam__0(v_w_61_, v_w_61_);
v_wconst_65_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_61_, v___x_64_);
lean_dec(v___x_64_);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(v_inst_59_, v_inst_60_, v_w_61_, v_aig_62_, v_x_63_, v___x_66_, v_wconst_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg___boxed(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_w_70_, lean_object* v_aig_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(v_inst_68_, v_inst_69_, v_w_70_, v_aig_71_, v_x_72_);
lean_dec_ref(v_x_72_);
lean_dec(v_w_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_w_77_, lean_object* v_aig_78_, lean_object* v_x_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_78_, v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___boxed(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_w_84_, lean_object* v_aig_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(v_00_u03b1_81_, v_inst_82_, v_inst_83_, v_w_84_, v_aig_85_, v_x_86_);
lean_dec_ref(v_x_86_);
lean_dec(v_w_84_);
return v_res_87_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
}
#ifdef __cplusplus
}
#endif
