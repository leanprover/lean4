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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_lhs_16_; lean_object* v_ref_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_res_25_; lean_object* v_aig_26_; lean_object* v_vec_27_; lean_object* v___x_28_; 
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
v_ref_17_ = lean_array_fget_borrowed(v_x_5_, v_curr_6_);
v___x_18_ = lean_nat_shiftr(v_ref_17_, v___x_11_);
v___x_19_ = lean_nat_land(v___x_11_, v_ref_17_);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_nat_dec_eq(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_bool_not(v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_23_, 0, v___x_18_);
lean_ctor_set_uint8(v___x_23_, sizeof(void*)*1, v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v_lhs_16_);
lean_ctor_set(v___x_24_, 2, v_acc_7_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_25_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_4_, v___x_24_);
v_aig_26_ = lean_ctor_get(v_res_25_, 0);
lean_inc_ref(v_aig_26_);
v_vec_27_ = lean_ctor_get(v_res_25_, 1);
lean_inc_ref(v_vec_27_);
lean_dec_ref(v_res_25_);
v___x_28_ = lean_nat_add(v_curr_6_, v___x_11_);
lean_dec(v_curr_6_);
v_aig_4_ = v_aig_26_;
v_curr_6_ = v___x_28_;
v_acc_7_ = v_vec_27_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg___boxed(lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_w_32_, lean_object* v_aig_33_, lean_object* v_x_34_, lean_object* v_curr_35_, lean_object* v_acc_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(v_inst_30_, v_inst_31_, v_w_32_, v_aig_33_, v_x_34_, v_curr_35_, v_acc_36_);
lean_dec_ref(v_x_34_);
lean_dec(v_w_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(lean_object* v_00_u03b1_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_w_41_, lean_object* v_aig_42_, lean_object* v_x_43_, lean_object* v_curr_44_, lean_object* v_acc_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(v_inst_39_, v_inst_40_, v_w_41_, v_aig_42_, v_x_43_, v_curr_44_, v_acc_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___boxed(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_w_50_, lean_object* v_aig_51_, lean_object* v_x_52_, lean_object* v_curr_53_, lean_object* v_acc_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(v_00_u03b1_47_, v_inst_48_, v_inst_49_, v_w_50_, v_aig_51_, v_x_52_, v_curr_53_, v_acc_54_);
lean_dec_ref(v_x_52_);
lean_dec(v_w_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_w_58_, lean_object* v_aig_59_, lean_object* v_x_60_){
_start:
{
lean_object* v___x_61_; lean_object* v_wconst_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = l_BitVec_instNatCast___lam__0(v_w_58_, v_w_58_);
v_wconst_62_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_58_, v___x_61_);
lean_dec(v___x_61_);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(v_inst_56_, v_inst_57_, v_w_58_, v_aig_59_, v_x_60_, v___x_63_, v_wconst_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg___boxed(lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_w_67_, lean_object* v_aig_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(v_inst_65_, v_inst_66_, v_w_67_, v_aig_68_, v_x_69_);
lean_dec_ref(v_x_69_);
lean_dec(v_w_67_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_w_74_, lean_object* v_aig_75_, lean_object* v_x_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(v_inst_72_, v_inst_73_, v_w_74_, v_aig_75_, v_x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___boxed(lean_object* v_00_u03b1_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_w_81_, lean_object* v_aig_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(v_00_u03b1_78_, v_inst_79_, v_inst_80_, v_w_81_, v_aig_82_, v_x_83_);
lean_dec_ref(v_x_83_);
lean_dec(v_w_81_);
return v_res_84_;
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
