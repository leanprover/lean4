// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD
// Imports: public import Std.Sat.AIG.RefVec
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg(lean_object* v_target_1_){
_start:
{
lean_object* v_w_2_; lean_object* v_vec_3_; lean_object* v_idx_4_; uint8_t v___x_5_; 
v_w_2_ = lean_ctor_get(v_target_1_, 0);
v_vec_3_ = lean_ctor_get(v_target_1_, 1);
v_idx_4_ = lean_ctor_get(v_target_1_, 2);
v___x_5_ = lean_nat_dec_lt(v_idx_4_, v_w_2_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set_uint8(v___x_7_, sizeof(void*)*1, v___x_5_);
return v___x_7_;
}
else
{
lean_object* v_ref_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_ref_8_ = lean_array_fget_borrowed(v_vec_3_, v_idx_4_);
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_shiftr(v_ref_8_, v___x_9_);
v___x_11_ = lean_nat_land(v___x_9_, v_ref_8_);
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_nat_dec_eq(v___x_11_, v___x_12_);
lean_dec(v___x_11_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_14_, 0, v___x_10_);
lean_ctor_set_uint8(v___x_14_, sizeof(void*)*1, v___x_5_);
return v___x_14_;
}
else
{
uint8_t v___x_15_; lean_object* v___x_16_; 
v___x_15_ = 0;
v___x_16_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_16_, 0, v___x_10_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1, v___x_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg___boxed(lean_object* v_target_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg(v_target_17_);
lean_dec_ref(v_target_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_aig_22_, lean_object* v_target_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg(v_target_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_aig_28_, lean_object* v_target_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD(v_00_u03b1_25_, v_inst_26_, v_inst_27_, v_aig_28_, v_target_29_);
lean_dec_ref(v_target_29_);
lean_dec_ref(v_aig_28_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_26_);
return v_res_30_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_RefVec(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_RefVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_RefVec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_RefVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin);
}
#ifdef __cplusplus
}
#endif
