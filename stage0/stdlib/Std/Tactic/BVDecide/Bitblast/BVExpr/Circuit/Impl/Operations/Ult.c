// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_xor(uint8_t, uint8_t);
static const lean_ctor_object l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult_0__Std_Tactic_BVDecide_BVPred_mkUlt_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult_0__Std_Tactic_BVDecide_BVPred_mkUlt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult_0__Std_Tactic_BVDecide_BVPred_mkUlt_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_w_6_, lean_object* v_aig_7_, lean_object* v_pair_8_){
_start:
{
lean_object* v_lhs_9_; lean_object* v_rhs_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_43_; 
v_lhs_9_ = lean_ctor_get(v_pair_8_, 0);
v_rhs_10_ = lean_ctor_get(v_pair_8_, 1);
v_isSharedCheck_43_ = !lean_is_exclusive(v_pair_8_);
if (v_isSharedCheck_43_ == 0)
{
v___x_12_ = v_pair_8_;
v_isShared_13_ = v_isSharedCheck_43_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_rhs_10_);
lean_inc(v_lhs_9_);
lean_dec(v_pair_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_43_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v_res_14_; lean_object* v_aig_15_; lean_object* v_vec_16_; uint8_t v___x_17_; lean_object* v_trueRef_18_; lean_object* v___x_20_; 
lean_inc_ref(v_inst_5_);
lean_inc_ref(v_inst_4_);
v_res_14_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(v_inst_4_, v_inst_5_, v_w_6_, v_aig_7_, v_rhs_10_);
v_aig_15_ = lean_ctor_get(v_res_14_, 0);
lean_inc_ref(v_aig_15_);
v_vec_16_ = lean_ctor_get(v_res_14_, 1);
lean_inc_ref(v_vec_16_);
lean_dec_ref(v_res_14_);
v___x_17_ = 1;
v_trueRef_18_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0));
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v_vec_16_);
v___x_20_ = v___x_12_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_lhs_9_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_vec_16_);
v___x_20_ = v_reuseFailAlloc_42_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v_res_22_; lean_object* v_ref_23_; lean_object* v_aig_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_41_; 
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v_w_6_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
lean_ctor_set(v___x_21_, 2, v_trueRef_18_);
v_res_22_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(v_inst_4_, v_inst_5_, v_aig_15_, v___x_21_);
v_ref_23_ = lean_ctor_get(v_res_22_, 1);
v_aig_24_ = lean_ctor_get(v_res_22_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_res_22_);
if (v_isSharedCheck_41_ == 0)
{
v___x_26_ = v_res_22_;
v_isShared_27_ = v_isSharedCheck_41_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_ref_23_);
lean_inc(v_aig_24_);
lean_dec(v_res_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_41_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v_gate_28_; uint8_t v_invert_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_40_; 
v_gate_28_ = lean_ctor_get(v_ref_23_, 0);
v_invert_29_ = lean_ctor_get_uint8(v_ref_23_, sizeof(void*)*1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_ref_23_);
if (v_isSharedCheck_40_ == 0)
{
v___x_31_ = v_ref_23_;
v_isShared_32_ = v_isSharedCheck_40_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_gate_28_);
lean_dec(v_ref_23_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_40_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
uint8_t v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_bool_xor(v___x_17_, v_invert_29_);
if (v_isShared_32_ == 0)
{
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_gate_28_);
v___x_35_ = v_reuseFailAlloc_39_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
lean_ctor_set_uint8(v___x_35_, sizeof(void*)*1, v___x_33_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_35_);
v___x_37_ = v___x_26_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_aig_24_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object* v_00_u03b1_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_w_47_, lean_object* v_aig_48_, lean_object* v_pair_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(v_inst_45_, v_inst_46_, v_w_47_, v_aig_48_, v_pair_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult_0__Std_Tactic_BVDecide_BVPred_mkUlt_match__1_splitter___redArg(lean_object* v_pair_51_, lean_object* v_h__1_52_){
_start:
{
lean_object* v_lhs_53_; lean_object* v_rhs_54_; lean_object* v___x_55_; 
v_lhs_53_ = lean_ctor_get(v_pair_51_, 0);
lean_inc_ref(v_lhs_53_);
v_rhs_54_ = lean_ctor_get(v_pair_51_, 1);
lean_inc_ref(v_rhs_54_);
lean_dec_ref(v_pair_51_);
v___x_55_ = lean_apply_2(v_h__1_52_, v_lhs_53_, v_rhs_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult_0__Std_Tactic_BVDecide_BVPred_mkUlt_match__1_splitter(lean_object* v_00_u03b1_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_w_59_, lean_object* v_aig_60_, lean_object* v_motive_61_, lean_object* v_pair_62_, lean_object* v_h__1_63_){
_start:
{
lean_object* v_lhs_64_; lean_object* v_rhs_65_; lean_object* v___x_66_; 
v_lhs_64_ = lean_ctor_get(v_pair_62_, 0);
lean_inc_ref(v_lhs_64_);
v_rhs_65_ = lean_ctor_get(v_pair_62_, 1);
lean_inc_ref(v_rhs_65_);
lean_dec_ref(v_pair_62_);
v___x_66_ = lean_apply_2(v_h__1_63_, v_lhs_64_, v_rhs_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult_0__Std_Tactic_BVDecide_BVPred_mkUlt_match__1_splitter___boxed(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_w_70_, lean_object* v_aig_71_, lean_object* v_motive_72_, lean_object* v_pair_73_, lean_object* v_h__1_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult_0__Std_Tactic_BVDecide_BVPred_mkUlt_match__1_splitter(v_00_u03b1_67_, v_inst_68_, v_inst_69_, v_w_70_, v_aig_71_, v_motive_72_, v_pair_73_, v_h__1_74_);
lean_dec_ref(v_aig_71_);
lean_dec(v_w_70_);
lean_dec_ref(v_inst_69_);
lean_dec_ref(v_inst_68_);
return v_res_75_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
}
#ifdef __cplusplus
}
#endif
