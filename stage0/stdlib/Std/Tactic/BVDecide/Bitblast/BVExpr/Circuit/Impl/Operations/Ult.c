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
static const lean_ctor_object l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_w_6_, lean_object* v_aig_7_, lean_object* v_pair_8_){
_start:
{
lean_object* v_lhs_9_; lean_object* v_rhs_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_61_; 
v_lhs_9_ = lean_ctor_get(v_pair_8_, 0);
v_rhs_10_ = lean_ctor_get(v_pair_8_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_pair_8_);
if (v_isSharedCheck_61_ == 0)
{
v___x_12_ = v_pair_8_;
v_isShared_13_ = v_isSharedCheck_61_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_rhs_10_);
lean_inc(v_lhs_9_);
lean_dec(v_pair_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_61_;
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
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_lhs_9_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_vec_16_);
v___x_20_ = v_reuseFailAlloc_60_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v_res_22_; lean_object* v_ref_23_; uint8_t v_invert_24_; 
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v_w_6_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
lean_ctor_set(v___x_21_, 2, v_trueRef_18_);
v_res_22_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(v_inst_4_, v_inst_5_, v_aig_15_, v___x_21_);
v_ref_23_ = lean_ctor_get(v_res_22_, 1);
lean_inc_ref(v_ref_23_);
v_invert_24_ = lean_ctor_get_uint8(v_ref_23_, sizeof(void*)*1);
if (v_invert_24_ == 0)
{
lean_object* v_aig_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_40_; 
v_aig_25_ = lean_ctor_get(v_res_22_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v_res_22_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; 
v_unused_41_ = lean_ctor_get(v_res_22_, 1);
lean_dec(v_unused_41_);
v___x_27_ = v_res_22_;
v_isShared_28_ = v_isSharedCheck_40_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_aig_25_);
lean_dec(v_res_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_40_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_gate_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_39_; 
v_gate_29_ = lean_ctor_get(v_ref_23_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v_ref_23_);
if (v_isSharedCheck_39_ == 0)
{
v___x_31_ = v_ref_23_;
v_isShared_32_ = v_isSharedCheck_39_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_gate_29_);
lean_dec(v_ref_23_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_39_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_gate_29_);
v___x_34_ = v_reuseFailAlloc_38_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_36_; 
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*1, v___x_17_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 1, v___x_34_);
v___x_36_ = v___x_27_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_aig_25_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
else
{
lean_object* v_aig_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_58_; 
v_aig_42_ = lean_ctor_get(v_res_22_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v_res_22_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; 
v_unused_59_ = lean_ctor_get(v_res_22_, 1);
lean_dec(v_unused_59_);
v___x_44_ = v_res_22_;
v_isShared_45_ = v_isSharedCheck_58_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_aig_42_);
lean_dec(v_res_22_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_58_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v_gate_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_57_; 
v_gate_46_ = lean_ctor_get(v_ref_23_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_ref_23_);
if (v_isSharedCheck_57_ == 0)
{
v___x_48_ = v_ref_23_;
v_isShared_49_ = v_isSharedCheck_57_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_gate_46_);
lean_dec(v_ref_23_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_57_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
uint8_t v___x_50_; lean_object* v___x_52_; 
v___x_50_ = 0;
if (v_isShared_49_ == 0)
{
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_gate_46_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*1, v___x_50_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___x_52_);
v___x_54_ = v___x_44_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_aig_42_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_w_65_, lean_object* v_aig_66_, lean_object* v_pair_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(v_inst_63_, v_inst_64_, v_w_65_, v_aig_66_, v_pair_67_);
return v___x_68_;
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
