// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: public import Lean.Expr public import Lean.Util.PtrSet
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object* v_f_x3f_3_, lean_object* v_e_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_replace_expr(v_f_x3f_3_, v_e_4_);
lean_dec_ref(v_e_4_);
lean_dec_ref(v_f_x3f_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object* v_f_x3f_6_, lean_object* v_e_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_replace_expr(v_f_x3f_6_, v_e_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object* v_f_x3f_9_, lean_object* v_e_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Expr_replace(v_f_x3f_9_, v_e_10_);
lean_dec_ref(v_e_10_);
lean_dec_ref(v_f_x3f_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* v_f_x3f_12_, lean_object* v_e_13_){
_start:
{
lean_object* v___x_14_; 
lean_inc_ref(v_f_x3f_12_);
lean_inc_ref(v_e_13_);
v___x_14_ = lean_apply_1(v_f_x3f_12_, v_e_13_);
if (lean_obj_tag(v___x_14_) == 0)
{
switch(lean_obj_tag(v_e_13_))
{
case 7:
{
lean_object* v_binderName_15_; lean_object* v_binderType_16_; lean_object* v_body_17_; uint8_t v_binderInfo_18_; lean_object* v_d_19_; lean_object* v_b_20_; size_t v___x_21_; size_t v___x_22_; uint8_t v___x_23_; 
v_binderName_15_ = lean_ctor_get(v_e_13_, 0);
v_binderType_16_ = lean_ctor_get(v_e_13_, 1);
v_body_17_ = lean_ctor_get(v_e_13_, 2);
v_binderInfo_18_ = lean_ctor_get_uint8(v_e_13_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_16_);
lean_inc_ref(v_f_x3f_12_);
v_d_19_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_binderType_16_);
lean_inc_ref(v_body_17_);
v_b_20_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_body_17_);
v___x_21_ = lean_ptr_addr(v_binderType_16_);
v___x_22_ = lean_ptr_addr(v_d_19_);
v___x_23_ = lean_usize_dec_eq(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_inc(v_binderName_15_);
lean_dec_ref_known(v_e_13_, 3);
v___x_24_ = l_Lean_Expr_forallE___override(v_binderName_15_, v_d_19_, v_b_20_, v_binderInfo_18_);
return v___x_24_;
}
else
{
size_t v___x_25_; size_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = lean_ptr_addr(v_body_17_);
v___x_26_ = lean_ptr_addr(v_b_20_);
v___x_27_ = lean_usize_dec_eq(v___x_25_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_inc(v_binderName_15_);
lean_dec_ref_known(v_e_13_, 3);
v___x_28_ = l_Lean_Expr_forallE___override(v_binderName_15_, v_d_19_, v_b_20_, v_binderInfo_18_);
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_18_, v_binderInfo_18_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
lean_inc(v_binderName_15_);
lean_dec_ref_known(v_e_13_, 3);
v___x_30_ = l_Lean_Expr_forallE___override(v_binderName_15_, v_d_19_, v_b_20_, v_binderInfo_18_);
return v___x_30_;
}
else
{
lean_dec_ref(v_b_20_);
lean_dec_ref(v_d_19_);
return v_e_13_;
}
}
}
}
case 6:
{
lean_object* v_binderName_31_; lean_object* v_binderType_32_; lean_object* v_body_33_; uint8_t v_binderInfo_34_; lean_object* v_d_35_; lean_object* v_b_36_; size_t v___x_37_; size_t v___x_38_; uint8_t v___x_39_; 
v_binderName_31_ = lean_ctor_get(v_e_13_, 0);
v_binderType_32_ = lean_ctor_get(v_e_13_, 1);
v_body_33_ = lean_ctor_get(v_e_13_, 2);
v_binderInfo_34_ = lean_ctor_get_uint8(v_e_13_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_32_);
lean_inc_ref(v_f_x3f_12_);
v_d_35_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_binderType_32_);
lean_inc_ref(v_body_33_);
v_b_36_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_body_33_);
v___x_37_ = lean_ptr_addr(v_binderType_32_);
v___x_38_ = lean_ptr_addr(v_d_35_);
v___x_39_ = lean_usize_dec_eq(v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
lean_inc(v_binderName_31_);
lean_dec_ref_known(v_e_13_, 3);
v___x_40_ = l_Lean_Expr_lam___override(v_binderName_31_, v_d_35_, v_b_36_, v_binderInfo_34_);
return v___x_40_;
}
else
{
size_t v___x_41_; size_t v___x_42_; uint8_t v___x_43_; 
v___x_41_ = lean_ptr_addr(v_body_33_);
v___x_42_ = lean_ptr_addr(v_b_36_);
v___x_43_ = lean_usize_dec_eq(v___x_41_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
lean_inc(v_binderName_31_);
lean_dec_ref_known(v_e_13_, 3);
v___x_44_ = l_Lean_Expr_lam___override(v_binderName_31_, v_d_35_, v_b_36_, v_binderInfo_34_);
return v___x_44_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_34_, v_binderInfo_34_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_inc(v_binderName_31_);
lean_dec_ref_known(v_e_13_, 3);
v___x_46_ = l_Lean_Expr_lam___override(v_binderName_31_, v_d_35_, v_b_36_, v_binderInfo_34_);
return v___x_46_;
}
else
{
lean_dec_ref(v_b_36_);
lean_dec_ref(v_d_35_);
return v_e_13_;
}
}
}
}
case 10:
{
lean_object* v_data_47_; lean_object* v_expr_48_; lean_object* v_b_49_; size_t v___x_50_; size_t v___x_51_; uint8_t v___x_52_; 
v_data_47_ = lean_ctor_get(v_e_13_, 0);
v_expr_48_ = lean_ctor_get(v_e_13_, 1);
lean_inc_ref(v_expr_48_);
v_b_49_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_expr_48_);
v___x_50_ = lean_ptr_addr(v_expr_48_);
v___x_51_ = lean_ptr_addr(v_b_49_);
v___x_52_ = lean_usize_dec_eq(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; 
lean_inc(v_data_47_);
lean_dec_ref_known(v_e_13_, 2);
v___x_53_ = l_Lean_Expr_mdata___override(v_data_47_, v_b_49_);
return v___x_53_;
}
else
{
lean_dec_ref(v_b_49_);
return v_e_13_;
}
}
case 8:
{
lean_object* v_declName_54_; lean_object* v_type_55_; lean_object* v_value_56_; lean_object* v_body_57_; uint8_t v_nondep_58_; lean_object* v_t_59_; lean_object* v_v_60_; lean_object* v_b_61_; size_t v___x_62_; size_t v___x_63_; uint8_t v___x_64_; 
v_declName_54_ = lean_ctor_get(v_e_13_, 0);
v_type_55_ = lean_ctor_get(v_e_13_, 1);
v_value_56_ = lean_ctor_get(v_e_13_, 2);
v_body_57_ = lean_ctor_get(v_e_13_, 3);
v_nondep_58_ = lean_ctor_get_uint8(v_e_13_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_55_);
lean_inc_ref_n(v_f_x3f_12_, 2);
v_t_59_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_type_55_);
lean_inc_ref(v_value_56_);
v_v_60_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_value_56_);
lean_inc_ref(v_body_57_);
v_b_61_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_body_57_);
v___x_62_ = lean_ptr_addr(v_type_55_);
v___x_63_ = lean_ptr_addr(v_t_59_);
v___x_64_ = lean_usize_dec_eq(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_inc(v_declName_54_);
lean_dec_ref_known(v_e_13_, 4);
v___x_65_ = l_Lean_Expr_letE___override(v_declName_54_, v_t_59_, v_v_60_, v_b_61_, v_nondep_58_);
return v___x_65_;
}
else
{
size_t v___x_66_; size_t v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_ptr_addr(v_value_56_);
v___x_67_ = lean_ptr_addr(v_v_60_);
v___x_68_ = lean_usize_dec_eq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_inc(v_declName_54_);
lean_dec_ref_known(v_e_13_, 4);
v___x_69_ = l_Lean_Expr_letE___override(v_declName_54_, v_t_59_, v_v_60_, v_b_61_, v_nondep_58_);
return v___x_69_;
}
else
{
size_t v___x_70_; size_t v___x_71_; uint8_t v___x_72_; 
v___x_70_ = lean_ptr_addr(v_body_57_);
v___x_71_ = lean_ptr_addr(v_b_61_);
v___x_72_ = lean_usize_dec_eq(v___x_70_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_inc(v_declName_54_);
lean_dec_ref_known(v_e_13_, 4);
v___x_73_ = l_Lean_Expr_letE___override(v_declName_54_, v_t_59_, v_v_60_, v_b_61_, v_nondep_58_);
return v___x_73_;
}
else
{
lean_dec_ref(v_b_61_);
lean_dec_ref(v_v_60_);
lean_dec_ref(v_t_59_);
return v_e_13_;
}
}
}
}
case 5:
{
lean_object* v_fn_74_; lean_object* v_arg_75_; lean_object* v_f_76_; lean_object* v_a_77_; size_t v___x_78_; size_t v___x_79_; uint8_t v___x_80_; 
v_fn_74_ = lean_ctor_get(v_e_13_, 0);
v_arg_75_ = lean_ctor_get(v_e_13_, 1);
lean_inc_ref(v_fn_74_);
lean_inc_ref(v_f_x3f_12_);
v_f_76_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_fn_74_);
lean_inc_ref(v_arg_75_);
v_a_77_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_arg_75_);
v___x_78_ = lean_ptr_addr(v_fn_74_);
v___x_79_ = lean_ptr_addr(v_f_76_);
v___x_80_ = lean_usize_dec_eq(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec_ref_known(v_e_13_, 2);
v___x_81_ = l_Lean_Expr_app___override(v_f_76_, v_a_77_);
return v___x_81_;
}
else
{
size_t v___x_82_; size_t v___x_83_; uint8_t v___x_84_; 
v___x_82_ = lean_ptr_addr(v_arg_75_);
v___x_83_ = lean_ptr_addr(v_a_77_);
v___x_84_ = lean_usize_dec_eq(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_dec_ref_known(v_e_13_, 2);
v___x_85_ = l_Lean_Expr_app___override(v_f_76_, v_a_77_);
return v___x_85_;
}
else
{
lean_dec_ref(v_a_77_);
lean_dec_ref(v_f_76_);
return v_e_13_;
}
}
}
case 11:
{
lean_object* v_typeName_86_; lean_object* v_idx_87_; lean_object* v_struct_88_; lean_object* v_b_89_; size_t v___x_90_; size_t v___x_91_; uint8_t v___x_92_; 
v_typeName_86_ = lean_ctor_get(v_e_13_, 0);
v_idx_87_ = lean_ctor_get(v_e_13_, 1);
v_struct_88_ = lean_ctor_get(v_e_13_, 2);
lean_inc_ref(v_struct_88_);
v_b_89_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_struct_88_);
v___x_90_ = lean_ptr_addr(v_struct_88_);
v___x_91_ = lean_ptr_addr(v_b_89_);
v___x_92_ = lean_usize_dec_eq(v___x_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_inc(v_idx_87_);
lean_inc(v_typeName_86_);
lean_dec_ref_known(v_e_13_, 3);
v___x_93_ = l_Lean_Expr_proj___override(v_typeName_86_, v_idx_87_, v_b_89_);
return v___x_93_;
}
else
{
lean_dec_ref(v_b_89_);
return v_e_13_;
}
}
default: 
{
lean_dec_ref(v_f_x3f_12_);
return v_e_13_;
}
}
}
else
{
lean_object* v_val_94_; 
lean_dec_ref(v_e_13_);
lean_dec_ref(v_f_x3f_12_);
v_val_94_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_val_94_);
lean_dec_ref_known(v___x_14_, 1);
return v_val_94_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_ReplaceExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_ReplaceExpr(builtin);
}
#ifdef __cplusplus
}
#endif
