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
LEAN_EXPORT void l_Lean_Expr_replaceImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_x3f_1_ = stack[0].m_obj;
lean_object* v_e_2_ = stack[1].m_obj;
lean_object* v_res_3_;
v_res_3_ = lean_replace_expr(v_f_x3f_1_, v_e_2_);
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object* v_f_x3f_4_, lean_object* v_e_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_replace_expr(v_f_x3f_4_, v_e_5_);
lean_dec_ref(v_e_5_);
lean_dec_ref(v_f_x3f_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object* v_f_x3f_7_, lean_object* v_e_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_replace_expr(v_f_x3f_7_, v_e_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object* v_f_x3f_10_, lean_object* v_e_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Expr_replace(v_f_x3f_10_, v_e_11_);
lean_dec_ref(v_e_11_);
lean_dec_ref(v_f_x3f_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* v_f_x3f_13_, lean_object* v_e_14_){
_start:
{
lean_object* v___x_15_; 
lean_inc_ref(v_f_x3f_13_);
lean_inc_ref(v_e_14_);
v___x_15_ = lean_apply_1(v_f_x3f_13_, v_e_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
switch(lean_obj_tag(v_e_14_))
{
case 7:
{
lean_object* v_binderName_16_; lean_object* v_binderType_17_; lean_object* v_body_18_; uint8_t v_binderInfo_19_; lean_object* v_d_20_; lean_object* v_b_21_; size_t v___x_22_; size_t v___x_23_; uint8_t v___x_24_; 
v_binderName_16_ = lean_ctor_get(v_e_14_, 0);
v_binderType_17_ = lean_ctor_get(v_e_14_, 1);
v_body_18_ = lean_ctor_get(v_e_14_, 2);
v_binderInfo_19_ = lean_ctor_get_uint8(v_e_14_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_17_);
lean_inc_ref(v_f_x3f_13_);
v_d_20_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_binderType_17_);
lean_inc_ref(v_body_18_);
v_b_21_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_body_18_);
v___x_22_ = lean_ptr_addr(v_binderType_17_);
v___x_23_ = lean_ptr_addr(v_d_20_);
v___x_24_ = lean_usize_dec_eq(v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
lean_inc(v_binderName_16_);
lean_dec_ref_known(v_e_14_, 3);
v___x_25_ = l_Lean_Expr_forallE___override(v_binderName_16_, v_d_20_, v_b_21_, v_binderInfo_19_);
return v___x_25_;
}
else
{
size_t v___x_26_; size_t v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_ptr_addr(v_body_18_);
v___x_27_ = lean_ptr_addr(v_b_21_);
v___x_28_ = lean_usize_dec_eq(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
lean_inc(v_binderName_16_);
lean_dec_ref_known(v_e_14_, 3);
v___x_29_ = l_Lean_Expr_forallE___override(v_binderName_16_, v_d_20_, v_b_21_, v_binderInfo_19_);
return v___x_29_;
}
else
{
uint8_t v___x_30_; 
v___x_30_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_19_, v_binderInfo_19_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; 
lean_inc(v_binderName_16_);
lean_dec_ref_known(v_e_14_, 3);
v___x_31_ = l_Lean_Expr_forallE___override(v_binderName_16_, v_d_20_, v_b_21_, v_binderInfo_19_);
return v___x_31_;
}
else
{
lean_dec_ref(v_b_21_);
lean_dec_ref(v_d_20_);
return v_e_14_;
}
}
}
}
case 6:
{
lean_object* v_binderName_32_; lean_object* v_binderType_33_; lean_object* v_body_34_; uint8_t v_binderInfo_35_; lean_object* v_d_36_; lean_object* v_b_37_; size_t v___x_38_; size_t v___x_39_; uint8_t v___x_40_; 
v_binderName_32_ = lean_ctor_get(v_e_14_, 0);
v_binderType_33_ = lean_ctor_get(v_e_14_, 1);
v_body_34_ = lean_ctor_get(v_e_14_, 2);
v_binderInfo_35_ = lean_ctor_get_uint8(v_e_14_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_33_);
lean_inc_ref(v_f_x3f_13_);
v_d_36_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_binderType_33_);
lean_inc_ref(v_body_34_);
v_b_37_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_body_34_);
v___x_38_ = lean_ptr_addr(v_binderType_33_);
v___x_39_ = lean_ptr_addr(v_d_36_);
v___x_40_ = lean_usize_dec_eq(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; 
lean_inc(v_binderName_32_);
lean_dec_ref_known(v_e_14_, 3);
v___x_41_ = l_Lean_Expr_lam___override(v_binderName_32_, v_d_36_, v_b_37_, v_binderInfo_35_);
return v___x_41_;
}
else
{
size_t v___x_42_; size_t v___x_43_; uint8_t v___x_44_; 
v___x_42_ = lean_ptr_addr(v_body_34_);
v___x_43_ = lean_ptr_addr(v_b_37_);
v___x_44_ = lean_usize_dec_eq(v___x_42_, v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_inc(v_binderName_32_);
lean_dec_ref_known(v_e_14_, 3);
v___x_45_ = l_Lean_Expr_lam___override(v_binderName_32_, v_d_36_, v_b_37_, v_binderInfo_35_);
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_35_, v_binderInfo_35_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
lean_inc(v_binderName_32_);
lean_dec_ref_known(v_e_14_, 3);
v___x_47_ = l_Lean_Expr_lam___override(v_binderName_32_, v_d_36_, v_b_37_, v_binderInfo_35_);
return v___x_47_;
}
else
{
lean_dec_ref(v_b_37_);
lean_dec_ref(v_d_36_);
return v_e_14_;
}
}
}
}
case 10:
{
lean_object* v_data_48_; lean_object* v_expr_49_; lean_object* v_b_50_; size_t v___x_51_; size_t v___x_52_; uint8_t v___x_53_; 
v_data_48_ = lean_ctor_get(v_e_14_, 0);
v_expr_49_ = lean_ctor_get(v_e_14_, 1);
lean_inc_ref(v_expr_49_);
v_b_50_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_expr_49_);
v___x_51_ = lean_ptr_addr(v_expr_49_);
v___x_52_ = lean_ptr_addr(v_b_50_);
v___x_53_ = lean_usize_dec_eq(v___x_51_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_inc(v_data_48_);
lean_dec_ref_known(v_e_14_, 2);
v___x_54_ = l_Lean_Expr_mdata___override(v_data_48_, v_b_50_);
return v___x_54_;
}
else
{
lean_dec_ref(v_b_50_);
return v_e_14_;
}
}
case 8:
{
lean_object* v_declName_55_; lean_object* v_type_56_; lean_object* v_value_57_; lean_object* v_body_58_; uint8_t v_nondep_59_; lean_object* v_t_60_; lean_object* v_v_61_; lean_object* v_b_62_; size_t v___x_63_; size_t v___x_64_; uint8_t v___x_65_; 
v_declName_55_ = lean_ctor_get(v_e_14_, 0);
v_type_56_ = lean_ctor_get(v_e_14_, 1);
v_value_57_ = lean_ctor_get(v_e_14_, 2);
v_body_58_ = lean_ctor_get(v_e_14_, 3);
v_nondep_59_ = lean_ctor_get_uint8(v_e_14_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_56_);
lean_inc_ref_n(v_f_x3f_13_, 2);
v_t_60_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_type_56_);
lean_inc_ref(v_value_57_);
v_v_61_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_value_57_);
lean_inc_ref(v_body_58_);
v_b_62_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_body_58_);
v___x_63_ = lean_ptr_addr(v_type_56_);
v___x_64_ = lean_ptr_addr(v_t_60_);
v___x_65_ = lean_usize_dec_eq(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
lean_inc(v_declName_55_);
lean_dec_ref_known(v_e_14_, 4);
v___x_66_ = l_Lean_Expr_letE___override(v_declName_55_, v_t_60_, v_v_61_, v_b_62_, v_nondep_59_);
return v___x_66_;
}
else
{
size_t v___x_67_; size_t v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_ptr_addr(v_value_57_);
v___x_68_ = lean_ptr_addr(v_v_61_);
v___x_69_ = lean_usize_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_inc(v_declName_55_);
lean_dec_ref_known(v_e_14_, 4);
v___x_70_ = l_Lean_Expr_letE___override(v_declName_55_, v_t_60_, v_v_61_, v_b_62_, v_nondep_59_);
return v___x_70_;
}
else
{
size_t v___x_71_; size_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = lean_ptr_addr(v_body_58_);
v___x_72_ = lean_ptr_addr(v_b_62_);
v___x_73_ = lean_usize_dec_eq(v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
lean_inc(v_declName_55_);
lean_dec_ref_known(v_e_14_, 4);
v___x_74_ = l_Lean_Expr_letE___override(v_declName_55_, v_t_60_, v_v_61_, v_b_62_, v_nondep_59_);
return v___x_74_;
}
else
{
lean_dec_ref(v_b_62_);
lean_dec_ref(v_v_61_);
lean_dec_ref(v_t_60_);
return v_e_14_;
}
}
}
}
case 5:
{
lean_object* v_fn_75_; lean_object* v_arg_76_; lean_object* v_f_77_; lean_object* v_a_78_; size_t v___x_79_; size_t v___x_80_; uint8_t v___x_81_; 
v_fn_75_ = lean_ctor_get(v_e_14_, 0);
v_arg_76_ = lean_ctor_get(v_e_14_, 1);
lean_inc_ref(v_fn_75_);
lean_inc_ref(v_f_x3f_13_);
v_f_77_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_fn_75_);
lean_inc_ref(v_arg_76_);
v_a_78_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_arg_76_);
v___x_79_ = lean_ptr_addr(v_fn_75_);
v___x_80_ = lean_ptr_addr(v_f_77_);
v___x_81_ = lean_usize_dec_eq(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_dec_ref_known(v_e_14_, 2);
v___x_82_ = l_Lean_Expr_app___override(v_f_77_, v_a_78_);
return v___x_82_;
}
else
{
size_t v___x_83_; size_t v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_ptr_addr(v_arg_76_);
v___x_84_ = lean_ptr_addr(v_a_78_);
v___x_85_ = lean_usize_dec_eq(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_dec_ref_known(v_e_14_, 2);
v___x_86_ = l_Lean_Expr_app___override(v_f_77_, v_a_78_);
return v___x_86_;
}
else
{
lean_dec_ref(v_a_78_);
lean_dec_ref(v_f_77_);
return v_e_14_;
}
}
}
case 11:
{
lean_object* v_typeName_87_; lean_object* v_idx_88_; lean_object* v_struct_89_; lean_object* v_b_90_; size_t v___x_91_; size_t v___x_92_; uint8_t v___x_93_; 
v_typeName_87_ = lean_ctor_get(v_e_14_, 0);
v_idx_88_ = lean_ctor_get(v_e_14_, 1);
v_struct_89_ = lean_ctor_get(v_e_14_, 2);
lean_inc_ref(v_struct_89_);
v_b_90_ = l_Lean_Expr_replaceNoCache(v_f_x3f_13_, v_struct_89_);
v___x_91_ = lean_ptr_addr(v_struct_89_);
v___x_92_ = lean_ptr_addr(v_b_90_);
v___x_93_ = lean_usize_dec_eq(v___x_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_inc(v_idx_88_);
lean_inc(v_typeName_87_);
lean_dec_ref_known(v_e_14_, 3);
v___x_94_ = l_Lean_Expr_proj___override(v_typeName_87_, v_idx_88_, v_b_90_);
return v___x_94_;
}
else
{
lean_dec_ref(v_b_90_);
return v_e_14_;
}
}
default: 
{
lean_dec_ref(v_f_x3f_13_);
return v_e_14_;
}
}
}
else
{
lean_object* v_val_95_; 
lean_dec_ref(v_e_14_);
lean_dec_ref(v_f_x3f_13_);
v_val_95_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v___x_15_, 1);
return v_val_95_;
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
