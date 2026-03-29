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
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* v_binderName_15_; lean_object* v_binderType_16_; lean_object* v_body_17_; uint8_t v_binderInfo_18_; lean_object* v_d_19_; lean_object* v_b_20_; uint8_t v___y_22_; size_t v___x_26_; size_t v___x_27_; uint8_t v___x_28_; 
v_binderName_15_ = lean_ctor_get(v_e_13_, 0);
v_binderType_16_ = lean_ctor_get(v_e_13_, 1);
v_body_17_ = lean_ctor_get(v_e_13_, 2);
v_binderInfo_18_ = lean_ctor_get_uint8(v_e_13_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_16_);
lean_inc_ref(v_f_x3f_12_);
v_d_19_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_binderType_16_);
lean_inc_ref(v_body_17_);
v_b_20_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_body_17_);
v___x_26_ = lean_ptr_addr(v_binderType_16_);
v___x_27_ = lean_ptr_addr(v_d_19_);
v___x_28_ = lean_usize_dec_eq(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
v___y_22_ = v___x_28_;
goto v___jp_21_;
}
else
{
size_t v___x_29_; size_t v___x_30_; uint8_t v___x_31_; 
v___x_29_ = lean_ptr_addr(v_body_17_);
v___x_30_ = lean_ptr_addr(v_b_20_);
v___x_31_ = lean_usize_dec_eq(v___x_29_, v___x_30_);
v___y_22_ = v___x_31_;
goto v___jp_21_;
}
v___jp_21_:
{
if (v___y_22_ == 0)
{
lean_object* v___x_23_; 
lean_inc(v_binderName_15_);
lean_dec_ref(v_e_13_);
v___x_23_ = l_Lean_Expr_forallE___override(v_binderName_15_, v_d_19_, v_b_20_, v_binderInfo_18_);
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_18_, v_binderInfo_18_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
lean_inc(v_binderName_15_);
lean_dec_ref(v_e_13_);
v___x_25_ = l_Lean_Expr_forallE___override(v_binderName_15_, v_d_19_, v_b_20_, v_binderInfo_18_);
return v___x_25_;
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
lean_object* v_binderName_32_; lean_object* v_binderType_33_; lean_object* v_body_34_; uint8_t v_binderInfo_35_; lean_object* v_d_36_; lean_object* v_b_37_; uint8_t v___y_39_; size_t v___x_43_; size_t v___x_44_; uint8_t v___x_45_; 
v_binderName_32_ = lean_ctor_get(v_e_13_, 0);
v_binderType_33_ = lean_ctor_get(v_e_13_, 1);
v_body_34_ = lean_ctor_get(v_e_13_, 2);
v_binderInfo_35_ = lean_ctor_get_uint8(v_e_13_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_33_);
lean_inc_ref(v_f_x3f_12_);
v_d_36_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_binderType_33_);
lean_inc_ref(v_body_34_);
v_b_37_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_body_34_);
v___x_43_ = lean_ptr_addr(v_binderType_33_);
v___x_44_ = lean_ptr_addr(v_d_36_);
v___x_45_ = lean_usize_dec_eq(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
v___y_39_ = v___x_45_;
goto v___jp_38_;
}
else
{
size_t v___x_46_; size_t v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_ptr_addr(v_body_34_);
v___x_47_ = lean_ptr_addr(v_b_37_);
v___x_48_ = lean_usize_dec_eq(v___x_46_, v___x_47_);
v___y_39_ = v___x_48_;
goto v___jp_38_;
}
v___jp_38_:
{
if (v___y_39_ == 0)
{
lean_object* v___x_40_; 
lean_inc(v_binderName_32_);
lean_dec_ref(v_e_13_);
v___x_40_ = l_Lean_Expr_lam___override(v_binderName_32_, v_d_36_, v_b_37_, v_binderInfo_35_);
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_35_, v_binderInfo_35_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_inc(v_binderName_32_);
lean_dec_ref(v_e_13_);
v___x_42_ = l_Lean_Expr_lam___override(v_binderName_32_, v_d_36_, v_b_37_, v_binderInfo_35_);
return v___x_42_;
}
else
{
lean_dec_ref(v_b_37_);
lean_dec_ref(v_d_36_);
return v_e_13_;
}
}
}
}
case 10:
{
lean_object* v_data_49_; lean_object* v_expr_50_; lean_object* v_b_51_; size_t v___x_52_; size_t v___x_53_; uint8_t v___x_54_; 
v_data_49_ = lean_ctor_get(v_e_13_, 0);
v_expr_50_ = lean_ctor_get(v_e_13_, 1);
lean_inc_ref(v_expr_50_);
v_b_51_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_expr_50_);
v___x_52_ = lean_ptr_addr(v_expr_50_);
v___x_53_ = lean_ptr_addr(v_b_51_);
v___x_54_ = lean_usize_dec_eq(v___x_52_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_inc(v_data_49_);
lean_dec_ref(v_e_13_);
v___x_55_ = l_Lean_Expr_mdata___override(v_data_49_, v_b_51_);
return v___x_55_;
}
else
{
lean_dec_ref(v_b_51_);
return v_e_13_;
}
}
case 8:
{
lean_object* v_declName_56_; lean_object* v_type_57_; lean_object* v_value_58_; lean_object* v_body_59_; uint8_t v_nondep_60_; lean_object* v_t_61_; lean_object* v_v_62_; lean_object* v_b_63_; uint8_t v___y_65_; size_t v___x_71_; size_t v___x_72_; uint8_t v___x_73_; 
v_declName_56_ = lean_ctor_get(v_e_13_, 0);
v_type_57_ = lean_ctor_get(v_e_13_, 1);
v_value_58_ = lean_ctor_get(v_e_13_, 2);
v_body_59_ = lean_ctor_get(v_e_13_, 3);
v_nondep_60_ = lean_ctor_get_uint8(v_e_13_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_57_);
lean_inc_ref_n(v_f_x3f_12_, 2);
v_t_61_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_type_57_);
lean_inc_ref(v_value_58_);
v_v_62_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_value_58_);
lean_inc_ref(v_body_59_);
v_b_63_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_body_59_);
v___x_71_ = lean_ptr_addr(v_type_57_);
v___x_72_ = lean_ptr_addr(v_t_61_);
v___x_73_ = lean_usize_dec_eq(v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
v___y_65_ = v___x_73_;
goto v___jp_64_;
}
else
{
size_t v___x_74_; size_t v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_ptr_addr(v_value_58_);
v___x_75_ = lean_ptr_addr(v_v_62_);
v___x_76_ = lean_usize_dec_eq(v___x_74_, v___x_75_);
v___y_65_ = v___x_76_;
goto v___jp_64_;
}
v___jp_64_:
{
if (v___y_65_ == 0)
{
lean_object* v___x_66_; 
lean_inc(v_declName_56_);
lean_dec_ref(v_e_13_);
v___x_66_ = l_Lean_Expr_letE___override(v_declName_56_, v_t_61_, v_v_62_, v_b_63_, v_nondep_60_);
return v___x_66_;
}
else
{
size_t v___x_67_; size_t v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_ptr_addr(v_body_59_);
v___x_68_ = lean_ptr_addr(v_b_63_);
v___x_69_ = lean_usize_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_inc(v_declName_56_);
lean_dec_ref(v_e_13_);
v___x_70_ = l_Lean_Expr_letE___override(v_declName_56_, v_t_61_, v_v_62_, v_b_63_, v_nondep_60_);
return v___x_70_;
}
else
{
lean_dec_ref(v_b_63_);
lean_dec_ref(v_v_62_);
lean_dec_ref(v_t_61_);
return v_e_13_;
}
}
}
}
case 5:
{
lean_object* v_fn_77_; lean_object* v_arg_78_; lean_object* v_f_79_; lean_object* v_a_80_; uint8_t v___y_82_; size_t v___x_84_; size_t v___x_85_; uint8_t v___x_86_; 
v_fn_77_ = lean_ctor_get(v_e_13_, 0);
v_arg_78_ = lean_ctor_get(v_e_13_, 1);
lean_inc_ref(v_fn_77_);
lean_inc_ref(v_f_x3f_12_);
v_f_79_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_fn_77_);
lean_inc_ref(v_arg_78_);
v_a_80_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_arg_78_);
v___x_84_ = lean_ptr_addr(v_fn_77_);
v___x_85_ = lean_ptr_addr(v_f_79_);
v___x_86_ = lean_usize_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
v___y_82_ = v___x_86_;
goto v___jp_81_;
}
else
{
size_t v___x_87_; size_t v___x_88_; uint8_t v___x_89_; 
v___x_87_ = lean_ptr_addr(v_arg_78_);
v___x_88_ = lean_ptr_addr(v_a_80_);
v___x_89_ = lean_usize_dec_eq(v___x_87_, v___x_88_);
v___y_82_ = v___x_89_;
goto v___jp_81_;
}
v___jp_81_:
{
if (v___y_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec_ref(v_e_13_);
v___x_83_ = l_Lean_Expr_app___override(v_f_79_, v_a_80_);
return v___x_83_;
}
else
{
lean_dec_ref(v_a_80_);
lean_dec_ref(v_f_79_);
return v_e_13_;
}
}
}
case 11:
{
lean_object* v_typeName_90_; lean_object* v_idx_91_; lean_object* v_struct_92_; lean_object* v_b_93_; size_t v___x_94_; size_t v___x_95_; uint8_t v___x_96_; 
v_typeName_90_ = lean_ctor_get(v_e_13_, 0);
v_idx_91_ = lean_ctor_get(v_e_13_, 1);
v_struct_92_ = lean_ctor_get(v_e_13_, 2);
lean_inc_ref(v_struct_92_);
v_b_93_ = l_Lean_Expr_replaceNoCache(v_f_x3f_12_, v_struct_92_);
v___x_94_ = lean_ptr_addr(v_struct_92_);
v___x_95_ = lean_ptr_addr(v_b_93_);
v___x_96_ = lean_usize_dec_eq(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_inc(v_idx_91_);
lean_inc(v_typeName_90_);
lean_dec_ref(v_e_13_);
v___x_97_ = l_Lean_Expr_proj___override(v_typeName_90_, v_idx_91_, v_b_93_);
return v___x_97_;
}
else
{
lean_dec_ref(v_b_93_);
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
lean_object* v_val_98_; 
lean_dec_ref(v_e_13_);
lean_dec_ref(v_f_x3f_12_);
v_val_98_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_val_98_);
lean_dec_ref(v___x_14_);
return v_val_98_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
