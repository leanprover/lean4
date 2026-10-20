// Lean compiler output
// Module: Std.Sat.AIG.CachedLemmas
// Imports: public import Std.Sat.AIG.Cached import Init.Data.Nat.Order import Init.Data.Order.Lemmas
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_apply_1(v_h__2_3_, lean_box(0));
return v___x_4_;
}
else
{
lean_object* v_val_5_; lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v_val_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref_known(v_x_1_, 1);
v___x_6_ = lean_apply_2(v_h__1_2_, v_val_5_, lean_box(0));
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(lean_object* v_00_u03b1_7_, lean_object* v_decls_8_, lean_object* v_decl_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v___x_14_; 
lean_dec(v_h__1_12_);
v___x_14_ = lean_apply_1(v_h__2_13_, lean_box(0));
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_13_);
v_val_15_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_11_, 1);
v___x_16_ = lean_apply_2(v_h__1_12_, v_val_15_, lean_box(0));
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(lean_object* v_00_u03b1_17_, lean_object* v_decls_18_, lean_object* v_decl_19_, lean_object* v_motive_20_, lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(v_00_u03b1_17_, v_decls_18_, v_decl_19_, v_motive_20_, v_x_21_, v_h__1_22_, v_h__2_23_);
lean_dec(v_decl_19_);
lean_dec_ref(v_decls_18_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_, lean_object* v_h__3_28_){
_start:
{
switch(lean_obj_tag(v_x_25_))
{
case 0:
{
lean_object* v___x_29_; 
lean_dec(v_h__3_28_);
lean_dec(v_h__2_27_);
v___x_29_ = lean_apply_1(v_h__1_26_, lean_box(0));
return v___x_29_;
}
case 1:
{
lean_object* v_idx_30_; lean_object* v___x_31_; 
lean_dec(v_h__3_28_);
lean_dec(v_h__1_26_);
v_idx_30_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_idx_30_);
lean_dec_ref_known(v_x_25_, 1);
v___x_31_ = lean_apply_2(v_h__2_27_, v_idx_30_, lean_box(0));
return v___x_31_;
}
default: 
{
lean_object* v_l_32_; lean_object* v_r_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_27_);
lean_dec(v_h__1_26_);
v_l_32_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_l_32_);
v_r_33_ = lean_ctor_get(v_x_25_, 1);
lean_inc(v_r_33_);
lean_dec_ref_known(v_x_25_, 2);
v___x_34_ = lean_apply_3(v_h__3_28_, v_l_32_, v_r_33_, lean_box(0));
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_35_, lean_object* v_motive_36_, lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_, lean_object* v_h__3_40_){
_start:
{
switch(lean_obj_tag(v_x_37_))
{
case 0:
{
lean_object* v___x_41_; 
lean_dec(v_h__3_40_);
lean_dec(v_h__2_39_);
v___x_41_ = lean_apply_1(v_h__1_38_, lean_box(0));
return v___x_41_;
}
case 1:
{
lean_object* v_idx_42_; lean_object* v___x_43_; 
lean_dec(v_h__3_40_);
lean_dec(v_h__1_38_);
v_idx_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_idx_42_);
lean_dec_ref_known(v_x_37_, 1);
v___x_43_ = lean_apply_2(v_h__2_39_, v_idx_42_, lean_box(0));
return v___x_43_;
}
default: 
{
lean_object* v_l_44_; lean_object* v_r_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_39_);
lean_dec(v_h__1_38_);
v_l_44_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_l_44_);
v_r_45_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_r_45_);
lean_dec_ref_known(v_x_37_, 2);
v___x_46_ = lean_apply_3(v_h__3_40_, v_l_44_, v_r_45_, lean_box(0));
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___redArg(lean_object* v_lhsVal_47_, lean_object* v_rhsVal_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_, lean_object* v_h__4_52_, lean_object* v_h__5_53_){
_start:
{
if (lean_obj_tag(v_lhsVal_47_) == 1)
{
lean_object* v_val_54_; uint8_t v___x_55_; 
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
v_val_54_ = lean_ctor_get(v_lhsVal_47_, 0);
v___x_55_ = lean_unbox(v_val_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; 
lean_dec_ref_known(v_lhsVal_47_, 1);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
v___x_56_ = lean_apply_1(v_h__1_49_, v_rhsVal_48_);
return v___x_56_;
}
else
{
lean_dec(v_h__1_49_);
if (lean_obj_tag(v_rhsVal_48_) == 1)
{
lean_object* v_val_57_; uint8_t v___x_58_; 
v_val_57_ = lean_ctor_get(v_rhsVal_48_, 0);
v___x_58_ = lean_unbox(v_val_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; 
lean_dec_ref_known(v_rhsVal_48_, 1);
lean_dec(v_h__3_51_);
v___x_59_ = lean_apply_2(v_h__2_50_, v_lhsVal_47_, lean_box(0));
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
lean_dec_ref_known(v_lhsVal_47_, 1);
lean_dec(v_h__2_50_);
v___x_60_ = lean_apply_2(v_h__3_51_, v_rhsVal_48_, lean_box(0));
return v___x_60_;
}
}
else
{
lean_object* v___x_61_; 
lean_dec_ref_known(v_lhsVal_47_, 1);
lean_dec(v_h__2_50_);
v___x_61_ = lean_apply_2(v_h__3_51_, v_rhsVal_48_, lean_box(0));
return v___x_61_;
}
}
}
else
{
lean_dec(v_h__3_51_);
lean_dec(v_h__1_49_);
if (lean_obj_tag(v_rhsVal_48_) == 1)
{
lean_object* v_val_62_; uint8_t v___x_63_; 
lean_dec(v_h__5_53_);
v_val_62_ = lean_ctor_get(v_rhsVal_48_, 0);
lean_inc(v_val_62_);
lean_dec_ref_known(v_rhsVal_48_, 1);
v___x_63_ = lean_unbox(v_val_62_);
lean_dec(v_val_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_dec(v_h__4_52_);
v___x_64_ = lean_apply_2(v_h__2_50_, v_lhsVal_47_, lean_box(0));
return v___x_64_;
}
else
{
lean_object* v___x_65_; 
lean_dec(v_h__2_50_);
v___x_65_ = lean_apply_3(v_h__4_52_, v_lhsVal_47_, lean_box(0), lean_box(0));
return v___x_65_;
}
}
else
{
lean_object* v___x_66_; 
lean_dec(v_h__4_52_);
lean_dec(v_h__2_50_);
v___x_66_ = lean_apply_6(v_h__5_53_, v_lhsVal_47_, v_rhsVal_48_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(lean_object* v_motive_67_, lean_object* v_lhsVal_68_, lean_object* v_rhsVal_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_, lean_object* v_h__3_72_, lean_object* v_h__4_73_, lean_object* v_h__5_74_){
_start:
{
if (lean_obj_tag(v_lhsVal_68_) == 1)
{
lean_object* v_val_75_; uint8_t v___x_76_; 
lean_dec(v_h__5_74_);
lean_dec(v_h__4_73_);
v_val_75_ = lean_ctor_get(v_lhsVal_68_, 0);
v___x_76_ = lean_unbox(v_val_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref_known(v_lhsVal_68_, 1);
lean_dec(v_h__3_72_);
lean_dec(v_h__2_71_);
v___x_77_ = lean_apply_1(v_h__1_70_, v_rhsVal_69_);
return v___x_77_;
}
else
{
lean_dec(v_h__1_70_);
if (lean_obj_tag(v_rhsVal_69_) == 1)
{
lean_object* v_val_78_; uint8_t v___x_79_; 
v_val_78_ = lean_ctor_get(v_rhsVal_69_, 0);
v___x_79_ = lean_unbox(v_val_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_dec_ref_known(v_rhsVal_69_, 1);
lean_dec(v_h__3_72_);
v___x_80_ = lean_apply_2(v_h__2_71_, v_lhsVal_68_, lean_box(0));
return v___x_80_;
}
else
{
lean_object* v___x_81_; 
lean_dec_ref_known(v_lhsVal_68_, 1);
lean_dec(v_h__2_71_);
v___x_81_ = lean_apply_2(v_h__3_72_, v_rhsVal_69_, lean_box(0));
return v___x_81_;
}
}
else
{
lean_object* v___x_82_; 
lean_dec_ref_known(v_lhsVal_68_, 1);
lean_dec(v_h__2_71_);
v___x_82_ = lean_apply_2(v_h__3_72_, v_rhsVal_69_, lean_box(0));
return v___x_82_;
}
}
}
else
{
lean_dec(v_h__3_72_);
lean_dec(v_h__1_70_);
if (lean_obj_tag(v_rhsVal_69_) == 1)
{
lean_object* v_val_83_; uint8_t v___x_84_; 
lean_dec(v_h__5_74_);
v_val_83_ = lean_ctor_get(v_rhsVal_69_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v_rhsVal_69_, 1);
v___x_84_ = lean_unbox(v_val_83_);
lean_dec(v_val_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_dec(v_h__4_73_);
v___x_85_ = lean_apply_2(v_h__2_71_, v_lhsVal_68_, lean_box(0));
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
lean_dec(v_h__2_71_);
v___x_86_ = lean_apply_3(v_h__4_73_, v_lhsVal_68_, lean_box(0), lean_box(0));
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v_h__4_73_);
lean_dec(v_h__2_71_);
v___x_87_ = lean_apply_6(v_h__5_74_, v_lhsVal_68_, v_rhsVal_69_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_87_;
}
}
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Cached(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_AIG_Cached(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Cached(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_CachedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_CachedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_CachedLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
