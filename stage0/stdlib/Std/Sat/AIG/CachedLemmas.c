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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_5_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v___x_5_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_5_;
}
case 1:
{
lean_object* v_idx_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_idx_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_idx_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_2(v_h__2_3_, v_idx_6_, lean_box(0));
return v___x_7_;
}
default: 
{
lean_object* v_l_8_; lean_object* v_r_9_; lean_object* v___x_10_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v_l_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_l_8_);
v_r_9_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_r_9_);
lean_dec_ref(v_x_1_);
v___x_10_ = lean_apply_3(v_h__3_4_, v_l_8_, v_r_9_, lean_box(0));
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_11_, lean_object* v_motive_12_, lean_object* v_x_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_, lean_object* v_h__3_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(v_x_13_, v_h__1_14_, v_h__2_15_, v_h__3_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___redArg(lean_object* v_aig_18_, lean_object* v_h__1_19_){
_start:
{
lean_object* v_decls_20_; lean_object* v_cache_21_; lean_object* v___x_22_; 
v_decls_20_ = lean_ctor_get(v_aig_18_, 0);
lean_inc_ref(v_decls_20_);
v_cache_21_ = lean_ctor_get(v_aig_18_, 1);
lean_inc_ref(v_cache_21_);
lean_dec_ref(v_aig_18_);
v___x_22_ = lean_apply_5(v_h__1_19_, v_decls_20_, v_cache_21_, lean_box(0), lean_box(0), lean_box(0));
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_motive_26_, lean_object* v_aig_27_, lean_object* v_h__1_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___redArg(v_aig_27_, v_h__1_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___boxed(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_motive_33_, lean_object* v_aig_34_, lean_object* v_h__1_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(v_00_u03b1_30_, v_inst_31_, v_inst_32_, v_motive_33_, v_aig_34_, v_h__1_35_);
lean_dec_ref(v_inst_32_);
lean_dec_ref(v_inst_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__1_38_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__2_39_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_39_);
v_val_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_42_);
lean_dec_ref(v_x_37_);
v___x_43_ = lean_apply_1(v_h__1_38_, v_val_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_decls_45_, lean_object* v_decl_46_, lean_object* v_motive_47_, lean_object* v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(v_x_48_, v_h__1_49_, v_h__2_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(lean_object* v_00_u03b1_52_, lean_object* v_decls_53_, lean_object* v_decl_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(v_00_u03b1_52_, v_decls_53_, v_decl_54_, v_motive_55_, v_x_56_, v_h__1_57_, v_h__2_58_);
lean_dec(v_decl_54_);
lean_dec_ref(v_decls_53_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___redArg(lean_object* v_lhsVal_60_, lean_object* v_rhsVal_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_, lean_object* v_h__4_65_, lean_object* v_h__5_66_){
_start:
{
if (lean_obj_tag(v_lhsVal_60_) == 1)
{
lean_object* v_val_67_; uint8_t v___x_68_; 
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
v_val_67_ = lean_ctor_get(v_lhsVal_60_, 0);
v___x_68_ = lean_unbox(v_val_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_dec_ref(v_lhsVal_60_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
v___x_69_ = lean_apply_1(v_h__1_62_, v_rhsVal_61_);
return v___x_69_;
}
else
{
lean_dec(v_h__1_62_);
if (lean_obj_tag(v_rhsVal_61_) == 1)
{
lean_object* v_val_70_; uint8_t v___x_71_; 
v_val_70_ = lean_ctor_get(v_rhsVal_61_, 0);
v___x_71_ = lean_unbox(v_val_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_rhsVal_61_);
lean_dec(v_h__3_64_);
v___x_72_ = lean_apply_2(v_h__2_63_, v_lhsVal_60_, lean_box(0));
return v___x_72_;
}
else
{
lean_object* v___x_73_; 
lean_dec_ref(v_lhsVal_60_);
lean_dec(v_h__2_63_);
v___x_73_ = lean_apply_2(v_h__3_64_, v_rhsVal_61_, lean_box(0));
return v___x_73_;
}
}
else
{
lean_object* v___x_74_; 
lean_dec_ref(v_lhsVal_60_);
lean_dec(v_h__2_63_);
v___x_74_ = lean_apply_2(v_h__3_64_, v_rhsVal_61_, lean_box(0));
return v___x_74_;
}
}
}
else
{
lean_dec(v_h__3_64_);
lean_dec(v_h__1_62_);
if (lean_obj_tag(v_rhsVal_61_) == 1)
{
lean_object* v_val_75_; uint8_t v___x_76_; 
lean_dec(v_h__5_66_);
v_val_75_ = lean_ctor_get(v_rhsVal_61_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v_rhsVal_61_);
v___x_76_ = lean_unbox(v_val_75_);
lean_dec(v_val_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec(v_h__4_65_);
v___x_77_ = lean_apply_2(v_h__2_63_, v_lhsVal_60_, lean_box(0));
return v___x_77_;
}
else
{
lean_object* v___x_78_; 
lean_dec(v_h__2_63_);
v___x_78_ = lean_apply_3(v_h__4_65_, v_lhsVal_60_, lean_box(0), lean_box(0));
return v___x_78_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec(v_h__4_65_);
lean_dec(v_h__2_63_);
v___x_79_ = lean_apply_6(v_h__5_66_, v_lhsVal_60_, v_rhsVal_61_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(lean_object* v_motive_80_, lean_object* v_lhsVal_81_, lean_object* v_rhsVal_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_, lean_object* v_h__3_85_, lean_object* v_h__4_86_, lean_object* v_h__5_87_){
_start:
{
if (lean_obj_tag(v_lhsVal_81_) == 1)
{
lean_object* v_val_88_; uint8_t v___x_89_; 
lean_dec(v_h__5_87_);
lean_dec(v_h__4_86_);
v_val_88_ = lean_ctor_get(v_lhsVal_81_, 0);
v___x_89_ = lean_unbox(v_val_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec_ref(v_lhsVal_81_);
lean_dec(v_h__3_85_);
lean_dec(v_h__2_84_);
v___x_90_ = lean_apply_1(v_h__1_83_, v_rhsVal_82_);
return v___x_90_;
}
else
{
lean_dec(v_h__1_83_);
if (lean_obj_tag(v_rhsVal_82_) == 1)
{
lean_object* v_val_91_; uint8_t v___x_92_; 
v_val_91_ = lean_ctor_get(v_rhsVal_82_, 0);
v___x_92_ = lean_unbox(v_val_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v_rhsVal_82_);
lean_dec(v_h__3_85_);
v___x_93_ = lean_apply_2(v_h__2_84_, v_lhsVal_81_, lean_box(0));
return v___x_93_;
}
else
{
lean_object* v___x_94_; 
lean_dec_ref(v_lhsVal_81_);
lean_dec(v_h__2_84_);
v___x_94_ = lean_apply_2(v_h__3_85_, v_rhsVal_82_, lean_box(0));
return v___x_94_;
}
}
else
{
lean_object* v___x_95_; 
lean_dec_ref(v_lhsVal_81_);
lean_dec(v_h__2_84_);
v___x_95_ = lean_apply_2(v_h__3_85_, v_rhsVal_82_, lean_box(0));
return v___x_95_;
}
}
}
else
{
lean_dec(v_h__3_85_);
lean_dec(v_h__1_83_);
if (lean_obj_tag(v_rhsVal_82_) == 1)
{
lean_object* v_val_96_; uint8_t v___x_97_; 
lean_dec(v_h__5_87_);
v_val_96_ = lean_ctor_get(v_rhsVal_82_, 0);
lean_inc(v_val_96_);
lean_dec_ref(v_rhsVal_82_);
v___x_97_ = lean_unbox(v_val_96_);
lean_dec(v_val_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec(v_h__4_86_);
v___x_98_ = lean_apply_2(v_h__2_84_, v_lhsVal_81_, lean_box(0));
return v___x_98_;
}
else
{
lean_object* v___x_99_; 
lean_dec(v_h__2_84_);
v___x_99_ = lean_apply_3(v_h__4_86_, v_lhsVal_81_, lean_box(0), lean_box(0));
return v___x_99_;
}
}
else
{
lean_object* v___x_100_; 
lean_dec(v_h__4_86_);
lean_dec(v_h__2_84_);
v___x_100_ = lean_apply_6(v_h__5_87_, v_lhsVal_81_, v_rhsVal_82_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___redArg(lean_object* v_aig_101_, lean_object* v_input_102_, lean_object* v_h__1_103_){
_start:
{
lean_object* v_decls_104_; lean_object* v_cache_105_; lean_object* v___x_106_; 
v_decls_104_ = lean_ctor_get(v_aig_101_, 0);
lean_inc_ref(v_decls_104_);
v_cache_105_ = lean_ctor_get(v_aig_101_, 1);
lean_inc_ref(v_cache_105_);
lean_dec_ref(v_aig_101_);
v___x_106_ = lean_apply_6(v_h__1_103_, v_decls_104_, v_cache_105_, lean_box(0), lean_box(0), lean_box(0), v_input_102_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_motive_110_, lean_object* v_aig_111_, lean_object* v_input_112_, lean_object* v_h__1_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___redArg(v_aig_111_, v_input_112_, v_h__1_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___boxed(lean_object* v_00_u03b1_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_motive_118_, lean_object* v_aig_119_, lean_object* v_input_120_, lean_object* v_h__1_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(v_00_u03b1_115_, v_inst_116_, v_inst_117_, v_motive_118_, v_aig_119_, v_input_120_, v_h__1_121_);
lean_dec_ref(v_inst_117_);
lean_dec_ref(v_inst_116_);
return v_res_122_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Cached(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
