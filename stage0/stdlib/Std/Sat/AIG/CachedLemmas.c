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
switch(lean_obj_tag(v_x_13_))
{
case 0:
{
lean_object* v___x_17_; 
lean_dec(v_h__3_16_);
lean_dec(v_h__2_15_);
v___x_17_ = lean_apply_1(v_h__1_14_, lean_box(0));
return v___x_17_;
}
case 1:
{
lean_object* v_idx_18_; lean_object* v___x_19_; 
lean_dec(v_h__3_16_);
lean_dec(v_h__1_14_);
v_idx_18_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_idx_18_);
lean_dec_ref(v_x_13_);
v___x_19_ = lean_apply_2(v_h__2_15_, v_idx_18_, lean_box(0));
return v___x_19_;
}
default: 
{
lean_object* v_l_20_; lean_object* v_r_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_15_);
lean_dec(v_h__1_14_);
v_l_20_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_l_20_);
v_r_21_ = lean_ctor_get(v_x_13_, 1);
lean_inc(v_r_21_);
lean_dec_ref(v_x_13_);
v___x_22_ = lean_apply_3(v_h__3_16_, v_l_20_, v_r_21_, lean_box(0));
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___redArg(lean_object* v_aig_23_, lean_object* v_h__1_24_){
_start:
{
lean_object* v_decls_25_; lean_object* v_cache_26_; lean_object* v___x_27_; 
v_decls_25_ = lean_ctor_get(v_aig_23_, 0);
lean_inc_ref(v_decls_25_);
v_cache_26_ = lean_ctor_get(v_aig_23_, 1);
lean_inc_ref(v_cache_26_);
lean_dec_ref(v_aig_23_);
v___x_27_ = lean_apply_5(v_h__1_24_, v_decls_25_, v_cache_26_, lean_box(0), lean_box(0), lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_motive_31_, lean_object* v_aig_32_, lean_object* v_h__1_33_){
_start:
{
lean_object* v_decls_34_; lean_object* v_cache_35_; lean_object* v___x_36_; 
v_decls_34_ = lean_ctor_get(v_aig_32_, 0);
lean_inc_ref(v_decls_34_);
v_cache_35_ = lean_ctor_get(v_aig_32_, 1);
lean_inc_ref(v_cache_35_);
lean_dec_ref(v_aig_32_);
v___x_36_ = lean_apply_5(v_h__1_33_, v_decls_34_, v_cache_35_, lean_box(0), lean_box(0), lean_box(0));
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_motive_40_, lean_object* v_aig_41_, lean_object* v_h__1_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(v_00_u03b1_37_, v_inst_38_, v_inst_39_, v_motive_40_, v_aig_41_, v_h__1_42_);
lean_dec_ref(v_inst_39_);
lean_dec_ref(v_inst_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_45_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__2_46_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_val_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_46_);
v_val_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_val_49_);
lean_dec_ref(v_x_44_);
v___x_50_ = lean_apply_1(v_h__1_45_, v_val_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(lean_object* v_00_u03b1_51_, lean_object* v_decls_52_, lean_object* v_decl_53_, lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_56_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_1(v_h__2_57_, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v_val_60_; lean_object* v___x_61_; 
lean_dec(v_h__2_57_);
v_val_60_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_60_);
lean_dec_ref(v_x_55_);
v___x_61_ = lean_apply_1(v_h__1_56_, v_val_60_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(lean_object* v_00_u03b1_62_, lean_object* v_decls_63_, lean_object* v_decl_64_, lean_object* v_motive_65_, lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(v_00_u03b1_62_, v_decls_63_, v_decl_64_, v_motive_65_, v_x_66_, v_h__1_67_, v_h__2_68_);
lean_dec(v_decl_64_);
lean_dec_ref(v_decls_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___redArg(lean_object* v_lhsVal_70_, lean_object* v_rhsVal_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_, lean_object* v_h__3_74_, lean_object* v_h__4_75_, lean_object* v_h__5_76_){
_start:
{
if (lean_obj_tag(v_lhsVal_70_) == 1)
{
lean_object* v_val_77_; uint8_t v___x_78_; 
lean_dec(v_h__5_76_);
lean_dec(v_h__4_75_);
v_val_77_ = lean_ctor_get(v_lhsVal_70_, 0);
v___x_78_ = lean_unbox(v_val_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v_lhsVal_70_);
lean_dec(v_h__3_74_);
lean_dec(v_h__2_73_);
v___x_79_ = lean_apply_1(v_h__1_72_, v_rhsVal_71_);
return v___x_79_;
}
else
{
lean_dec(v_h__1_72_);
if (lean_obj_tag(v_rhsVal_71_) == 1)
{
lean_object* v_val_80_; uint8_t v___x_81_; 
v_val_80_ = lean_ctor_get(v_rhsVal_71_, 0);
v___x_81_ = lean_unbox(v_val_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_dec_ref(v_rhsVal_71_);
lean_dec(v_h__3_74_);
v___x_82_ = lean_apply_2(v_h__2_73_, v_lhsVal_70_, lean_box(0));
return v___x_82_;
}
else
{
lean_object* v___x_83_; 
lean_dec_ref(v_lhsVal_70_);
lean_dec(v_h__2_73_);
v___x_83_ = lean_apply_2(v_h__3_74_, v_rhsVal_71_, lean_box(0));
return v___x_83_;
}
}
else
{
lean_object* v___x_84_; 
lean_dec_ref(v_lhsVal_70_);
lean_dec(v_h__2_73_);
v___x_84_ = lean_apply_2(v_h__3_74_, v_rhsVal_71_, lean_box(0));
return v___x_84_;
}
}
}
else
{
lean_dec(v_h__3_74_);
lean_dec(v_h__1_72_);
if (lean_obj_tag(v_rhsVal_71_) == 1)
{
lean_object* v_val_85_; uint8_t v___x_86_; 
lean_dec(v_h__5_76_);
v_val_85_ = lean_ctor_get(v_rhsVal_71_, 0);
lean_inc(v_val_85_);
lean_dec_ref(v_rhsVal_71_);
v___x_86_ = lean_unbox(v_val_85_);
lean_dec(v_val_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
lean_dec(v_h__4_75_);
v___x_87_ = lean_apply_2(v_h__2_73_, v_lhsVal_70_, lean_box(0));
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec(v_h__2_73_);
v___x_88_ = lean_apply_3(v_h__4_75_, v_lhsVal_70_, lean_box(0), lean_box(0));
return v___x_88_;
}
}
else
{
lean_object* v___x_89_; 
lean_dec(v_h__4_75_);
lean_dec(v_h__2_73_);
v___x_89_ = lean_apply_6(v_h__5_76_, v_lhsVal_70_, v_rhsVal_71_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(lean_object* v_motive_90_, lean_object* v_lhsVal_91_, lean_object* v_rhsVal_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_, lean_object* v_h__4_96_, lean_object* v_h__5_97_){
_start:
{
if (lean_obj_tag(v_lhsVal_91_) == 1)
{
lean_object* v_val_98_; uint8_t v___x_99_; 
lean_dec(v_h__5_97_);
lean_dec(v_h__4_96_);
v_val_98_ = lean_ctor_get(v_lhsVal_91_, 0);
v___x_99_ = lean_unbox(v_val_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v_lhsVal_91_);
lean_dec(v_h__3_95_);
lean_dec(v_h__2_94_);
v___x_100_ = lean_apply_1(v_h__1_93_, v_rhsVal_92_);
return v___x_100_;
}
else
{
lean_dec(v_h__1_93_);
if (lean_obj_tag(v_rhsVal_92_) == 1)
{
lean_object* v_val_101_; uint8_t v___x_102_; 
v_val_101_ = lean_ctor_get(v_rhsVal_92_, 0);
v___x_102_ = lean_unbox(v_val_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v_rhsVal_92_);
lean_dec(v_h__3_95_);
v___x_103_ = lean_apply_2(v_h__2_94_, v_lhsVal_91_, lean_box(0));
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_dec_ref(v_lhsVal_91_);
lean_dec(v_h__2_94_);
v___x_104_ = lean_apply_2(v_h__3_95_, v_rhsVal_92_, lean_box(0));
return v___x_104_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec_ref(v_lhsVal_91_);
lean_dec(v_h__2_94_);
v___x_105_ = lean_apply_2(v_h__3_95_, v_rhsVal_92_, lean_box(0));
return v___x_105_;
}
}
}
else
{
lean_dec(v_h__3_95_);
lean_dec(v_h__1_93_);
if (lean_obj_tag(v_rhsVal_92_) == 1)
{
lean_object* v_val_106_; uint8_t v___x_107_; 
lean_dec(v_h__5_97_);
v_val_106_ = lean_ctor_get(v_rhsVal_92_, 0);
lean_inc(v_val_106_);
lean_dec_ref(v_rhsVal_92_);
v___x_107_ = lean_unbox(v_val_106_);
lean_dec(v_val_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec(v_h__4_96_);
v___x_108_ = lean_apply_2(v_h__2_94_, v_lhsVal_91_, lean_box(0));
return v___x_108_;
}
else
{
lean_object* v___x_109_; 
lean_dec(v_h__2_94_);
v___x_109_ = lean_apply_3(v_h__4_96_, v_lhsVal_91_, lean_box(0), lean_box(0));
return v___x_109_;
}
}
else
{
lean_object* v___x_110_; 
lean_dec(v_h__4_96_);
lean_dec(v_h__2_94_);
v___x_110_ = lean_apply_6(v_h__5_97_, v_lhsVal_91_, v_rhsVal_92_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___redArg(lean_object* v_aig_111_, lean_object* v_input_112_, lean_object* v_h__1_113_){
_start:
{
lean_object* v_decls_114_; lean_object* v_cache_115_; lean_object* v___x_116_; 
v_decls_114_ = lean_ctor_get(v_aig_111_, 0);
lean_inc_ref(v_decls_114_);
v_cache_115_ = lean_ctor_get(v_aig_111_, 1);
lean_inc_ref(v_cache_115_);
lean_dec_ref(v_aig_111_);
v___x_116_ = lean_apply_6(v_h__1_113_, v_decls_114_, v_cache_115_, lean_box(0), lean_box(0), lean_box(0), v_input_112_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(lean_object* v_00_u03b1_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_motive_120_, lean_object* v_aig_121_, lean_object* v_input_122_, lean_object* v_h__1_123_){
_start:
{
lean_object* v_decls_124_; lean_object* v_cache_125_; lean_object* v___x_126_; 
v_decls_124_ = lean_ctor_get(v_aig_121_, 0);
lean_inc_ref(v_decls_124_);
v_cache_125_ = lean_ctor_get(v_aig_121_, 1);
lean_inc_ref(v_cache_125_);
lean_dec_ref(v_aig_121_);
v___x_126_ = lean_apply_6(v_h__1_123_, v_decls_124_, v_cache_125_, lean_box(0), lean_box(0), lean_box(0), v_input_122_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___boxed(lean_object* v_00_u03b1_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_motive_130_, lean_object* v_aig_131_, lean_object* v_input_132_, lean_object* v_h__1_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(v_00_u03b1_127_, v_inst_128_, v_inst_129_, v_motive_130_, v_aig_131_, v_input_132_, v_h__1_133_);
lean_dec_ref(v_inst_129_);
lean_dec_ref(v_inst_128_);
return v_res_134_;
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
