// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Cell
// Imports: public import Std.Data.Internal.List.Associative import Init.Data.List.Find
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
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Cell_contains___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Cell_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___redArg(lean_object* v_k_x27_1_, lean_object* v_v_x27_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_k_x27_1_);
lean_ctor_set(v___x_3_, 1, v_v_x27_2_);
v___x_4_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq(lean_object* v_00_u03b1_5_, lean_object* v_00_u03b2_6_, lean_object* v_inst_7_, lean_object* v_k_8_, lean_object* v_k_x27_9_, lean_object* v_v_x27_10_, lean_object* v_hcmp_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_x27_9_, v_v_x27_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___boxed(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_inst_15_, lean_object* v_k_16_, lean_object* v_k_x27_17_, lean_object* v_v_x27_18_, lean_object* v_hcmp_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_DTreeMap_Internal_Cell_ofEq(v_00_u03b1_13_, v_00_u03b2_14_, v_inst_15_, v_k_16_, v_k_x27_17_, v_v_x27_18_, v_hcmp_19_);
lean_dec_ref(v_k_16_);
lean_dec_ref(v_inst_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of___redArg(lean_object* v_k_21_, lean_object* v_v_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_21_, v_v_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_k_27_, lean_object* v_v_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_27_, v_v_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_inst_32_, lean_object* v_k_33_, lean_object* v_v_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_DTreeMap_Internal_Cell_of(v_00_u03b1_30_, v_00_u03b2_31_, v_inst_32_, v_k_33_, v_v_34_);
lean_dec_ref(v_inst_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_inst_38_, lean_object* v_k_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___boxed(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_inst_43_, lean_object* v_k_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_DTreeMap_Internal_Cell_empty(v_00_u03b1_41_, v_00_u03b2_42_, v_inst_43_, v_k_44_);
lean_dec_ref(v_k_44_);
lean_dec_ref(v_inst_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___redArg(lean_object* v_k_46_, lean_object* v_v_x3f_47_){
_start:
{
if (lean_obj_tag(v_v_x3f_47_) == 0)
{
lean_object* v___x_48_; 
lean_dec(v_k_46_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
else
{
lean_object* v_val_49_; lean_object* v___x_50_; 
v_val_49_ = lean_ctor_get(v_v_x3f_47_, 0);
lean_inc(v_val_49_);
lean_dec_ref(v_v_x3f_47_);
v___x_50_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_46_, v_val_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_inst_53_, lean_object* v_k_54_, lean_object* v_v_x3f_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_54_, v_v_x3f_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___boxed(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_inst_59_, lean_object* v_k_60_, lean_object* v_v_x3f_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_DTreeMap_Internal_Cell_ofOption(v_00_u03b1_57_, v_00_u03b2_58_, v_inst_59_, v_k_60_, v_v_x3f_61_);
lean_dec_ref(v_inst_59_);
return v_res_62_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Cell_contains___redArg(lean_object* v_c_63_){
_start:
{
if (lean_obj_tag(v_c_63_) == 0)
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 1;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___redArg___boxed(lean_object* v_c_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_66_);
lean_dec(v_c_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Cell_contains(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_inst_71_, lean_object* v_k_72_, lean_object* v_c_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___boxed(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_inst_77_, lean_object* v_k_78_, lean_object* v_c_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Std_DTreeMap_Internal_Cell_contains(v_00_u03b1_75_, v_00_u03b2_76_, v_inst_77_, v_k_78_, v_c_79_);
lean_dec(v_c_79_);
lean_dec_ref(v_k_78_);
lean_dec_ref(v_inst_77_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(lean_object* v_c_82_){
_start:
{
if (lean_obj_tag(v_c_82_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(0);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_val_84_ = lean_ctor_get(v_c_82_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_c_82_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v_c_82_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_dec(v_c_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_snd_88_; lean_object* v___x_90_; 
v_snd_88_ = lean_ctor_get(v_val_84_, 1);
lean_inc(v_snd_88_);
lean_dec(v_val_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v_snd_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_snd_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_k_98_, lean_object* v_c_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___boxed(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_k_106_, lean_object* v_c_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DTreeMap_Internal_Cell_get_x3f(v_00_u03b1_101_, v_00_u03b2_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_k_106_, v_c_107_);
lean_dec(v_k_106_);
lean_dec_ref(v_inst_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(lean_object* v_c_109_){
_start:
{
if (lean_obj_tag(v_c_109_) == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_127_; 
v_val_111_ = lean_ctor_get(v_c_109_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_c_109_);
if (v_isSharedCheck_127_ == 0)
{
v___x_113_ = v_c_109_;
v_isShared_114_ = v_isSharedCheck_127_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_dec(v_c_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_127_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_126_; 
v_fst_115_ = lean_ctor_get(v_val_111_, 0);
v_snd_116_ = lean_ctor_get(v_val_111_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_val_111_);
if (v_isSharedCheck_126_ == 0)
{
v___x_118_ = v_val_111_;
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_val_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_snd_116_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_123_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_121_);
v___x_123_ = v___x_113_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v_inst_130_, lean_object* v_k_131_, lean_object* v_c_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___boxed(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_inst_136_, lean_object* v_k_137_, lean_object* v_c_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f(v_00_u03b1_134_, v_00_u03b2_135_, v_inst_136_, v_k_137_, v_c_138_);
lean_dec(v_k_137_);
lean_dec_ref(v_inst_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(lean_object* v_c_140_){
_start:
{
if (lean_obj_tag(v_c_140_) == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_box(0);
return v___x_141_;
}
else
{
lean_object* v_val_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_150_; 
v_val_142_ = lean_ctor_get(v_c_140_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_c_140_);
if (v_isSharedCheck_150_ == 0)
{
v___x_144_ = v_c_140_;
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_val_142_);
lean_dec(v_c_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_fst_146_; lean_object* v___x_148_; 
v_fst_146_ = lean_ctor_get(v_val_142_, 0);
lean_inc(v_fst_146_);
lean_dec(v_val_142_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v_fst_146_);
v___x_148_ = v___x_144_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_fst_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_inst_153_, lean_object* v_k_154_, lean_object* v_c_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___boxed(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_inst_159_, lean_object* v_k_160_, lean_object* v_c_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f(v_00_u03b1_157_, v_00_u03b2_158_, v_inst_159_, v_k_160_, v_c_161_);
lean_dec(v_k_160_);
lean_dec_ref(v_inst_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___redArg(lean_object* v_k_163_, lean_object* v_f_164_, lean_object* v_c_165_){
_start:
{
if (lean_obj_tag(v_c_165_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_f_164_, v___x_166_);
v___x_168_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_163_, v___x_167_);
return v___x_168_;
}
else
{
lean_object* v_val_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_val_169_ = lean_ctor_get(v_c_165_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_c_165_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_c_165_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_val_169_);
lean_dec(v_c_165_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_snd_173_; lean_object* v___x_175_; 
v_snd_173_ = lean_ctor_get(v_val_169_, 1);
lean_inc(v_snd_173_);
lean_dec(v_val_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v_snd_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_snd_173_);
v___x_175_ = v_reuseFailAlloc_178_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_apply_1(v_f_164_, v___x_175_);
v___x_177_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_163_, v___x_176_);
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter(lean_object* v_00_u03b1_180_, lean_object* v_00_u03b2_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_k_185_, lean_object* v_f_186_, lean_object* v_c_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DTreeMap_Internal_Cell_alter___redArg(v_k_185_, v_f_186_, v_c_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___boxed(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_k_194_, lean_object* v_f_195_, lean_object* v_c_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_DTreeMap_Internal_Cell_alter(v_00_u03b1_189_, v_00_u03b2_190_, v_inst_191_, v_inst_192_, v_inst_193_, v_k_194_, v_f_195_, v_c_196_);
lean_dec_ref(v_inst_191_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(lean_object* v_c_198_){
_start:
{
if (lean_obj_tag(v_c_198_) == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_val_200_ = lean_ctor_get(v_c_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_c_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v_c_198_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_dec(v_c_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v_snd_204_; lean_object* v___x_206_; 
v_snd_204_ = lean_ctor_get(v_val_200_, 1);
lean_inc(v_snd_204_);
lean_dec(v_val_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v_snd_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_snd_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_inst_211_, lean_object* v_k_212_, lean_object* v_c_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___boxed(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_inst_217_, lean_object* v_k_218_, lean_object* v_c_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f(v_00_u03b1_215_, v_00_u03b2_216_, v_inst_217_, v_k_218_, v_c_219_);
lean_dec(v_k_218_);
lean_dec_ref(v_inst_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(lean_object* v_k_221_, lean_object* v_f_222_, lean_object* v_c_223_){
_start:
{
if (lean_obj_tag(v_c_223_) == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_box(0);
v___x_225_ = lean_apply_1(v_f_222_, v___x_224_);
v___x_226_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_221_, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_237_; 
v_val_227_ = lean_ctor_get(v_c_223_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_c_223_);
if (v_isSharedCheck_237_ == 0)
{
v___x_229_ = v_c_223_;
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_val_227_);
lean_dec(v_c_223_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_snd_231_; lean_object* v___x_233_; 
v_snd_231_ = lean_ctor_get(v_val_227_, 1);
lean_inc(v_snd_231_);
lean_dec(v_val_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v_snd_231_);
v___x_233_ = v___x_229_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_snd_231_);
v___x_233_ = v_reuseFailAlloc_236_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_apply_1(v_f_222_, v___x_233_);
v___x_235_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_221_, v___x_234_);
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter(lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_k_242_, lean_object* v_f_243_, lean_object* v_c_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(v_k_242_, v_f_243_, v_c_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___boxed(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_k_250_, lean_object* v_f_251_, lean_object* v_c_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_DTreeMap_Internal_Cell_Const_alter(v_00_u03b1_246_, v_00_u03b2_247_, v_inst_248_, v_inst_249_, v_k_250_, v_f_251_, v_c_252_);
lean_dec_ref(v_inst_248_);
return v_res_253_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(lean_object* v_k_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_fst_256_; lean_object* v___x_257_; uint8_t v___x_258_; uint8_t v___x_259_; uint8_t v___x_260_; 
v_fst_256_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_fst_256_);
lean_dec_ref(v_x_255_);
v___x_257_ = lean_apply_1(v_k_254_, v_fst_256_);
v___x_258_ = 1;
v___x_259_ = lean_unbox(v___x_257_);
v___x_260_ = l_instDecidableEqOrdering(v___x_259_, v___x_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed(lean_object* v_k_261_, lean_object* v_x_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(v_k_261_, v_x_262_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg(lean_object* v_l_265_, lean_object* v_k_266_){
_start:
{
lean_object* v___f_267_; lean_object* v___x_268_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_267_, 0, v_k_266_);
v___x_268_ = l_List_find_x3f___redArg(v___f_267_, v_l_265_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_l_272_, lean_object* v_k_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DTreeMap_Internal_List_findCell___redArg(v_l_272_, v_k_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___boxed(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_inst_277_, lean_object* v_l_278_, lean_object* v_k_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_DTreeMap_Internal_List_findCell(v_00_u03b1_275_, v_00_u03b2_276_, v_inst_277_, v_l_278_, v_k_279_);
lean_dec_ref(v_inst_277_);
return v_res_280_;
}
}
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
}
#ifdef __cplusplus
}
#endif
