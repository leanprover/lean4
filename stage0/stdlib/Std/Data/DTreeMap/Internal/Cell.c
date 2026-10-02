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
lean_object* l_Ordering_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___redArg___boxed(lean_object*);
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
static lean_once_cell_t l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___closed__0;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___redArg(){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___redArg___boxed(lean_object* v___dummy_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_DTreeMap_Internal_Cell_empty___redArg();
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_inst_42_, lean_object* v_k_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___boxed(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_inst_47_, lean_object* v_k_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_DTreeMap_Internal_Cell_empty(v_00_u03b1_45_, v_00_u03b2_46_, v_inst_47_, v_k_48_);
lean_dec_ref(v_k_48_);
lean_dec_ref(v_inst_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___redArg(lean_object* v_k_50_, lean_object* v_v_x3f_51_){
_start:
{
if (lean_obj_tag(v_v_x3f_51_) == 0)
{
lean_object* v___x_52_; 
lean_dec(v_k_50_);
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_54_; 
v_val_53_ = lean_ctor_get(v_v_x3f_51_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v_v_x3f_51_, 1);
v___x_54_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_50_, v_val_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_inst_57_, lean_object* v_k_58_, lean_object* v_v_x3f_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_58_, v_v_x3f_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___boxed(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_inst_63_, lean_object* v_k_64_, lean_object* v_v_x3f_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_DTreeMap_Internal_Cell_ofOption(v_00_u03b1_61_, v_00_u03b2_62_, v_inst_63_, v_k_64_, v_v_x3f_65_);
lean_dec_ref(v_inst_63_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Cell_contains___redArg(lean_object* v_c_67_){
_start:
{
if (lean_obj_tag(v_c_67_) == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___redArg___boxed(lean_object* v_c_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_70_);
lean_dec(v_c_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Cell_contains(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_inst_75_, lean_object* v_k_76_, lean_object* v_c_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___boxed(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_inst_81_, lean_object* v_k_82_, lean_object* v_c_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Std_DTreeMap_Internal_Cell_contains(v_00_u03b1_79_, v_00_u03b2_80_, v_inst_81_, v_k_82_, v_c_83_);
lean_dec(v_c_83_);
lean_dec_ref(v_k_82_);
lean_dec_ref(v_inst_81_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(lean_object* v_c_86_){
_start:
{
if (lean_obj_tag(v_c_86_) == 0)
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_val_88_ = lean_ctor_get(v_c_86_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_c_86_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v_c_86_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_dec(v_c_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_snd_92_; lean_object* v___x_94_; 
v_snd_92_ = lean_ctor_get(v_val_88_, 1);
lean_inc(v_snd_92_);
lean_dec(v_val_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v_snd_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_snd_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_k_102_, lean_object* v_c_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_k_110_, lean_object* v_c_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_DTreeMap_Internal_Cell_get_x3f(v_00_u03b1_105_, v_00_u03b2_106_, v_inst_107_, v_inst_108_, v_inst_109_, v_k_110_, v_c_111_);
lean_dec(v_k_110_);
lean_dec_ref(v_inst_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(lean_object* v_c_113_){
_start:
{
if (lean_obj_tag(v_c_113_) == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_131_; 
v_val_115_ = lean_ctor_get(v_c_113_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_c_113_);
if (v_isSharedCheck_131_ == 0)
{
v___x_117_ = v_c_113_;
v_isShared_118_ = v_isSharedCheck_131_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_dec(v_c_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_131_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_fst_119_ = lean_ctor_get(v_val_115_, 0);
v_snd_120_ = lean_ctor_get(v_val_115_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_val_115_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v_val_115_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_val_115_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_fst_119_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_snd_120_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_125_);
v___x_127_ = v___x_117_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_inst_134_, lean_object* v_k_135_, lean_object* v_c_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___boxed(lean_object* v_00_u03b1_138_, lean_object* v_00_u03b2_139_, lean_object* v_inst_140_, lean_object* v_k_141_, lean_object* v_c_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f(v_00_u03b1_138_, v_00_u03b2_139_, v_inst_140_, v_k_141_, v_c_142_);
lean_dec(v_k_141_);
lean_dec_ref(v_inst_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(lean_object* v_c_144_){
_start:
{
if (lean_obj_tag(v_c_144_) == 0)
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
return v___x_145_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_val_146_ = lean_ctor_get(v_c_144_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_c_144_);
if (v_isSharedCheck_154_ == 0)
{
v___x_148_ = v_c_144_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_val_146_);
lean_dec(v_c_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_fst_150_; lean_object* v___x_152_; 
v_fst_150_ = lean_ctor_get(v_val_146_, 0);
lean_inc(v_fst_150_);
lean_dec(v_val_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v_fst_150_);
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_fst_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_inst_157_, lean_object* v_k_158_, lean_object* v_c_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___boxed(lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v_inst_163_, lean_object* v_k_164_, lean_object* v_c_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f(v_00_u03b1_161_, v_00_u03b2_162_, v_inst_163_, v_k_164_, v_c_165_);
lean_dec(v_k_164_);
lean_dec_ref(v_inst_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___redArg(lean_object* v_k_167_, lean_object* v_f_168_, lean_object* v_c_169_){
_start:
{
if (lean_obj_tag(v_c_169_) == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_1(v_f_168_, v___x_170_);
v___x_172_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_167_, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_183_; 
v_val_173_ = lean_ctor_get(v_c_169_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_c_169_);
if (v_isSharedCheck_183_ == 0)
{
v___x_175_ = v_c_169_;
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_val_173_);
lean_dec(v_c_169_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_snd_177_; lean_object* v___x_179_; 
v_snd_177_ = lean_ctor_get(v_val_173_, 1);
lean_inc(v_snd_177_);
lean_dec(v_val_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_snd_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_snd_177_);
v___x_179_ = v_reuseFailAlloc_182_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_apply_1(v_f_168_, v___x_179_);
v___x_181_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_167_, v___x_180_);
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_k_189_, lean_object* v_f_190_, lean_object* v_c_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DTreeMap_Internal_Cell_alter___redArg(v_k_189_, v_f_190_, v_c_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___boxed(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_k_198_, lean_object* v_f_199_, lean_object* v_c_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DTreeMap_Internal_Cell_alter(v_00_u03b1_193_, v_00_u03b2_194_, v_inst_195_, v_inst_196_, v_inst_197_, v_k_198_, v_f_199_, v_c_200_);
lean_dec_ref(v_inst_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(lean_object* v_c_202_){
_start:
{
if (lean_obj_tag(v_c_202_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v_val_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_val_204_ = lean_ctor_get(v_c_202_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_c_202_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v_c_202_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_val_204_);
lean_dec(v_c_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_snd_208_; lean_object* v___x_210_; 
v_snd_208_ = lean_ctor_get(v_val_204_, 1);
lean_inc(v_snd_208_);
lean_dec(v_val_204_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v_snd_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_snd_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f(lean_object* v_00_u03b1_213_, lean_object* v_00_u03b2_214_, lean_object* v_inst_215_, lean_object* v_k_216_, lean_object* v_c_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___boxed(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_inst_221_, lean_object* v_k_222_, lean_object* v_c_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f(v_00_u03b1_219_, v_00_u03b2_220_, v_inst_221_, v_k_222_, v_c_223_);
lean_dec(v_k_222_);
lean_dec_ref(v_inst_221_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(lean_object* v_k_225_, lean_object* v_f_226_, lean_object* v_c_227_){
_start:
{
if (lean_obj_tag(v_c_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_1(v_f_226_, v___x_228_);
v___x_230_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_225_, v___x_229_);
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_241_; 
v_val_231_ = lean_ctor_get(v_c_227_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_c_227_);
if (v_isSharedCheck_241_ == 0)
{
v___x_233_ = v_c_227_;
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_dec(v_c_227_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_snd_235_; lean_object* v___x_237_; 
v_snd_235_ = lean_ctor_get(v_val_231_, 1);
lean_inc(v_snd_235_);
lean_dec(v_val_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v_snd_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_snd_235_);
v___x_237_ = v_reuseFailAlloc_240_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_apply_1(v_f_226_, v___x_237_);
v___x_239_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_225_, v___x_238_);
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_k_246_, lean_object* v_f_247_, lean_object* v_c_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(v_k_246_, v_f_247_, v_c_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___boxed(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_k_254_, lean_object* v_f_255_, lean_object* v_c_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_DTreeMap_Internal_Cell_Const_alter(v_00_u03b1_250_, v_00_u03b2_251_, v_inst_252_, v_inst_253_, v_k_254_, v_f_255_, v_c_256_);
lean_dec_ref(v_inst_252_);
return v_res_257_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_258_ = 1;
v___x_259_ = l_Ordering_ctorIdx(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(lean_object* v_k_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_fst_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_fst_262_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_fst_262_);
lean_dec_ref(v_x_261_);
v___x_263_ = lean_apply_1(v_k_260_, v_fst_262_);
v___x_264_ = lean_unbox(v___x_263_);
v___x_265_ = l_Ordering_ctorIdx(v___x_264_);
v___x_266_ = lean_obj_once(&l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___closed__0, &l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___closed__0_once, _init_l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___closed__0);
v___x_267_ = lean_nat_dec_eq(v___x_265_, v___x_266_);
lean_dec(v___x_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed(lean_object* v_k_268_, lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(v_k_268_, v_x_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg(lean_object* v_l_272_, lean_object* v_k_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; 
v___f_274_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_274_, 0, v_k_273_);
v___x_275_ = l_List_find_x3f___redArg(v___f_274_, v_l_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_inst_278_, lean_object* v_l_279_, lean_object* v_k_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_DTreeMap_Internal_List_findCell___redArg(v_l_279_, v_k_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___boxed(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_inst_284_, lean_object* v_l_285_, lean_object* v_k_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_DTreeMap_Internal_List_findCell(v_00_u03b1_282_, v_00_u03b2_283_, v_inst_284_, v_l_285_, v_k_286_);
lean_dec_ref(v_inst_284_);
return v_res_287_;
}
}
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Cell(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
