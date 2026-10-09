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
lean_object* lean_obj_tag_nat(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Cell_empty___redArg(){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Cell_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_38_;
v_res_38_ = l_Std_DTreeMap_Internal_Cell_empty___redArg();
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___redArg___boxed(lean_object* v___dummy_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_DTreeMap_Internal_Cell_empty___redArg();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_inst_43_, lean_object* v_k_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_empty___boxed(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_inst_48_, lean_object* v_k_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_DTreeMap_Internal_Cell_empty(v_00_u03b1_46_, v_00_u03b2_47_, v_inst_48_, v_k_49_);
lean_dec_ref(v_k_49_);
lean_dec_ref(v_inst_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___redArg(lean_object* v_k_51_, lean_object* v_v_x3f_52_){
_start:
{
if (lean_obj_tag(v_v_x3f_52_) == 0)
{
lean_object* v___x_53_; 
lean_dec(v_k_51_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
lean_object* v_val_54_; lean_object* v___x_55_; 
v_val_54_ = lean_ctor_get(v_v_x3f_52_, 0);
lean_inc(v_val_54_);
lean_dec_ref_known(v_v_x3f_52_, 1);
v___x_55_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_51_, v_val_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_inst_58_, lean_object* v_k_59_, lean_object* v_v_x3f_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_59_, v_v_x3f_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_ofOption___boxed(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_inst_64_, lean_object* v_k_65_, lean_object* v_v_x3f_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_DTreeMap_Internal_Cell_ofOption(v_00_u03b1_62_, v_00_u03b2_63_, v_inst_64_, v_k_65_, v_v_x3f_66_);
lean_dec_ref(v_inst_64_);
return v_res_67_;
}
}
uint8_t l_Std_DTreeMap_Internal_Cell_contains___redArg(lean_object* v_c_68_){
_start:
{
if (lean_obj_tag(v_c_68_) == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Cell_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_68_ = stack[0].m_obj;
uint8_t v_res_71_;
v_res_71_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_68_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___redArg___boxed(lean_object* v_c_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_72_);
lean_dec(v_c_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_Std_DTreeMap_Internal_Cell_contains(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_inst_77_, lean_object* v_k_78_, lean_object* v_c_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Cell_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_77_ = stack[2].m_obj;
lean_object* v_k_78_ = stack[3].m_obj;
lean_object* v_c_79_ = stack[4].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Std_DTreeMap_Internal_Cell_contains(lean_box(0), lean_box(0), v_inst_77_, v_k_78_, v_c_79_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_contains___boxed(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_inst_84_, lean_object* v_k_85_, lean_object* v_c_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Std_DTreeMap_Internal_Cell_contains(v_00_u03b1_82_, v_00_u03b2_83_, v_inst_84_, v_k_85_, v_c_86_);
lean_dec(v_c_86_);
lean_dec_ref(v_k_85_);
lean_dec_ref(v_inst_84_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(lean_object* v_c_89_){
_start:
{
if (lean_obj_tag(v_c_89_) == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v_val_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_99_; 
v_val_91_ = lean_ctor_get(v_c_89_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_c_89_);
if (v_isSharedCheck_99_ == 0)
{
v___x_93_ = v_c_89_;
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_val_91_);
lean_dec(v_c_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_snd_95_; lean_object* v___x_97_; 
v_snd_95_ = lean_ctor_get(v_val_91_, 1);
lean_inc(v_snd_95_);
lean_dec(v_val_91_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v_snd_95_);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_snd_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_k_105_, lean_object* v_c_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_get_x3f___boxed(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_k_113_, lean_object* v_c_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_DTreeMap_Internal_Cell_get_x3f(v_00_u03b1_108_, v_00_u03b2_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_k_113_, v_c_114_);
lean_dec(v_k_113_);
lean_dec_ref(v_inst_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(lean_object* v_c_116_){
_start:
{
if (lean_obj_tag(v_c_116_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
lean_object* v_val_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_134_; 
v_val_118_ = lean_ctor_get(v_c_116_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_c_116_);
if (v_isSharedCheck_134_ == 0)
{
v___x_120_ = v_c_116_;
v_isShared_121_ = v_isSharedCheck_134_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_val_118_);
lean_dec(v_c_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_134_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_fst_122_; lean_object* v_snd_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_133_; 
v_fst_122_ = lean_ctor_get(v_val_118_, 0);
v_snd_123_ = lean_ctor_get(v_val_118_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v_val_118_);
if (v_isSharedCheck_133_ == 0)
{
v___x_125_ = v_val_118_;
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_snd_123_);
lean_inc(v_fst_122_);
lean_dec(v_val_118_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fst_122_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_snd_123_);
v___x_128_ = v_reuseFailAlloc_132_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_130_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_128_);
v___x_130_ = v___x_120_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_inst_137_, lean_object* v_k_138_, lean_object* v_c_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getEntry_x3f___boxed(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_inst_143_, lean_object* v_k_144_, lean_object* v_c_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f(v_00_u03b1_141_, v_00_u03b2_142_, v_inst_143_, v_k_144_, v_c_145_);
lean_dec(v_k_144_);
lean_dec_ref(v_inst_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(lean_object* v_c_147_){
_start:
{
if (lean_obj_tag(v_c_147_) == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_val_149_ = lean_ctor_get(v_c_147_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v_c_147_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v_c_147_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_val_149_);
lean_dec(v_c_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_fst_153_; lean_object* v___x_155_; 
v_fst_153_ = lean_ctor_get(v_val_149_, 0);
lean_inc(v_fst_153_);
lean_dec(v_val_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v_fst_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_fst_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f(lean_object* v_00_u03b1_158_, lean_object* v_00_u03b2_159_, lean_object* v_inst_160_, lean_object* v_k_161_, lean_object* v_c_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_getKey_x3f___boxed(lean_object* v_00_u03b1_164_, lean_object* v_00_u03b2_165_, lean_object* v_inst_166_, lean_object* v_k_167_, lean_object* v_c_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f(v_00_u03b1_164_, v_00_u03b2_165_, v_inst_166_, v_k_167_, v_c_168_);
lean_dec(v_k_167_);
lean_dec_ref(v_inst_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___redArg(lean_object* v_k_170_, lean_object* v_f_171_, lean_object* v_c_172_){
_start:
{
if (lean_obj_tag(v_c_172_) == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_box(0);
v___x_174_ = lean_apply_1(v_f_171_, v___x_173_);
v___x_175_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_170_, v___x_174_);
return v___x_175_;
}
else
{
lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
v_val_176_ = lean_ctor_get(v_c_172_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_c_172_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v_c_172_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_dec(v_c_172_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_snd_180_; lean_object* v___x_182_; 
v_snd_180_ = lean_ctor_get(v_val_176_, 1);
lean_inc(v_snd_180_);
lean_dec(v_val_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v_snd_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_snd_180_);
v___x_182_ = v_reuseFailAlloc_185_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_apply_1(v_f_171_, v___x_182_);
v___x_184_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_170_, v___x_183_);
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter(lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_k_192_, lean_object* v_f_193_, lean_object* v_c_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Std_DTreeMap_Internal_Cell_alter___redArg(v_k_192_, v_f_193_, v_c_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_alter___boxed(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_k_201_, lean_object* v_f_202_, lean_object* v_c_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DTreeMap_Internal_Cell_alter(v_00_u03b1_196_, v_00_u03b2_197_, v_inst_198_, v_inst_199_, v_inst_200_, v_k_201_, v_f_202_, v_c_203_);
lean_dec_ref(v_inst_198_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(lean_object* v_c_205_){
_start:
{
if (lean_obj_tag(v_c_205_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_val_207_ = lean_ctor_get(v_c_205_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_c_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v_c_205_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_val_207_);
lean_dec(v_c_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_snd_211_; lean_object* v___x_213_; 
v_snd_211_ = lean_ctor_get(v_val_207_, 1);
lean_inc(v_snd_211_);
lean_dec(v_val_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v_snd_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_snd_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_inst_218_, lean_object* v_k_219_, lean_object* v_c_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_get_x3f___boxed(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_inst_224_, lean_object* v_k_225_, lean_object* v_c_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f(v_00_u03b1_222_, v_00_u03b2_223_, v_inst_224_, v_k_225_, v_c_226_);
lean_dec(v_k_225_);
lean_dec_ref(v_inst_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(lean_object* v_k_228_, lean_object* v_f_229_, lean_object* v_c_230_){
_start:
{
if (lean_obj_tag(v_c_230_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_1(v_f_229_, v___x_231_);
v___x_233_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_228_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v_val_234_ = lean_ctor_get(v_c_230_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_c_230_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v_c_230_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_val_234_);
lean_dec(v_c_230_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_snd_238_; lean_object* v___x_240_; 
v_snd_238_ = lean_ctor_get(v_val_234_, 1);
lean_inc(v_snd_238_);
lean_dec(v_val_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v_snd_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_snd_238_);
v___x_240_ = v_reuseFailAlloc_243_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_apply_1(v_f_229_, v___x_240_);
v___x_242_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_228_, v___x_241_);
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_k_249_, lean_object* v_f_250_, lean_object* v_c_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(v_k_249_, v_f_250_, v_c_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Cell_Const_alter___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_k_257_, lean_object* v_f_258_, lean_object* v_c_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DTreeMap_Internal_Cell_Const_alter(v_00_u03b1_253_, v_00_u03b2_254_, v_inst_255_, v_inst_256_, v_k_257_, v_f_258_, v_c_259_);
lean_dec_ref(v_inst_255_);
return v_res_260_;
}
}
uint8_t l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(lean_object* v_k_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_fst_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_fst_263_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_fst_263_);
lean_dec_ref(v_x_262_);
v___x_264_ = lean_apply_1(v_k_261_, v_fst_263_);
v___x_265_ = lean_obj_tag_nat(v___x_264_);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_dec_eq(v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_261_ = stack[0].m_obj;
lean_object* v_x_262_ = stack[1].m_obj;
uint8_t v_res_268_;
v_res_268_ = l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(v_k_261_, v_x_262_);
stack->m_num = v_res_268_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed(lean_object* v_k_269_, lean_object* v_x_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(v_k_269_, v_x_270_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___redArg(lean_object* v_l_273_, lean_object* v_k_274_){
_start:
{
lean_object* v___f_275_; lean_object* v___x_276_; 
v___f_275_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_275_, 0, v_k_274_);
v___x_276_ = l_List_find_x3f___redArg(v___f_275_, v_l_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_inst_279_, lean_object* v_l_280_, lean_object* v_k_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DTreeMap_Internal_List_findCell___redArg(v_l_280_, v_k_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_List_findCell___boxed(lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_inst_285_, lean_object* v_l_286_, lean_object* v_k_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_DTreeMap_Internal_List_findCell(v_00_u03b1_283_, v_00_u03b2_284_, v_inst_285_, v_l_286_, v_k_287_);
lean_dec_ref(v_inst_285_);
return v_res_288_;
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
