// Lean compiler output
// Module: Init.Data.List.Attach
// Imports: import all Init.Data.List.Lemmas public import Init.Data.List.Lemmas import Init.Data.List.Count import Init.Data.Subtype.Basic
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
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_pmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmapImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_unattach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmap___redArg(lean_object* v_f_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
lean_dec(v_f_1_);
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_x_2_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_x_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_12_; 
lean_inc(v_f_1_);
v___x_9_ = lean_apply_2(v_f_1_, v_head_4_, lean_box(0));
v___x_10_ = l_List_pmap___redArg(v_f_1_, v_tail_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_10_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v___x_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_pmap(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_P_17_, lean_object* v_f_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_List_pmap___redArg(v_f_18_, v_x_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(lean_object* v_l_22_){
_start:
{
lean_inc(v_l_22_);
return v_l_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg___boxed(lean_object* v_l_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(v_l_23_);
lean_dec(v_l_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl(lean_object* v_00_u03b1_25_, lean_object* v_l_26_, lean_object* v_P_27_, lean_object* v_x_28_){
_start:
{
lean_inc(v_l_26_);
return v_l_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___boxed(lean_object* v_00_u03b1_29_, lean_object* v_l_30_, lean_object* v_P_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl(v_00_u03b1_29_, v_l_30_, v_P_31_, v_x_32_);
lean_dec(v_l_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_List_attach___redArg(lean_object* v_l_34_){
_start:
{
lean_inc(v_l_34_);
return v_l_34_;
}
}
LEAN_EXPORT lean_object* l_List_attach___redArg___boxed(lean_object* v_l_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_List_attach___redArg(v_l_35_);
lean_dec(v_l_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_List_attach(lean_object* v_00_u03b1_37_, lean_object* v_l_38_){
_start:
{
lean_inc(v_l_38_);
return v_l_38_;
}
}
LEAN_EXPORT lean_object* l_List_attach___boxed(lean_object* v_00_u03b1_39_, lean_object* v_l_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_List_attach(v_00_u03b1_39_, v_l_40_);
lean_dec(v_l_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg___lam__0(lean_object* v_f_42_, lean_object* v_x_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_apply_2(v_f_42_, v_x_43_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg(lean_object* v_f_45_, lean_object* v_l_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___f_47_ = lean_alloc_closure((void*)(l_List_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_47_, 0, v_f_45_);
v___x_48_ = lean_box(0);
v___x_49_ = l_List_mapTR_loop___redArg(v___f_47_, v_l_46_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_List_pmapImpl(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_P_52_, lean_object* v_f_53_, lean_object* v_l_54_, lean_object* v_H_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___f_56_ = lean_alloc_closure((void*)(l_List_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_56_, 0, v_f_53_);
v___x_57_ = lean_box(0);
v___x_58_ = l_List_mapTR_loop___redArg(v___f_56_, v_l_54_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter___redArg(lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_62_; 
lean_dec(v_h__2_61_);
v___x_62_ = lean_apply_1(v_h__1_60_, lean_box(0));
return v___x_62_;
}
else
{
lean_object* v_head_63_; lean_object* v_tail_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_60_);
v_head_63_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_head_63_);
v_tail_64_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_tail_64_);
lean_dec_ref(v_x_59_);
v___x_65_ = lean_apply_3(v_h__2_61_, v_head_63_, v_tail_64_, lean_box(0));
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter(lean_object* v_00_u03b1_66_, lean_object* v_P_67_, lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_73_; 
lean_dec(v_h__2_72_);
v___x_73_ = lean_apply_1(v_h__1_71_, lean_box(0));
return v___x_73_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_71_);
v_head_74_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_head_74_);
v_tail_75_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_tail_75_);
lean_dec_ref(v_x_69_);
v___x_76_ = lean_apply_3(v_h__2_72_, v_head_74_, v_tail_75_, lean_box(0));
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_79_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__1_78_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_83_; 
lean_dec(v_h__1_78_);
v_val_82_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_82_);
lean_dec_ref(v_x_77_);
v___x_83_ = lean_apply_1(v_h__2_79_, v_val_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_84_, lean_object* v_motive_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_88_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_apply_1(v_h__1_87_, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v_val_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_87_);
v_val_91_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_val_91_);
lean_dec_ref(v_x_86_);
v___x_92_ = lean_apply_1(v_h__2_88_, v_val_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
if (lean_obj_tag(v_a_93_) == 0)
{
lean_object* v___x_95_; 
v___x_95_ = l_List_reverse___redArg(v_a_94_);
return v___x_95_;
}
else
{
lean_object* v_head_96_; lean_object* v_tail_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_head_96_ = lean_ctor_get(v_a_93_, 0);
v_tail_97_ = lean_ctor_get(v_a_93_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_a_93_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v_a_93_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_tail_97_);
lean_inc(v_head_96_);
lean_dec(v_a_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_a_94_);
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_head_96_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_a_94_);
v___x_102_ = v_reuseFailAlloc_104_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
v_a_93_ = v_tail_97_;
v_a_94_ = v___x_102_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unattach___redArg(lean_object* v_l_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_l_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_List_unattach(lean_object* v_00_u03b1_109_, lean_object* v_p_110_, lean_object* v_l_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_List_unattach___redArg(v_l_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0(lean_object* v_00_u03b1_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_a_114_, v_a_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__1_118_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__2_119_, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; 
lean_dec(v_h__2_119_);
v_val_122_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_val_122_);
lean_dec_ref(v_x_117_);
v___x_123_ = lean_apply_1(v_h__1_118_, v_val_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_h__1_127_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_1(v_h__2_128_, v___x_129_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; 
lean_dec(v_h__2_128_);
v_val_131_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_val_131_);
lean_dec_ref(v_x_126_);
v___x_132_ = lean_apply_1(v_h__1_127_, v_val_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(uint8_t v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (v_x_133_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_h__1_134_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_1(v_h__2_135_, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__2_135_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__1_134_, v___x_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
uint8_t v_x_26__boxed_143_; lean_object* v_res_144_; 
v_x_26__boxed_143_ = lean_unbox(v_x_140_);
v_res_144_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_143_, v_h__1_141_, v_h__2_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(lean_object* v_motive_145_, uint8_t v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
if (v_x_146_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_147_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v_h__2_148_, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_h__2_148_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_1(v_h__1_147_, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
uint8_t v_x_37__boxed_157_; lean_object* v_res_158_; 
v_x_37__boxed_157_ = lean_unbox(v_x_154_);
v_res_158_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(v_motive_153_, v_x_37__boxed_157_, v_h__1_155_, v_h__2_156_);
return v_res_158_;
}
}
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
