// Lean compiler output
// Module: Std.Data.Iterators.Producers.Range
// Imports: public import Init.Data.Range.Polymorphic.Iterators
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
LEAN_EXPORT lean_object* l_Std_Rcc_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_iter___redArg(lean_object* v_r_1_){
_start:
{
lean_object* v_lower_2_; lean_object* v_upper_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_lower_2_ = lean_ctor_get(v_r_1_, 0);
v_upper_3_ = lean_ctor_get(v_r_1_, 1);
v_isSharedCheck_11_ = !lean_is_exclusive(v_r_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_r_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_upper_3_);
lean_inc(v_lower_2_);
lean_dec(v_r_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v_lower_2_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_upper_3_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_iter(lean_object* v_00_u03b1_12_, lean_object* v_r_13_){
_start:
{
lean_object* v_lower_14_; lean_object* v_upper_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_23_; 
v_lower_14_ = lean_ctor_get(v_r_13_, 0);
v_upper_15_ = lean_ctor_get(v_r_13_, 1);
v_isSharedCheck_23_ = !lean_is_exclusive(v_r_13_);
if (v_isSharedCheck_23_ == 0)
{
v___x_17_ = v_r_13_;
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_upper_15_);
lean_inc(v_lower_14_);
lean_dec(v_r_13_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_19_, 0, v_lower_14_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_19_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_upper_15_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_iter___redArg(lean_object* v_r_24_){
_start:
{
lean_object* v_lower_25_; lean_object* v_upper_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_34_; 
v_lower_25_ = lean_ctor_get(v_r_24_, 0);
v_upper_26_ = lean_ctor_get(v_r_24_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_r_24_);
if (v_isSharedCheck_34_ == 0)
{
v___x_28_ = v_r_24_;
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_upper_26_);
lean_inc(v_lower_25_);
lean_dec(v_r_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v_lower_25_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_30_);
v___x_32_ = v___x_28_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_upper_26_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_iter(lean_object* v_00_u03b1_35_, lean_object* v_r_36_){
_start:
{
lean_object* v_lower_37_; lean_object* v_upper_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_46_; 
v_lower_37_ = lean_ctor_get(v_r_36_, 0);
v_upper_38_ = lean_ctor_get(v_r_36_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_r_36_);
if (v_isSharedCheck_46_ == 0)
{
v___x_40_ = v_r_36_;
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_upper_38_);
lean_inc(v_lower_37_);
lean_dec(v_r_36_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v_lower_37_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v___x_42_);
v___x_44_ = v___x_40_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_upper_38_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rci_iter___redArg(lean_object* v_r_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v_r_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_iter(lean_object* v_00_u03b1_49_, lean_object* v_r_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_r_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_iter___redArg(lean_object* v_inst_52_, lean_object* v_r_53_){
_start:
{
lean_object* v_succ_x3f_54_; lean_object* v_lower_55_; lean_object* v_upper_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_succ_x3f_54_ = lean_ctor_get(v_inst_52_, 0);
lean_inc_ref(v_succ_x3f_54_);
lean_dec_ref(v_inst_52_);
v_lower_55_ = lean_ctor_get(v_r_53_, 0);
v_upper_56_ = lean_ctor_get(v_r_53_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_r_53_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v_r_53_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_upper_56_);
lean_inc(v_lower_55_);
lean_dec(v_r_53_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_apply_1(v_succ_x3f_54_, v_lower_55_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_upper_56_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_iter(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_r_67_){
_start:
{
lean_object* v_succ_x3f_68_; lean_object* v_lower_69_; lean_object* v_upper_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v_succ_x3f_68_ = lean_ctor_get(v_inst_66_, 0);
lean_inc_ref(v_succ_x3f_68_);
lean_dec_ref(v_inst_66_);
v_lower_69_ = lean_ctor_get(v_r_67_, 0);
v_upper_70_ = lean_ctor_get(v_r_67_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_r_67_);
if (v_isSharedCheck_78_ == 0)
{
v___x_72_ = v_r_67_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_upper_70_);
lean_inc(v_lower_69_);
lean_dec(v_r_67_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_74_ = lean_apply_1(v_succ_x3f_68_, v_lower_69_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_74_);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_upper_70_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_iter___redArg(lean_object* v_inst_79_, lean_object* v_r_80_){
_start:
{
lean_object* v_succ_x3f_81_; lean_object* v_lower_82_; lean_object* v_upper_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v_succ_x3f_81_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_ref(v_succ_x3f_81_);
lean_dec_ref(v_inst_79_);
v_lower_82_ = lean_ctor_get(v_r_80_, 0);
v_upper_83_ = lean_ctor_get(v_r_80_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_r_80_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v_r_80_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_upper_83_);
lean_inc(v_lower_82_);
lean_dec(v_r_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_apply_1(v_succ_x3f_81_, v_lower_82_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_upper_83_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_iter(lean_object* v_00_u03b1_92_, lean_object* v_inst_93_, lean_object* v_r_94_){
_start:
{
lean_object* v_succ_x3f_95_; lean_object* v_lower_96_; lean_object* v_upper_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_succ_x3f_95_ = lean_ctor_get(v_inst_93_, 0);
lean_inc_ref(v_succ_x3f_95_);
lean_dec_ref(v_inst_93_);
v_lower_96_ = lean_ctor_get(v_r_94_, 0);
v_upper_97_ = lean_ctor_get(v_r_94_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_r_94_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v_r_94_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_upper_97_);
lean_inc(v_lower_96_);
lean_dec(v_r_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_apply_1(v_succ_x3f_95_, v_lower_96_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_101_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_upper_97_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_iter___redArg(lean_object* v_inst_106_, lean_object* v_r_107_){
_start:
{
lean_object* v_succ_x3f_108_; lean_object* v___x_109_; 
v_succ_x3f_108_ = lean_ctor_get(v_inst_106_, 0);
lean_inc_ref(v_succ_x3f_108_);
lean_dec_ref(v_inst_106_);
v___x_109_ = lean_apply_1(v_succ_x3f_108_, v_r_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_iter(lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_r_112_){
_start:
{
lean_object* v_succ_x3f_113_; lean_object* v___x_114_; 
v_succ_x3f_113_ = lean_ctor_get(v_inst_111_, 0);
lean_inc_ref(v_succ_x3f_113_);
lean_dec_ref(v_inst_111_);
v___x_114_ = lean_apply_1(v_succ_x3f_113_, v_r_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_iter___redArg(lean_object* v_inst_115_, lean_object* v_r_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v_inst_115_);
lean_ctor_set(v___x_117_, 1, v_r_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_iter(lean_object* v_00_u03b1_118_, lean_object* v_inst_119_, lean_object* v_r_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_inst_119_);
lean_ctor_set(v___x_121_, 1, v_r_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_iter___redArg(lean_object* v_inst_122_, lean_object* v_r_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_inst_122_);
lean_ctor_set(v___x_124_, 1, v_r_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_iter(lean_object* v_00_u03b1_125_, lean_object* v_inst_126_, lean_object* v_r_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_inst_126_);
lean_ctor_set(v___x_128_, 1, v_r_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_iter___redArg(lean_object* v_inst_129_){
_start:
{
lean_inc(v_inst_129_);
return v_inst_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_iter___redArg___boxed(lean_object* v_inst_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Rii_iter___redArg(v_inst_130_);
lean_dec(v_inst_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_iter(lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_x_134_){
_start:
{
lean_inc(v_inst_133_);
return v_inst_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_iter___boxed(lean_object* v_00_u03b1_135_, lean_object* v_inst_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Rii_iter(v_00_u03b1_135_, v_inst_136_, v_x_137_);
lean_dec(v_inst_136_);
return v_res_138_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Range(builtin);
}
#ifdef __cplusplus
}
#endif
