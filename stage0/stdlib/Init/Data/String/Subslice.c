// Lean compiler output
// Module: Init.Data.String.Subslice
// Imports: public import Init.Data.String.Basic import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Lemmas.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSubslice(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSubslice___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_instCoeOut(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_copy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_copy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_instToString(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_subslice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_subslice(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_subslice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_subslice_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_subslice_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_subslice_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.String.Subslice"};
static const lean_object* l_String_Slice_subslice_x21___closed__0 = (const lean_object*)&l_String_Slice_subslice_x21___closed__0_value;
static const lean_string_object l_String_Slice_subslice_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "String.Slice.subslice!"};
static const lean_object* l_String_Slice_subslice_x21___closed__1 = (const lean_object*)&l_String_Slice_subslice_x21___closed__1_value;
static const lean_string_object l_String_Slice_subslice_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Trying to construct a degenerate subslice"};
static const lean_object* l_String_Slice_subslice_x21___closed__2 = (const lean_object*)&l_String_Slice_subslice_x21___closed__2_value;
static lean_once_cell_t l_String_Slice_subslice_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_subslice_x21___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_subslice_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_subsliceFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_subsliceFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toSubslice(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toSubslice___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSubslice(lean_object* v_s_1_){
_start:
{
lean_object* v_startInclusive_2_; lean_object* v_endExclusive_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_startInclusive_2_ = lean_ctor_get(v_s_1_, 1);
v_endExclusive_3_ = lean_ctor_get(v_s_1_, 2);
v___x_4_ = lean_nat_sub(v_endExclusive_3_, v_startInclusive_2_);
lean_inc(v___x_4_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSubslice___boxed(lean_object* v_s_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_String_Slice_instInhabitedSubslice(v_s_6_);
lean_dec_ref(v_s_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toSlice(lean_object* v_s_8_, lean_object* v_sl_9_){
_start:
{
lean_object* v_startInclusive_10_; lean_object* v_endExclusive_11_; lean_object* v_str_12_; lean_object* v_startInclusive_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_22_; 
v_startInclusive_10_ = lean_ctor_get(v_sl_9_, 0);
v_endExclusive_11_ = lean_ctor_get(v_sl_9_, 1);
v_str_12_ = lean_ctor_get(v_s_8_, 0);
v_startInclusive_13_ = lean_ctor_get(v_s_8_, 1);
v_isSharedCheck_22_ = !lean_is_exclusive(v_s_8_);
if (v_isSharedCheck_22_ == 0)
{
lean_object* v_unused_23_; 
v_unused_23_ = lean_ctor_get(v_s_8_, 2);
lean_dec(v_unused_23_);
v___x_15_ = v_s_8_;
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_startInclusive_13_);
lean_inc(v_str_12_);
lean_dec(v_s_8_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_17_ = lean_nat_add(v_startInclusive_13_, v_startInclusive_10_);
v___x_18_ = lean_nat_add(v_startInclusive_13_, v_endExclusive_11_);
lean_dec(v_startInclusive_13_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 2, v___x_18_);
lean_ctor_set(v___x_15_, 1, v___x_17_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_str_12_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_21_, 2, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toSlice___boxed(lean_object* v_s_24_, lean_object* v_sl_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_String_Slice_Subslice_toSlice(v_s_24_, v_sl_25_);
lean_dec_ref(v_sl_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_instCoeOut(lean_object* v_s_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_closure((void*)(l_String_Slice_Subslice_toSlice___boxed), 2, 1);
lean_closure_set(v___x_28_, 0, v_s_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_copy(lean_object* v_s_29_, lean_object* v_sl_30_){
_start:
{
lean_object* v_startInclusive_31_; lean_object* v_endExclusive_32_; lean_object* v_str_33_; lean_object* v_startInclusive_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_startInclusive_31_ = lean_ctor_get(v_sl_30_, 0);
v_endExclusive_32_ = lean_ctor_get(v_sl_30_, 1);
v_str_33_ = lean_ctor_get(v_s_29_, 0);
v_startInclusive_34_ = lean_ctor_get(v_s_29_, 1);
v___x_35_ = lean_nat_add(v_startInclusive_34_, v_startInclusive_31_);
v___x_36_ = lean_nat_add(v_startInclusive_34_, v_endExclusive_32_);
v___x_37_ = lean_string_utf8_extract(v_str_33_, v___x_35_, v___x_36_);
lean_dec(v___x_36_);
lean_dec(v___x_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_copy___boxed(lean_object* v_s_38_, lean_object* v_sl_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_String_Slice_Subslice_copy(v_s_38_, v_sl_39_);
lean_dec_ref(v_sl_39_);
lean_dec_ref(v_s_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toString(lean_object* v_s_41_, lean_object* v_sl_42_){
_start:
{
lean_object* v_startInclusive_43_; lean_object* v_endExclusive_44_; lean_object* v_str_45_; lean_object* v_startInclusive_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_startInclusive_43_ = lean_ctor_get(v_sl_42_, 0);
v_endExclusive_44_ = lean_ctor_get(v_sl_42_, 1);
v_str_45_ = lean_ctor_get(v_s_41_, 0);
v_startInclusive_46_ = lean_ctor_get(v_s_41_, 1);
v___x_47_ = lean_nat_add(v_startInclusive_46_, v_startInclusive_43_);
v___x_48_ = lean_nat_add(v_startInclusive_46_, v_endExclusive_44_);
v___x_49_ = lean_string_utf8_extract(v_str_45_, v___x_47_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v___x_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toString___boxed(lean_object* v_s_50_, lean_object* v_sl_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_String_Slice_Subslice_toString(v_s_50_, v_sl_51_);
lean_dec_ref(v_sl_51_);
lean_dec_ref(v_s_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_instToString(lean_object* v_s_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_closure((void*)(l_String_Slice_Subslice_toString___boxed), 2, 1);
lean_closure_set(v___x_54_, 0, v_s_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice___redArg(lean_object* v_newStart_55_, lean_object* v_newEnd_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v_newStart_55_);
lean_ctor_set(v___x_57_, 1, v_newEnd_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice(lean_object* v_s_58_, lean_object* v_newStart_59_, lean_object* v_newEnd_60_, lean_object* v_h_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_newStart_59_);
lean_ctor_set(v___x_62_, 1, v_newEnd_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice___boxed(lean_object* v_s_63_, lean_object* v_newStart_64_, lean_object* v_newEnd_65_, lean_object* v_h_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_String_Slice_subslice(v_s_63_, v_newStart_64_, v_newEnd_65_, v_h_66_);
lean_dec_ref(v_s_63_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_subslice_x21_spec__0(lean_object* v_s_68_, lean_object* v_msg_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = l_String_Slice_instInhabitedSubslice(v_s_68_);
v___x_71_ = lean_panic_fn_borrowed(v___x_70_, v_msg_69_);
lean_dec_ref(v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_subslice_x21_spec__0___boxed(lean_object* v_s_72_, lean_object* v_msg_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_panic___at___00String_Slice_subslice_x21_spec__0(v_s_72_, v_msg_73_);
lean_dec_ref(v_s_72_);
return v_res_74_;
}
}
static lean_object* _init_l_String_Slice_subslice_x21___closed__3(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_78_ = ((lean_object*)(l_String_Slice_subslice_x21___closed__2));
v___x_79_ = lean_unsigned_to_nat(4u);
v___x_80_ = lean_unsigned_to_nat(128u);
v___x_81_ = ((lean_object*)(l_String_Slice_subslice_x21___closed__1));
v___x_82_ = ((lean_object*)(l_String_Slice_subslice_x21___closed__0));
v___x_83_ = l_mkPanicMessageWithDecl(v___x_82_, v___x_81_, v___x_80_, v___x_79_, v___x_78_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice_x21(lean_object* v_s_84_, lean_object* v_newStart_85_, lean_object* v_newEnd_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = lean_nat_dec_le(v_newStart_85_, v_newEnd_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_newEnd_86_);
lean_dec(v_newStart_85_);
v___x_88_ = lean_obj_once(&l_String_Slice_subslice_x21___closed__3, &l_String_Slice_subslice_x21___closed__3_once, _init_l_String_Slice_subslice_x21___closed__3);
v___x_89_ = l_panic___at___00String_Slice_subslice_x21_spec__0(v_s_84_, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_newStart_85_);
lean_ctor_set(v___x_90_, 1, v_newEnd_86_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice_x21___boxed(lean_object* v_s_91_, lean_object* v_newStart_92_, lean_object* v_newEnd_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_String_Slice_subslice_x21(v_s_91_, v_newStart_92_, v_newEnd_93_);
lean_dec_ref(v_s_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subsliceFrom(lean_object* v_s_95_, lean_object* v_newStart_96_){
_start:
{
lean_object* v_startInclusive_97_; lean_object* v_endExclusive_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_startInclusive_97_ = lean_ctor_get(v_s_95_, 1);
v_endExclusive_98_ = lean_ctor_get(v_s_95_, 2);
v___x_99_ = lean_nat_sub(v_endExclusive_98_, v_startInclusive_97_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_newStart_96_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subsliceFrom___boxed(lean_object* v_s_101_, lean_object* v_newStart_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_String_Slice_subsliceFrom(v_s_101_, v_newStart_102_);
lean_dec_ref(v_s_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toSubslice(lean_object* v_s_104_){
_start:
{
lean_object* v_startInclusive_105_; lean_object* v_endExclusive_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_startInclusive_105_ = lean_ctor_get(v_s_104_, 1);
v_endExclusive_106_ = lean_ctor_get(v_s_104_, 2);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_sub(v_endExclusive_106_, v_startInclusive_105_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toSubslice___boxed(lean_object* v_s_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_String_Slice_toSubslice(v_s_110_);
lean_dec_ref(v_s_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___redArg(lean_object* v_p_112_, lean_object* v_sl_113_){
_start:
{
lean_object* v_startInclusive_114_; lean_object* v_endExclusive_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_124_; 
v_startInclusive_114_ = lean_ctor_get(v_sl_113_, 0);
v_endExclusive_115_ = lean_ctor_get(v_sl_113_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_sl_113_);
if (v_isSharedCheck_124_ == 0)
{
v___x_117_ = v_sl_113_;
v_isShared_118_ = v_isSharedCheck_124_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_endExclusive_115_);
lean_inc(v_startInclusive_114_);
lean_dec(v_sl_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_124_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_119_ = lean_nat_add(v_p_112_, v_startInclusive_114_);
lean_dec(v_startInclusive_114_);
v___x_120_ = lean_nat_add(v_p_112_, v_endExclusive_115_);
lean_dec(v_endExclusive_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_120_);
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_122_ = v___x_117_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___redArg___boxed(lean_object* v_p_125_, lean_object* v_sl_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_String_Slice_Subslice_ofSliceFrom___redArg(v_p_125_, v_sl_126_);
lean_dec(v_p_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom(lean_object* v_s_128_, lean_object* v_p_129_, lean_object* v_sl_130_){
_start:
{
lean_object* v_startInclusive_131_; lean_object* v_endExclusive_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_141_; 
v_startInclusive_131_ = lean_ctor_get(v_sl_130_, 0);
v_endExclusive_132_ = lean_ctor_get(v_sl_130_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_sl_130_);
if (v_isSharedCheck_141_ == 0)
{
v___x_134_ = v_sl_130_;
v_isShared_135_ = v_isSharedCheck_141_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_endExclusive_132_);
lean_inc(v_startInclusive_131_);
lean_dec(v_sl_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_141_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_nat_add(v_p_129_, v_startInclusive_131_);
lean_dec(v_startInclusive_131_);
v___x_137_ = lean_nat_add(v_p_129_, v_endExclusive_132_);
lean_dec(v_endExclusive_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_137_);
lean_ctor_set(v___x_134_, 0, v___x_136_);
v___x_139_ = v___x_134_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___boxed(lean_object* v_s_142_, lean_object* v_p_143_, lean_object* v_sl_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_String_Slice_Subslice_ofSliceFrom(v_s_142_, v_p_143_, v_sl_144_);
lean_dec(v_p_143_);
lean_dec_ref(v_s_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft___redArg(lean_object* v_sl_146_, lean_object* v_newStart_147_){
_start:
{
lean_object* v_endExclusive_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_endExclusive_148_ = lean_ctor_get(v_sl_146_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_sl_146_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v_sl_146_, 0);
lean_dec(v_unused_156_);
v___x_150_ = v_sl_146_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_endExclusive_148_);
lean_dec(v_sl_146_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v_newStart_147_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_newStart_147_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_endExclusive_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft(lean_object* v_s_157_, lean_object* v_sl_158_, lean_object* v_newStart_159_, lean_object* v_h_160_){
_start:
{
lean_object* v_endExclusive_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_endExclusive_161_ = lean_ctor_get(v_sl_158_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_sl_158_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v_sl_158_, 0);
lean_dec(v_unused_169_);
v___x_163_ = v_sl_158_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_endExclusive_161_);
lean_dec(v_sl_158_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v_newStart_159_);
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_newStart_159_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_endExclusive_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft___boxed(lean_object* v_s_170_, lean_object* v_sl_171_, lean_object* v_newStart_172_, lean_object* v_h_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_String_Slice_Subslice_extendLeft(v_s_170_, v_sl_171_, v_newStart_172_, v_h_173_);
lean_dec_ref(v_s_170_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast___redArg(lean_object* v_sl_175_){
_start:
{
lean_object* v_startInclusive_176_; lean_object* v_endExclusive_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_startInclusive_176_ = lean_ctor_get(v_sl_175_, 0);
v_endExclusive_177_ = lean_ctor_get(v_sl_175_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_sl_175_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v_sl_175_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_endExclusive_177_);
lean_inc(v_startInclusive_176_);
lean_dec(v_sl_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_startInclusive_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_endExclusive_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast(lean_object* v_s_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_sl_188_){
_start:
{
lean_object* v_startInclusive_189_; lean_object* v_endExclusive_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_startInclusive_189_ = lean_ctor_get(v_sl_188_, 0);
v_endExclusive_190_ = lean_ctor_get(v_sl_188_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_sl_188_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v_sl_188_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_endExclusive_190_);
lean_inc(v_startInclusive_189_);
lean_dec(v_sl_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_startInclusive_189_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_endExclusive_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast___boxed(lean_object* v_s_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_sl_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_String_Slice_Subslice_cast(v_s_198_, v_t_199_, v_h_200_, v_sl_201_);
lean_dec_ref(v_t_199_);
lean_dec_ref(v_s_198_);
return v_res_202_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Subslice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Subslice(builtin);
}
#ifdef __cplusplus
}
#endif
