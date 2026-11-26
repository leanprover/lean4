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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice_decEq___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_startInclusive_3_; lean_object* v_endExclusive_4_; lean_object* v_startInclusive_5_; lean_object* v_endExclusive_6_; uint8_t v_decide_7_; 
v_startInclusive_3_ = lean_ctor_get(v_x_1_, 0);
v_endExclusive_4_ = lean_ctor_get(v_x_1_, 1);
v_startInclusive_5_ = lean_ctor_get(v_x_2_, 0);
v_endExclusive_6_ = lean_ctor_get(v_x_2_, 1);
v_decide_7_ = lean_nat_dec_eq(v_startInclusive_3_, v_startInclusive_5_);
if (v_decide_7_ == 0)
{
return v_decide_7_;
}
else
{
uint8_t v_decide_8_; 
v_decide_8_ = lean_nat_dec_eq(v_endExclusive_4_, v_endExclusive_6_);
return v_decide_8_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice_decEq___redArg___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_String_Slice_instDecidableEqSubslice_decEq___redArg(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice_decEq(lean_object* v_s_13_, lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_String_Slice_instDecidableEqSubslice_decEq___redArg(v_x_14_, v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice_decEq___boxed(lean_object* v_s_17_, lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_String_Slice_instDecidableEqSubslice_decEq(v_s_17_, v_x_18_, v_x_19_);
lean_dec_ref(v_x_19_);
lean_dec_ref(v_x_18_);
lean_dec_ref(v_s_17_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice___redArg(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l_String_Slice_instDecidableEqSubslice_decEq___redArg(v_x_22_, v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice___redArg___boxed(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_String_Slice_instDecidableEqSubslice___redArg(v_x_25_, v_x_26_);
lean_dec_ref(v_x_26_);
lean_dec_ref(v_x_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqSubslice(lean_object* v_s_29_, lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = l_String_Slice_instDecidableEqSubslice_decEq___redArg(v_x_30_, v_x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqSubslice___boxed(lean_object* v_s_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_String_Slice_instDecidableEqSubslice(v_s_33_, v_x_34_, v_x_35_);
lean_dec_ref(v_x_35_);
lean_dec_ref(v_x_34_);
lean_dec_ref(v_s_33_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSubslice(lean_object* v_s_38_){
_start:
{
lean_object* v_startInclusive_39_; lean_object* v_endExclusive_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_startInclusive_39_ = lean_ctor_get(v_s_38_, 1);
v_endExclusive_40_ = lean_ctor_get(v_s_38_, 2);
v___x_41_ = lean_nat_sub(v_endExclusive_40_, v_startInclusive_39_);
lean_inc(v___x_41_);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSubslice___boxed(lean_object* v_s_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_String_Slice_instInhabitedSubslice(v_s_43_);
lean_dec_ref(v_s_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toSlice(lean_object* v_s_45_, lean_object* v_sl_46_){
_start:
{
lean_object* v_startInclusive_47_; lean_object* v_endExclusive_48_; lean_object* v_str_49_; lean_object* v_startInclusive_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_59_; 
v_startInclusive_47_ = lean_ctor_get(v_sl_46_, 0);
v_endExclusive_48_ = lean_ctor_get(v_sl_46_, 1);
v_str_49_ = lean_ctor_get(v_s_45_, 0);
v_startInclusive_50_ = lean_ctor_get(v_s_45_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v_s_45_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v_s_45_, 2);
lean_dec(v_unused_60_);
v___x_52_ = v_s_45_;
v_isShared_53_ = v_isSharedCheck_59_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_startInclusive_50_);
lean_inc(v_str_49_);
lean_dec(v_s_45_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_59_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_54_ = lean_nat_add(v_startInclusive_50_, v_startInclusive_47_);
v___x_55_ = lean_nat_add(v_startInclusive_50_, v_endExclusive_48_);
lean_dec(v_startInclusive_50_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 2, v___x_55_);
lean_ctor_set(v___x_52_, 1, v___x_54_);
v___x_57_ = v___x_52_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_str_49_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_58_, 2, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toSlice___boxed(lean_object* v_s_61_, lean_object* v_sl_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_String_Slice_Subslice_toSlice(v_s_61_, v_sl_62_);
lean_dec_ref(v_sl_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_instCoeOut(lean_object* v_s_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_alloc_closure((void*)(l_String_Slice_Subslice_toSlice___boxed), 2, 1);
lean_closure_set(v___x_65_, 0, v_s_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_copy(lean_object* v_s_66_, lean_object* v_sl_67_){
_start:
{
lean_object* v_startInclusive_68_; lean_object* v_endExclusive_69_; lean_object* v_str_70_; lean_object* v_startInclusive_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_startInclusive_68_ = lean_ctor_get(v_sl_67_, 0);
v_endExclusive_69_ = lean_ctor_get(v_sl_67_, 1);
v_str_70_ = lean_ctor_get(v_s_66_, 0);
v_startInclusive_71_ = lean_ctor_get(v_s_66_, 1);
v___x_72_ = lean_nat_add(v_startInclusive_71_, v_startInclusive_68_);
v___x_73_ = lean_nat_add(v_startInclusive_71_, v_endExclusive_69_);
v___x_74_ = lean_string_utf8_extract_fast(v_str_70_, v___x_72_, v___x_73_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_copy___boxed(lean_object* v_s_75_, lean_object* v_sl_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_String_Slice_Subslice_copy(v_s_75_, v_sl_76_);
lean_dec_ref(v_sl_76_);
lean_dec_ref(v_s_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toString(lean_object* v_s_78_, lean_object* v_sl_79_){
_start:
{
lean_object* v_startInclusive_80_; lean_object* v_endExclusive_81_; lean_object* v_str_82_; lean_object* v_startInclusive_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_startInclusive_80_ = lean_ctor_get(v_sl_79_, 0);
v_endExclusive_81_ = lean_ctor_get(v_sl_79_, 1);
v_str_82_ = lean_ctor_get(v_s_78_, 0);
v_startInclusive_83_ = lean_ctor_get(v_s_78_, 1);
v___x_84_ = lean_nat_add(v_startInclusive_83_, v_startInclusive_80_);
v___x_85_ = lean_nat_add(v_startInclusive_83_, v_endExclusive_81_);
v___x_86_ = lean_string_utf8_extract_fast(v_str_82_, v___x_84_, v___x_85_);
lean_dec(v___x_85_);
lean_dec(v___x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_toString___boxed(lean_object* v_s_87_, lean_object* v_sl_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_String_Slice_Subslice_toString(v_s_87_, v_sl_88_);
lean_dec_ref(v_sl_88_);
lean_dec_ref(v_s_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_instToString(lean_object* v_s_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_closure((void*)(l_String_Slice_Subslice_toString___boxed), 2, 1);
lean_closure_set(v___x_91_, 0, v_s_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice___redArg(lean_object* v_newStart_92_, lean_object* v_newEnd_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_newStart_92_);
lean_ctor_set(v___x_94_, 1, v_newEnd_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice(lean_object* v_s_95_, lean_object* v_newStart_96_, lean_object* v_newEnd_97_, lean_object* v_h_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v_newStart_96_);
lean_ctor_set(v___x_99_, 1, v_newEnd_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice___boxed(lean_object* v_s_100_, lean_object* v_newStart_101_, lean_object* v_newEnd_102_, lean_object* v_h_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_String_Slice_subslice(v_s_100_, v_newStart_101_, v_newEnd_102_, v_h_103_);
lean_dec_ref(v_s_100_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_subslice_x21_spec__0(lean_object* v_s_105_, lean_object* v_msg_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = l_String_Slice_instInhabitedSubslice(v_s_105_);
v___x_108_ = lean_panic_fn_borrowed(v___x_107_, v_msg_106_);
lean_dec_ref(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_subslice_x21_spec__0___boxed(lean_object* v_s_109_, lean_object* v_msg_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_panic___at___00String_Slice_subslice_x21_spec__0(v_s_109_, v_msg_110_);
lean_dec_ref(v_s_109_);
return v_res_111_;
}
}
static lean_object* _init_l_String_Slice_subslice_x21___closed__3(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_115_ = ((lean_object*)(l_String_Slice_subslice_x21___closed__2));
v___x_116_ = lean_unsigned_to_nat(4u);
v___x_117_ = lean_unsigned_to_nat(129u);
v___x_118_ = ((lean_object*)(l_String_Slice_subslice_x21___closed__1));
v___x_119_ = ((lean_object*)(l_String_Slice_subslice_x21___closed__0));
v___x_120_ = l_mkPanicMessageWithDecl(v___x_119_, v___x_118_, v___x_117_, v___x_116_, v___x_115_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice_x21(lean_object* v_s_121_, lean_object* v_newStart_122_, lean_object* v_newEnd_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_le(v_newStart_122_, v_newEnd_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_newEnd_123_);
lean_dec(v_newStart_122_);
v___x_125_ = lean_obj_once(&l_String_Slice_subslice_x21___closed__3, &l_String_Slice_subslice_x21___closed__3_once, _init_l_String_Slice_subslice_x21___closed__3);
v___x_126_ = l_panic___at___00String_Slice_subslice_x21_spec__0(v_s_121_, v___x_125_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_newStart_122_);
lean_ctor_set(v___x_127_, 1, v_newEnd_123_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_subslice_x21___boxed(lean_object* v_s_128_, lean_object* v_newStart_129_, lean_object* v_newEnd_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_String_Slice_subslice_x21(v_s_128_, v_newStart_129_, v_newEnd_130_);
lean_dec_ref(v_s_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subsliceFrom(lean_object* v_s_132_, lean_object* v_newStart_133_){
_start:
{
lean_object* v_startInclusive_134_; lean_object* v_endExclusive_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_startInclusive_134_ = lean_ctor_get(v_s_132_, 1);
v_endExclusive_135_ = lean_ctor_get(v_s_132_, 2);
v___x_136_ = lean_nat_sub(v_endExclusive_135_, v_startInclusive_134_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_newStart_133_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_subsliceFrom___boxed(lean_object* v_s_138_, lean_object* v_newStart_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_String_Slice_subsliceFrom(v_s_138_, v_newStart_139_);
lean_dec_ref(v_s_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toSubslice(lean_object* v_s_141_){
_start:
{
lean_object* v_startInclusive_142_; lean_object* v_endExclusive_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_startInclusive_142_ = lean_ctor_get(v_s_141_, 1);
v_endExclusive_143_ = lean_ctor_get(v_s_141_, 2);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_nat_sub(v_endExclusive_143_, v_startInclusive_142_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toSubslice___boxed(lean_object* v_s_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_String_Slice_toSubslice(v_s_147_);
lean_dec_ref(v_s_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___redArg(lean_object* v_p_149_, lean_object* v_sl_150_){
_start:
{
lean_object* v_startInclusive_151_; lean_object* v_endExclusive_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_161_; 
v_startInclusive_151_ = lean_ctor_get(v_sl_150_, 0);
v_endExclusive_152_ = lean_ctor_get(v_sl_150_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_sl_150_);
if (v_isSharedCheck_161_ == 0)
{
v___x_154_ = v_sl_150_;
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_endExclusive_152_);
lean_inc(v_startInclusive_151_);
lean_dec(v_sl_150_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_156_ = lean_nat_add(v_p_149_, v_startInclusive_151_);
lean_dec(v_startInclusive_151_);
v___x_157_ = lean_nat_add(v_p_149_, v_endExclusive_152_);
lean_dec(v_endExclusive_152_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_157_);
lean_ctor_set(v___x_154_, 0, v___x_156_);
v___x_159_ = v___x_154_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___redArg___boxed(lean_object* v_p_162_, lean_object* v_sl_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_String_Slice_Subslice_ofSliceFrom___redArg(v_p_162_, v_sl_163_);
lean_dec(v_p_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom(lean_object* v_s_165_, lean_object* v_p_166_, lean_object* v_sl_167_){
_start:
{
lean_object* v_startInclusive_168_; lean_object* v_endExclusive_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_178_; 
v_startInclusive_168_ = lean_ctor_get(v_sl_167_, 0);
v_endExclusive_169_ = lean_ctor_get(v_sl_167_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_sl_167_);
if (v_isSharedCheck_178_ == 0)
{
v___x_171_ = v_sl_167_;
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_endExclusive_169_);
lean_inc(v_startInclusive_168_);
lean_dec(v_sl_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_nat_add(v_p_166_, v_startInclusive_168_);
lean_dec(v_startInclusive_168_);
v___x_174_ = lean_nat_add(v_p_166_, v_endExclusive_169_);
lean_dec(v_endExclusive_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_174_);
lean_ctor_set(v___x_171_, 0, v___x_173_);
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_ofSliceFrom___boxed(lean_object* v_s_179_, lean_object* v_p_180_, lean_object* v_sl_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_String_Slice_Subslice_ofSliceFrom(v_s_179_, v_p_180_, v_sl_181_);
lean_dec(v_p_180_);
lean_dec_ref(v_s_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft___redArg(lean_object* v_sl_183_, lean_object* v_newStart_184_){
_start:
{
lean_object* v_endExclusive_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_endExclusive_185_ = lean_ctor_get(v_sl_183_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_sl_183_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v_sl_183_, 0);
lean_dec(v_unused_193_);
v___x_187_ = v_sl_183_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_endExclusive_185_);
lean_dec(v_sl_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v_newStart_184_);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_newStart_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_endExclusive_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft(lean_object* v_s_194_, lean_object* v_sl_195_, lean_object* v_newStart_196_, lean_object* v_h_197_){
_start:
{
lean_object* v_endExclusive_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_endExclusive_198_ = lean_ctor_get(v_sl_195_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_sl_195_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_sl_195_, 0);
lean_dec(v_unused_206_);
v___x_200_ = v_sl_195_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_endExclusive_198_);
lean_dec(v_sl_195_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v_newStart_196_);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_newStart_196_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_endExclusive_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_extendLeft___boxed(lean_object* v_s_207_, lean_object* v_sl_208_, lean_object* v_newStart_209_, lean_object* v_h_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_String_Slice_Subslice_extendLeft(v_s_207_, v_sl_208_, v_newStart_209_, v_h_210_);
lean_dec_ref(v_s_207_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast___redArg(lean_object* v_sl_212_){
_start:
{
lean_object* v_startInclusive_213_; lean_object* v_endExclusive_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_startInclusive_213_ = lean_ctor_get(v_sl_212_, 0);
v_endExclusive_214_ = lean_ctor_get(v_sl_212_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_sl_212_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v_sl_212_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_endExclusive_214_);
lean_inc(v_startInclusive_213_);
lean_dec(v_sl_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_startInclusive_213_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_endExclusive_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast(lean_object* v_s_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_sl_225_){
_start:
{
lean_object* v_startInclusive_226_; lean_object* v_endExclusive_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_startInclusive_226_ = lean_ctor_get(v_sl_225_, 0);
v_endExclusive_227_ = lean_ctor_get(v_sl_225_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_sl_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v_sl_225_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_endExclusive_227_);
lean_inc(v_startInclusive_226_);
lean_dec(v_sl_225_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_startInclusive_226_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_endExclusive_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Subslice_cast___boxed(lean_object* v_s_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_sl_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_String_Slice_Subslice_cast(v_s_235_, v_t_236_, v_h_237_, v_sl_238_);
lean_dec_ref(v_t_236_);
lean_dec_ref(v_s_235_);
return v_res_239_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
