// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Div
// Imports: public import Init.Data.Float.Model.Unpacked.Round
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Float_Model_totalExponent(lean_object*, lean_object*);
lean_object* l_Float_Model_Format_targetExponent(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__1_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__2 = (const lean_object*)&l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__2_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_accuracyOfFraction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_accuracyOfFraction___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_divCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_divCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Float_Model_UnpackedFloat_div___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_div___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_div___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_div___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_div___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_div___closed__1_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_div(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_div___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_accuracyOfFraction(lean_object* v_num_7_, lean_object* v_den_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_nat_dec_eq(v_num_7_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_11_ = lean_unsigned_to_nat(2u);
v___x_12_ = lean_nat_mul(v___x_11_, v_num_7_);
v___x_13_ = lean_nat_dec_lt(v___x_12_, v_den_8_);
if (v___x_13_ == 0)
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v___x_12_, v_den_8_);
lean_dec(v___x_12_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__0));
return v___x_15_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = ((lean_object*)(l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__1));
return v___x_16_;
}
}
else
{
lean_object* v___x_17_; 
lean_dec(v___x_12_);
v___x_17_ = ((lean_object*)(l_Float_Model_UnpackedFloat_accuracyOfFraction___closed__2));
return v___x_17_;
}
}
else
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_accuracyOfFraction___boxed(lean_object* v_num_19_, lean_object* v_den_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Float_Model_UnpackedFloat_accuracyOfFraction(v_num_19_, v_den_20_);
lean_dec(v_den_20_);
lean_dec(v_num_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_divCore(lean_object* v_spec_22_, lean_object* v_m_u2081_23_, lean_object* v_e_u2081_24_, lean_object* v_m_u2082_25_, lean_object* v_e_u2082_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___y_29_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_27_ = lean_int_sub(v_e_u2081_24_, v_e_u2082_26_);
v___x_38_ = l_Float_Model_totalExponent(v_m_u2081_23_, v_e_u2081_24_);
v___x_39_ = l_Float_Model_totalExponent(v_m_u2082_25_, v_e_u2082_26_);
v___x_40_ = lean_int_sub(v___x_38_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v___x_38_);
v___x_41_ = l_Float_Model_Format_targetExponent(v_spec_22_, v___x_40_);
lean_dec(v___x_40_);
v___x_42_ = lean_int_dec_le(v___x_27_, v___x_41_);
if (v___x_42_ == 0)
{
v___y_29_ = v___x_41_;
goto v___jp_28_;
}
else
{
lean_dec(v___x_41_);
lean_inc(v___x_27_);
v___y_29_ = v___x_27_;
goto v___jp_28_;
}
v___jp_28_:
{
lean_object* v___x_30_; lean_object* v_shiftAmount_31_; lean_object* v_m_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_30_ = lean_int_sub(v___x_27_, v___y_29_);
lean_dec(v___x_27_);
v_shiftAmount_31_ = l_Int_toNat(v___x_30_);
lean_dec(v___x_30_);
v_m_32_ = lean_nat_shiftl(v_m_u2081_23_, v_shiftAmount_31_);
lean_dec(v_shiftAmount_31_);
v___x_33_ = lean_nat_div(v_m_32_, v_m_u2082_25_);
v___x_34_ = lean_nat_mod(v_m_32_, v_m_u2082_25_);
lean_dec(v_m_32_);
v___x_35_ = l_Float_Model_UnpackedFloat_accuracyOfFraction(v___x_34_, v_m_u2082_25_);
lean_dec(v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___y_29_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_33_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_divCore___boxed(lean_object* v_spec_43_, lean_object* v_m_u2081_44_, lean_object* v_e_u2081_45_, lean_object* v_m_u2082_46_, lean_object* v_e_u2082_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Float_Model_UnpackedFloat_divCore(v_spec_43_, v_m_u2081_44_, v_e_u2081_45_, v_m_u2082_46_, v_e_u2082_47_);
lean_dec(v_e_u2082_47_);
lean_dec(v_m_u2082_46_);
lean_dec(v_e_u2081_45_);
lean_dec(v_m_u2081_44_);
lean_dec_ref(v_spec_43_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_div(lean_object* v_spec_53_, lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
switch(lean_obj_tag(v_x_54_))
{
case 0:
{
switch(lean_obj_tag(v_x_55_))
{
case 0:
{
lean_object* v___x_56_; 
lean_dec_ref_known(v_x_55_, 0);
lean_dec_ref_known(v_x_54_, 0);
v___x_56_ = lean_box(1);
return v___x_56_;
}
case 1:
{
lean_dec_ref_known(v_x_54_, 0);
return v_x_55_;
}
case 2:
{
uint8_t v_sign_57_; 
v_sign_57_ = lean_ctor_get_uint8(v_x_54_, 0);
if (v_sign_57_ == 0)
{
uint8_t v_sign_58_; 
v_sign_58_ = lean_ctor_get_uint8(v_x_55_, 0);
lean_dec_ref_known(v_x_55_, 0);
if (v_sign_58_ == 0)
{
lean_object* v___x_59_; 
lean_dec_ref_known(v_x_54_, 0);
v___x_59_ = ((lean_object*)(l_Float_Model_UnpackedFloat_div___closed__0));
return v___x_59_;
}
else
{
return v_x_54_;
}
}
else
{
uint8_t v_sign_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_dec_ref_known(v_x_54_, 0);
v_sign_60_ = lean_ctor_get_uint8(v_x_55_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v_x_55_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_dec(v_x_55_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 0);
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, 0, v_sign_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
default: 
{
uint8_t v_sign_68_; 
v_sign_68_ = lean_ctor_get_uint8(v_x_54_, 0);
if (v_sign_68_ == 0)
{
uint8_t v_sign_69_; 
v_sign_69_ = lean_ctor_get_uint8(v_x_55_, sizeof(void*)*2);
lean_dec_ref_known(v_x_55_, 2);
if (v_sign_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec_ref_known(v_x_54_, 0);
v___x_70_ = ((lean_object*)(l_Float_Model_UnpackedFloat_div___closed__0));
return v___x_70_;
}
else
{
return v_x_54_;
}
}
else
{
lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v_isSharedCheck_78_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_78_ == 0)
{
v___x_72_ = v_x_54_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_dec(v_x_54_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
uint8_t v_sign_74_; lean_object* v___x_76_; 
v_sign_74_ = lean_ctor_get_uint8(v_x_55_, sizeof(void*)*2);
lean_dec_ref_known(v_x_55_, 2);
if (v_isShared_73_ == 0)
{
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 0, 1);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_ctor_set_uint8(v___x_76_, 0, v_sign_74_);
return v___x_76_;
}
}
}
}
}
}
case 1:
{
lean_dec(v_x_55_);
return v_x_54_;
}
case 2:
{
switch(lean_obj_tag(v_x_55_))
{
case 0:
{
uint8_t v_sign_79_; 
v_sign_79_ = lean_ctor_get_uint8(v_x_54_, 0);
if (v_sign_79_ == 0)
{
uint8_t v_sign_80_; 
v_sign_80_ = lean_ctor_get_uint8(v_x_55_, 0);
lean_dec_ref_known(v_x_55_, 0);
if (v_sign_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec_ref_known(v_x_54_, 0);
v___x_81_ = ((lean_object*)(l_Float_Model_UnpackedFloat_div___closed__1));
return v___x_81_;
}
else
{
return v_x_54_;
}
}
else
{
uint8_t v_sign_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec_ref_known(v_x_54_, 0);
v_sign_82_ = lean_ctor_get_uint8(v_x_55_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v_x_55_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_dec(v_x_55_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 2);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, 0, v_sign_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_x_54_, 0);
return v_x_55_;
}
case 2:
{
lean_object* v___x_90_; 
lean_dec_ref_known(v_x_55_, 0);
lean_dec_ref_known(v_x_54_, 0);
v___x_90_ = lean_box(1);
return v___x_90_;
}
default: 
{
uint8_t v_sign_91_; 
v_sign_91_ = lean_ctor_get_uint8(v_x_54_, 0);
if (v_sign_91_ == 0)
{
uint8_t v_sign_92_; 
v_sign_92_ = lean_ctor_get_uint8(v_x_55_, sizeof(void*)*2);
lean_dec_ref_known(v_x_55_, 2);
if (v_sign_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref_known(v_x_54_, 0);
v___x_93_ = ((lean_object*)(l_Float_Model_UnpackedFloat_div___closed__1));
return v___x_93_;
}
else
{
return v_x_54_;
}
}
else
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_101_; 
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_101_ == 0)
{
v___x_95_ = v_x_54_;
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
else
{
lean_dec(v_x_54_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
uint8_t v_sign_97_; lean_object* v___x_99_; 
v_sign_97_ = lean_ctor_get_uint8(v_x_55_, sizeof(void*)*2);
lean_dec_ref_known(v_x_55_, 2);
if (v_isShared_96_ == 0)
{
v___x_99_ = v___x_95_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(2, 0, 1);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_ctor_set_uint8(v___x_99_, 0, v_sign_97_);
return v___x_99_;
}
}
}
}
}
}
default: 
{
switch(lean_obj_tag(v_x_55_))
{
case 0:
{
uint8_t v_sign_102_; 
v_sign_102_ = lean_ctor_get_uint8(v_x_54_, sizeof(void*)*2);
lean_dec_ref_known(v_x_54_, 2);
if (v_sign_102_ == 0)
{
uint8_t v_sign_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
v_sign_103_ = lean_ctor_get_uint8(v_x_55_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_111_ == 0)
{
v___x_105_ = v_x_55_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_dec(v_x_55_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
if (v_sign_103_ == 0)
{
lean_object* v___x_107_; 
lean_del_object(v___x_105_);
v___x_107_ = ((lean_object*)(l_Float_Model_UnpackedFloat_div___closed__1));
return v___x_107_;
}
else
{
lean_object* v___x_109_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 2);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(2, 0, 1);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_ctor_set_uint8(v___x_109_, 0, v_sign_102_);
return v___x_109_;
}
}
}
}
else
{
uint8_t v_sign_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_sign_112_ = lean_ctor_get_uint8(v_x_55_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v_x_55_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_dec(v_x_55_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 2);
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_118_, 0, v_sign_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_x_54_, 2);
return v_x_55_;
}
case 2:
{
uint8_t v_sign_120_; 
v_sign_120_ = lean_ctor_get_uint8(v_x_54_, sizeof(void*)*2);
lean_dec_ref_known(v_x_54_, 2);
if (v_sign_120_ == 0)
{
uint8_t v_sign_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_sign_121_ = lean_ctor_get_uint8(v_x_55_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v_x_55_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_dec(v_x_55_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
if (v_sign_121_ == 0)
{
lean_object* v___x_125_; 
lean_del_object(v___x_123_);
v___x_125_ = ((lean_object*)(l_Float_Model_UnpackedFloat_div___closed__0));
return v___x_125_;
}
else
{
lean_object* v___x_127_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 0);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 0, 1);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_ctor_set_uint8(v___x_127_, 0, v_sign_120_);
return v___x_127_;
}
}
}
}
else
{
uint8_t v_sign_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_sign_130_ = lean_ctor_get_uint8(v_x_55_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v_x_55_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_dec(v_x_55_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set_tag(v___x_132_, 0);
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_136_, 0, v_sign_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
default: 
{
uint8_t v_sign_138_; lean_object* v_mantissa_139_; lean_object* v_exponent_140_; uint8_t v_sign_141_; lean_object* v_mantissa_142_; lean_object* v_exponent_143_; lean_object* v___x_144_; lean_object* v_snd_145_; 
v_sign_138_ = lean_ctor_get_uint8(v_x_54_, sizeof(void*)*2);
v_mantissa_139_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_mantissa_139_);
v_exponent_140_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_exponent_140_);
lean_dec_ref_known(v_x_54_, 2);
v_sign_141_ = lean_ctor_get_uint8(v_x_55_, sizeof(void*)*2);
v_mantissa_142_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_mantissa_142_);
v_exponent_143_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_exponent_143_);
lean_dec_ref_known(v_x_55_, 2);
v___x_144_ = l_Float_Model_UnpackedFloat_divCore(v_spec_53_, v_mantissa_139_, v_exponent_140_, v_mantissa_142_, v_exponent_143_);
lean_dec(v_exponent_143_);
lean_dec(v_mantissa_142_);
lean_dec(v_exponent_140_);
lean_dec(v_mantissa_139_);
v_snd_145_ = lean_ctor_get(v___x_144_, 1);
lean_inc(v_snd_145_);
if (v_sign_138_ == 0)
{
if (v_sign_141_ == 0)
{
lean_object* v_fst_146_; lean_object* v_fst_147_; lean_object* v_snd_148_; uint8_t v___x_149_; lean_object* v___x_150_; 
v_fst_146_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_fst_146_);
lean_dec_ref(v___x_144_);
v_fst_147_ = lean_ctor_get(v_snd_145_, 0);
lean_inc(v_fst_147_);
v_snd_148_ = lean_ctor_get(v_snd_145_, 1);
lean_inc(v_snd_148_);
lean_dec(v_snd_145_);
v___x_149_ = 1;
v___x_150_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_53_, v___x_149_, v_fst_146_, v_fst_147_, v_snd_148_);
lean_dec(v_snd_148_);
lean_dec(v_fst_147_);
return v___x_150_;
}
else
{
lean_object* v_fst_151_; lean_object* v_fst_152_; lean_object* v_snd_153_; lean_object* v___x_154_; 
v_fst_151_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_fst_151_);
lean_dec_ref(v___x_144_);
v_fst_152_ = lean_ctor_get(v_snd_145_, 0);
lean_inc(v_fst_152_);
v_snd_153_ = lean_ctor_get(v_snd_145_, 1);
lean_inc(v_snd_153_);
lean_dec(v_snd_145_);
v___x_154_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_53_, v_sign_138_, v_fst_151_, v_fst_152_, v_snd_153_);
lean_dec(v_snd_153_);
lean_dec(v_fst_152_);
return v___x_154_;
}
}
else
{
lean_object* v_fst_155_; lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v___x_158_; 
v_fst_155_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_fst_155_);
lean_dec_ref(v___x_144_);
v_fst_156_ = lean_ctor_get(v_snd_145_, 0);
lean_inc(v_fst_156_);
v_snd_157_ = lean_ctor_get(v_snd_145_, 1);
lean_inc(v_snd_157_);
lean_dec(v_snd_145_);
v___x_158_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_53_, v_sign_141_, v_fst_155_, v_fst_156_, v_snd_157_);
lean_dec(v_snd_157_);
lean_dec(v_fst_156_);
return v___x_158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_div___boxed(lean_object* v_spec_159_, lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Float_Model_UnpackedFloat_div(v_spec_159_, v_x_160_, v_x_161_);
lean_dec_ref(v_spec_159_);
return v_res_162_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Div(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Div(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Div(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Div(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Div(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Div(builtin);
}
#ifdef __cplusplus
}
#endif
