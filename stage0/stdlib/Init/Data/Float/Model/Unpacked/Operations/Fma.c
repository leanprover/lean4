// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Fma
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_normalize(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Float_Model_UnpackedFloat_decreaseExponent(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_fma_spec__0(lean_object*);
static const lean_ctor_object l_Float_Model_UnpackedFloat_fma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_fma___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_fma___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_fma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_fma___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_fma___closed__1_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_fma(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_fma___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_fma_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_fma(lean_object* v_spec_7_, lean_object* v_x_8_, lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
switch(lean_obj_tag(v_x_8_))
{
case 0:
{
switch(lean_obj_tag(v_x_9_))
{
case 0:
{
switch(lean_obj_tag(v_x_10_))
{
case 1:
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
case 0:
{
uint8_t v_sign_11_; uint8_t v_sign_12_; uint8_t v_sign_13_; uint8_t v___y_15_; 
v_sign_11_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_12_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_13_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_11_ == 0)
{
if (v_sign_12_ == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 1;
v___y_15_ = v___x_22_;
goto v___jp_14_;
}
else
{
v___y_15_ = v_sign_11_;
goto v___jp_14_;
}
}
else
{
v___y_15_ = v_sign_12_;
goto v___jp_14_;
}
v___jp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_16_ = lean_box(v___y_15_);
v___x_17_ = lean_obj_tag_nat(v___x_16_);
lean_dec(v___x_16_);
v___x_18_ = lean_box(v_sign_13_);
v___x_19_ = lean_obj_tag_nat(v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_nat_dec_eq(v___x_17_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_21_ = lean_box(1);
return v___x_21_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_23_; 
lean_dec(v_x_10_);
v_sign_23_ = lean_ctor_get_uint8(v_x_8_, 0);
if (v_sign_23_ == 0)
{
uint8_t v_sign_24_; 
v_sign_24_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
if (v_sign_24_ == 0)
{
lean_object* v___x_25_; 
lean_dec_ref_known(v_x_8_, 0);
v___x_25_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_25_;
}
else
{
return v_x_8_;
}
}
else
{
lean_dec_ref_known(v_x_8_, 0);
return v_x_9_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_x_8_, 0);
lean_dec(v_x_10_);
return v_x_9_;
}
case 2:
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 0);
if (lean_obj_tag(v_x_10_) == 1)
{
return v_x_10_;
}
else
{
lean_object* v___x_26_; 
lean_dec(v_x_10_);
v___x_26_ = lean_box(1);
return v___x_26_;
}
}
default: 
{
switch(lean_obj_tag(v_x_10_))
{
case 1:
{
lean_dec_ref_known(v_x_9_, 2);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
case 0:
{
uint8_t v_sign_27_; uint8_t v_sign_28_; uint8_t v_sign_29_; uint8_t v___y_31_; 
v_sign_27_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_28_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
v_sign_29_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_27_ == 0)
{
if (v_sign_28_ == 0)
{
uint8_t v___x_38_; 
v___x_38_ = 1;
v___y_31_ = v___x_38_;
goto v___jp_30_;
}
else
{
v___y_31_ = v_sign_27_;
goto v___jp_30_;
}
}
else
{
v___y_31_ = v_sign_28_;
goto v___jp_30_;
}
v___jp_30_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_32_ = lean_box(v___y_31_);
v___x_33_ = lean_obj_tag_nat(v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = lean_box(v_sign_29_);
v___x_35_ = lean_obj_tag_nat(v___x_34_);
lean_dec(v___x_34_);
v___x_36_ = lean_nat_dec_eq(v___x_33_, v___x_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_37_ = lean_box(1);
return v___x_37_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_39_; 
lean_dec(v_x_10_);
v_sign_39_ = lean_ctor_get_uint8(v_x_8_, 0);
if (v_sign_39_ == 0)
{
uint8_t v_sign_40_; 
v_sign_40_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
if (v_sign_40_ == 0)
{
lean_object* v___x_41_; 
lean_dec_ref_known(v_x_8_, 0);
v___x_41_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_41_;
}
else
{
return v_x_8_;
}
}
else
{
lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_49_; 
v_isSharedCheck_49_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_49_ == 0)
{
v___x_43_ = v_x_8_;
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
else
{
lean_dec(v_x_8_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
uint8_t v_sign_45_; lean_object* v___x_47_; 
v_sign_45_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
if (v_isShared_44_ == 0)
{
v___x_47_ = v___x_43_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 0, 1);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_ctor_set_uint8(v___x_47_, 0, v_sign_45_);
return v___x_47_;
}
}
}
}
}
}
}
}
case 1:
{
lean_dec(v_x_10_);
lean_dec(v_x_9_);
return v_x_8_;
}
case 2:
{
switch(lean_obj_tag(v_x_9_))
{
case 0:
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 0);
if (lean_obj_tag(v_x_10_) == 1)
{
return v_x_10_;
}
else
{
lean_object* v___x_50_; 
lean_dec(v_x_10_);
v___x_50_ = lean_box(1);
return v___x_50_;
}
}
case 1:
{
lean_dec_ref_known(v_x_8_, 0);
lean_dec(v_x_10_);
return v_x_9_;
}
case 2:
{
if (lean_obj_tag(v_x_10_) == 2)
{
uint8_t v_sign_51_; uint8_t v_sign_52_; uint8_t v_sign_53_; uint8_t v___y_55_; 
v_sign_51_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_52_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_53_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_51_ == 0)
{
if (v_sign_52_ == 0)
{
uint8_t v___x_62_; 
v___x_62_ = 1;
v___y_55_ = v___x_62_;
goto v___jp_54_;
}
else
{
v___y_55_ = v_sign_51_;
goto v___jp_54_;
}
}
else
{
v___y_55_ = v_sign_52_;
goto v___jp_54_;
}
v___jp_54_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_56_ = lean_box(v___y_55_);
v___x_57_ = lean_obj_tag_nat(v___x_56_);
lean_dec(v___x_56_);
v___x_58_ = lean_box(v_sign_53_);
v___x_59_ = lean_obj_tag_nat(v___x_58_);
lean_dec(v___x_58_);
v___x_60_ = lean_nat_dec_eq(v___x_57_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_61_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_61_;
}
else
{
return v_x_10_;
}
}
}
else
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
}
default: 
{
if (lean_obj_tag(v_x_10_) == 2)
{
uint8_t v_sign_63_; uint8_t v_sign_64_; uint8_t v_sign_65_; uint8_t v___y_67_; 
v_sign_63_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_64_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
v_sign_65_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_63_ == 0)
{
if (v_sign_64_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 1;
v___y_67_ = v___x_74_;
goto v___jp_66_;
}
else
{
v___y_67_ = v_sign_63_;
goto v___jp_66_;
}
}
else
{
v___y_67_ = v_sign_64_;
goto v___jp_66_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_68_ = lean_box(v___y_67_);
v___x_69_ = lean_obj_tag_nat(v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = lean_box(v_sign_65_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_dec_eq(v___x_69_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_73_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_73_;
}
else
{
return v_x_10_;
}
}
}
else
{
lean_dec_ref_known(v_x_9_, 2);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
}
}
}
default: 
{
switch(lean_obj_tag(v_x_9_))
{
case 0:
{
switch(lean_obj_tag(v_x_10_))
{
case 1:
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 2);
return v_x_10_;
}
case 0:
{
uint8_t v_sign_75_; uint8_t v_sign_76_; uint8_t v_sign_77_; uint8_t v___y_79_; 
v_sign_75_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
v_sign_76_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_77_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_75_ == 0)
{
if (v_sign_76_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 1;
v___y_79_ = v___x_86_;
goto v___jp_78_;
}
else
{
v___y_79_ = v_sign_75_;
goto v___jp_78_;
}
}
else
{
v___y_79_ = v_sign_76_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_80_ = lean_box(v___y_79_);
v___x_81_ = lean_obj_tag_nat(v___x_80_);
lean_dec(v___x_80_);
v___x_82_ = lean_box(v_sign_77_);
v___x_83_ = lean_obj_tag_nat(v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = lean_nat_dec_eq(v___x_81_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_85_ = lean_box(1);
return v___x_85_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_87_; 
lean_dec(v_x_10_);
v_sign_87_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
if (v_sign_87_ == 0)
{
uint8_t v_sign_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_sign_88_ = lean_ctor_get_uint8(v_x_9_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v_x_9_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_dec(v_x_9_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
if (v_sign_88_ == 0)
{
lean_object* v___x_92_; 
lean_del_object(v___x_90_);
v___x_92_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_92_;
}
else
{
lean_object* v___x_94_; 
if (v_isShared_91_ == 0)
{
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 0, 1);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_ctor_set_uint8(v___x_94_, 0, v_sign_87_);
return v___x_94_;
}
}
}
}
else
{
return v_x_9_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_x_8_, 2);
lean_dec(v_x_10_);
return v_x_9_;
}
case 2:
{
if (lean_obj_tag(v_x_10_) == 2)
{
uint8_t v_sign_97_; uint8_t v_sign_98_; uint8_t v_sign_99_; uint8_t v___y_101_; 
v_sign_97_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
v_sign_98_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_99_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_97_ == 0)
{
if (v_sign_98_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 1;
v___y_101_ = v___x_108_;
goto v___jp_100_;
}
else
{
v___y_101_ = v_sign_97_;
goto v___jp_100_;
}
}
else
{
v___y_101_ = v_sign_98_;
goto v___jp_100_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_102_ = lean_box(v___y_101_);
v___x_103_ = lean_obj_tag_nat(v___x_102_);
lean_dec(v___x_102_);
v___x_104_ = lean_box(v_sign_99_);
v___x_105_ = lean_obj_tag_nat(v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_nat_dec_eq(v___x_103_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_107_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_107_;
}
else
{
return v_x_10_;
}
}
}
else
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 2);
return v_x_10_;
}
}
default: 
{
uint8_t v_sign_109_; lean_object* v_mantissa_110_; lean_object* v_exponent_111_; uint8_t v_sign_112_; lean_object* v_mantissa_113_; lean_object* v_exponent_114_; uint8_t v___y_116_; 
v_sign_109_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
v_mantissa_110_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_mantissa_110_);
v_exponent_111_ = lean_ctor_get(v_x_8_, 1);
lean_inc(v_exponent_111_);
lean_dec_ref_known(v_x_8_, 2);
v_sign_112_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
v_mantissa_113_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_mantissa_113_);
v_exponent_114_ = lean_ctor_get(v_x_9_, 1);
lean_inc(v_exponent_114_);
lean_dec_ref_known(v_x_9_, 2);
switch(lean_obj_tag(v_x_10_))
{
case 2:
{
lean_dec_ref_known(v_x_10_, 0);
if (v_sign_109_ == 0)
{
if (v_sign_112_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 1;
v___y_116_ = v___x_121_;
goto v___jp_115_;
}
else
{
v___y_116_ = v_sign_109_;
goto v___jp_115_;
}
}
else
{
v___y_116_ = v_sign_112_;
goto v___jp_115_;
}
}
case 3:
{
uint8_t v_sign_122_; lean_object* v_mantissa_123_; lean_object* v_exponent_124_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; uint8_t v___y_129_; lean_object* v_productMantissa_137_; lean_object* v_productExponent_138_; lean_object* v___y_140_; uint8_t v___x_148_; 
v_sign_122_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_123_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_mantissa_123_);
v_exponent_124_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_exponent_124_);
lean_dec_ref_known(v_x_10_, 2);
v_productMantissa_137_ = lean_nat_mul(v_mantissa_110_, v_mantissa_113_);
lean_dec(v_mantissa_113_);
lean_dec(v_mantissa_110_);
v_productExponent_138_ = lean_int_add(v_exponent_111_, v_exponent_114_);
lean_dec(v_exponent_114_);
lean_dec(v_exponent_111_);
v___x_148_ = lean_int_dec_le(v_productExponent_138_, v_exponent_124_);
if (v___x_148_ == 0)
{
lean_inc(v_exponent_124_);
v___y_140_ = v_exponent_124_;
goto v___jp_139_;
}
else
{
lean_inc(v_productExponent_138_);
v___y_140_ = v_productExponent_138_;
goto v___jp_139_;
}
v___jp_125_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_mantissa_134_; uint8_t v___x_135_; lean_object* v___x_136_; 
v___x_130_ = lean_nat_to_int(v___y_128_);
v___x_131_ = l_Float_Model_UnpackedFloat_Sign_apply(v___y_129_, v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_nat_to_int(v___y_126_);
v___x_133_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_122_, v___x_132_);
lean_dec(v___x_132_);
v_mantissa_134_ = lean_int_add(v___x_131_, v___x_133_);
lean_dec(v___x_133_);
lean_dec(v___x_131_);
v___x_135_ = 1;
v___x_136_ = l_Float_Model_UnpackedFloat_normalize(v_spec_7_, v_mantissa_134_, v___y_127_, v___x_135_);
lean_dec(v___y_127_);
lean_dec(v_mantissa_134_);
return v___x_136_;
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v_fst_142_; lean_object* v___x_143_; 
v___x_141_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_productMantissa_137_, v_productExponent_138_, v___y_140_);
lean_dec(v_productExponent_138_);
lean_dec(v_productMantissa_137_);
v_fst_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_fst_142_);
lean_dec_ref(v___x_141_);
v___x_143_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_123_, v_exponent_124_, v___y_140_);
lean_dec(v_exponent_124_);
lean_dec(v_mantissa_123_);
if (v_sign_109_ == 0)
{
if (v_sign_112_ == 0)
{
lean_object* v_fst_144_; uint8_t v___x_145_; 
v_fst_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_fst_144_);
lean_dec_ref(v___x_143_);
v___x_145_ = 1;
v___y_126_ = v_fst_144_;
v___y_127_ = v___y_140_;
v___y_128_ = v_fst_142_;
v___y_129_ = v___x_145_;
goto v___jp_125_;
}
else
{
lean_object* v_fst_146_; 
v_fst_146_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_fst_146_);
lean_dec_ref(v___x_143_);
v___y_126_ = v_fst_146_;
v___y_127_ = v___y_140_;
v___y_128_ = v_fst_142_;
v___y_129_ = v_sign_109_;
goto v___jp_125_;
}
}
else
{
lean_object* v_fst_147_; 
v_fst_147_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_fst_147_);
lean_dec_ref(v___x_143_);
v___y_126_ = v_fst_147_;
v___y_127_ = v___y_140_;
v___y_128_ = v_fst_142_;
v___y_129_ = v_sign_112_;
goto v___jp_125_;
}
}
}
default: 
{
lean_dec(v_exponent_114_);
lean_dec(v_mantissa_113_);
lean_dec(v_exponent_111_);
lean_dec(v_mantissa_110_);
return v_x_10_;
}
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = lean_nat_mul(v_mantissa_110_, v_mantissa_113_);
lean_dec(v_mantissa_113_);
lean_dec(v_mantissa_110_);
v___x_118_ = lean_int_add(v_exponent_111_, v_exponent_114_);
lean_dec(v_exponent_114_);
lean_dec(v_exponent_111_);
v___x_119_ = lean_box(0);
v___x_120_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_7_, v___y_116_, v___x_117_, v___x_118_, v___x_119_);
lean_dec(v___x_118_);
return v___x_120_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_fma___boxed(lean_object* v_spec_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Float_Model_UnpackedFloat_fma(v_spec_149_, v_x_150_, v_x_151_, v_x_152_);
lean_dec_ref(v_spec_149_);
return v_res_153_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Fma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Fma(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Fma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Fma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Fma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Fma(builtin);
}
#ifdef __cplusplus
}
#endif
