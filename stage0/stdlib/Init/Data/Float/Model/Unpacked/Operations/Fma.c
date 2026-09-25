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
lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx(uint8_t);
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
uint8_t v___x_20_; 
v___x_20_ = 1;
v___y_15_ = v___x_20_;
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
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_16_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_15_);
v___x_17_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_13_);
v___x_18_ = lean_nat_dec_eq(v___x_16_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_16_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_19_ = lean_box(1);
return v___x_19_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_21_; 
lean_dec(v_x_10_);
v_sign_21_ = lean_ctor_get_uint8(v_x_8_, 0);
if (v_sign_21_ == 0)
{
uint8_t v_sign_22_; 
v_sign_22_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
if (v_sign_22_ == 0)
{
lean_object* v___x_23_; 
lean_dec_ref_known(v_x_8_, 0);
v___x_23_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_23_;
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
switch(lean_obj_tag(v_x_10_))
{
case 1:
{
return v_x_10_;
}
case 0:
{
lean_object* v___x_24_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_24_ = lean_box(1);
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; 
lean_dec(v_x_10_);
v___x_25_ = lean_box(1);
return v___x_25_;
}
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
uint8_t v_sign_26_; uint8_t v_sign_27_; uint8_t v_sign_28_; uint8_t v___y_30_; 
v_sign_26_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_27_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
v_sign_28_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_26_ == 0)
{
if (v_sign_27_ == 0)
{
uint8_t v___x_35_; 
v___x_35_ = 1;
v___y_30_ = v___x_35_;
goto v___jp_29_;
}
else
{
v___y_30_ = v_sign_26_;
goto v___jp_29_;
}
}
else
{
v___y_30_ = v_sign_27_;
goto v___jp_29_;
}
v___jp_29_:
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_30_);
v___x_32_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_28_);
v___x_33_ = lean_nat_dec_eq(v___x_31_, v___x_32_);
lean_dec(v___x_32_);
lean_dec(v___x_31_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_34_ = lean_box(1);
return v___x_34_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_36_; 
lean_dec(v_x_10_);
v_sign_36_ = lean_ctor_get_uint8(v_x_8_, 0);
if (v_sign_36_ == 0)
{
uint8_t v_sign_37_; 
v_sign_37_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
if (v_sign_37_ == 0)
{
lean_object* v___x_38_; 
lean_dec_ref_known(v_x_8_, 0);
v___x_38_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_38_;
}
else
{
return v_x_8_;
}
}
else
{
lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_46_; 
v_isSharedCheck_46_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_46_ == 0)
{
v___x_40_ = v_x_8_;
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
else
{
lean_dec(v_x_8_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
uint8_t v_sign_42_; lean_object* v___x_44_; 
v_sign_42_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
if (v_isShared_41_ == 0)
{
v___x_44_ = v___x_40_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 0, 1);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_ctor_set_uint8(v___x_44_, 0, v_sign_42_);
return v___x_44_;
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
switch(lean_obj_tag(v_x_10_))
{
case 1:
{
return v_x_10_;
}
case 0:
{
lean_object* v___x_47_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_47_ = lean_box(1);
return v___x_47_;
}
default: 
{
lean_object* v___x_48_; 
lean_dec(v_x_10_);
v___x_48_ = lean_box(1);
return v___x_48_;
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
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
case 2:
{
uint8_t v_sign_49_; uint8_t v_sign_50_; uint8_t v_sign_51_; uint8_t v___y_53_; 
v_sign_49_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_50_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_51_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_49_ == 0)
{
if (v_sign_50_ == 0)
{
uint8_t v___x_58_; 
v___x_58_ = 1;
v___y_53_ = v___x_58_;
goto v___jp_52_;
}
else
{
v___y_53_ = v_sign_49_;
goto v___jp_52_;
}
}
else
{
v___y_53_ = v_sign_50_;
goto v___jp_52_;
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_54_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_53_);
v___x_55_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_51_);
v___x_56_ = lean_nat_dec_eq(v___x_54_, v___x_55_);
lean_dec(v___x_55_);
lean_dec(v___x_54_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_57_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_57_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
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
lean_dec_ref_known(v_x_9_, 2);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
case 2:
{
uint8_t v_sign_59_; uint8_t v_sign_60_; uint8_t v_sign_61_; uint8_t v___y_63_; 
v_sign_59_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_60_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
v_sign_61_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_59_ == 0)
{
if (v_sign_60_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 1;
v___y_63_ = v___x_68_;
goto v___jp_62_;
}
else
{
v___y_63_ = v_sign_59_;
goto v___jp_62_;
}
}
else
{
v___y_63_ = v_sign_60_;
goto v___jp_62_;
}
v___jp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_63_);
v___x_65_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_61_);
v___x_66_ = lean_nat_dec_eq(v___x_64_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_64_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_67_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_67_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
lean_dec_ref_known(v_x_9_, 2);
lean_dec_ref_known(v_x_8_, 0);
return v_x_10_;
}
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
uint8_t v_sign_69_; uint8_t v_sign_70_; uint8_t v_sign_71_; uint8_t v___y_73_; 
v_sign_69_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
v_sign_70_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_71_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_69_ == 0)
{
if (v_sign_70_ == 0)
{
uint8_t v___x_78_; 
v___x_78_ = 1;
v___y_73_ = v___x_78_;
goto v___jp_72_;
}
else
{
v___y_73_ = v_sign_69_;
goto v___jp_72_;
}
}
else
{
v___y_73_ = v_sign_70_;
goto v___jp_72_;
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_73_);
v___x_75_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_71_);
v___x_76_ = lean_nat_dec_eq(v___x_74_, v___x_75_);
lean_dec(v___x_75_);
lean_dec(v___x_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_77_ = lean_box(1);
return v___x_77_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_79_; 
lean_dec(v_x_10_);
v_sign_79_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
if (v_sign_79_ == 0)
{
uint8_t v_sign_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_88_; 
v_sign_80_ = lean_ctor_get_uint8(v_x_9_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_88_ == 0)
{
v___x_82_ = v_x_9_;
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_x_9_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
if (v_sign_80_ == 0)
{
lean_object* v___x_84_; 
lean_del_object(v___x_82_);
v___x_84_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_84_;
}
else
{
lean_object* v___x_86_; 
if (v_isShared_83_ == 0)
{
v___x_86_ = v___x_82_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 0, 1);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_ctor_set_uint8(v___x_86_, 0, v_sign_79_);
return v___x_86_;
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
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 2);
return v_x_10_;
}
case 2:
{
uint8_t v_sign_89_; uint8_t v_sign_90_; uint8_t v_sign_91_; uint8_t v___y_93_; 
v_sign_89_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
v_sign_90_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_91_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_89_ == 0)
{
if (v_sign_90_ == 0)
{
uint8_t v___x_98_; 
v___x_98_ = 1;
v___y_93_ = v___x_98_;
goto v___jp_92_;
}
else
{
v___y_93_ = v_sign_89_;
goto v___jp_92_;
}
}
else
{
v___y_93_ = v_sign_90_;
goto v___jp_92_;
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_94_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_93_);
v___x_95_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_91_);
v___x_96_ = lean_nat_dec_eq(v___x_94_, v___x_95_);
lean_dec(v___x_95_);
lean_dec(v___x_94_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_97_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_97_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
lean_dec_ref_known(v_x_9_, 0);
lean_dec_ref_known(v_x_8_, 2);
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_99_; lean_object* v_mantissa_100_; lean_object* v_exponent_101_; uint8_t v_sign_102_; lean_object* v_mantissa_103_; lean_object* v_exponent_104_; uint8_t v___y_106_; 
v_sign_99_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
v_mantissa_100_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_mantissa_100_);
v_exponent_101_ = lean_ctor_get(v_x_8_, 1);
lean_inc(v_exponent_101_);
lean_dec_ref_known(v_x_8_, 2);
v_sign_102_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
v_mantissa_103_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_mantissa_103_);
v_exponent_104_ = lean_ctor_get(v_x_9_, 1);
lean_inc(v_exponent_104_);
lean_dec_ref_known(v_x_9_, 2);
switch(lean_obj_tag(v_x_10_))
{
case 2:
{
lean_dec_ref_known(v_x_10_, 0);
if (v_sign_99_ == 0)
{
if (v_sign_102_ == 0)
{
uint8_t v___x_111_; 
v___x_111_ = 1;
v___y_106_ = v___x_111_;
goto v___jp_105_;
}
else
{
v___y_106_ = v_sign_99_;
goto v___jp_105_;
}
}
else
{
v___y_106_ = v_sign_102_;
goto v___jp_105_;
}
}
case 3:
{
uint8_t v_sign_112_; lean_object* v_mantissa_113_; lean_object* v_exponent_114_; lean_object* v___y_116_; lean_object* v___y_117_; lean_object* v___y_118_; uint8_t v___y_119_; lean_object* v_productMantissa_127_; lean_object* v_productExponent_128_; lean_object* v___y_130_; uint8_t v___x_138_; 
v_sign_112_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_113_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_mantissa_113_);
v_exponent_114_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_exponent_114_);
lean_dec_ref_known(v_x_10_, 2);
v_productMantissa_127_ = lean_nat_mul(v_mantissa_100_, v_mantissa_103_);
lean_dec(v_mantissa_103_);
lean_dec(v_mantissa_100_);
v_productExponent_128_ = lean_int_add(v_exponent_101_, v_exponent_104_);
lean_dec(v_exponent_104_);
lean_dec(v_exponent_101_);
v___x_138_ = lean_int_dec_le(v_productExponent_128_, v_exponent_114_);
if (v___x_138_ == 0)
{
lean_inc(v_exponent_114_);
v___y_130_ = v_exponent_114_;
goto v___jp_129_;
}
else
{
lean_inc(v_productExponent_128_);
v___y_130_ = v_productExponent_128_;
goto v___jp_129_;
}
v___jp_115_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_mantissa_124_; uint8_t v___x_125_; lean_object* v___x_126_; 
v___x_120_ = lean_nat_to_int(v___y_118_);
v___x_121_ = l_Float_Model_UnpackedFloat_Sign_apply(v___y_119_, v___x_120_);
lean_dec(v___x_120_);
v___x_122_ = lean_nat_to_int(v___y_117_);
v___x_123_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_112_, v___x_122_);
lean_dec(v___x_122_);
v_mantissa_124_ = lean_int_add(v___x_121_, v___x_123_);
lean_dec(v___x_123_);
lean_dec(v___x_121_);
v___x_125_ = 1;
v___x_126_ = l_Float_Model_UnpackedFloat_normalize(v_spec_7_, v_mantissa_124_, v___y_116_, v___x_125_);
lean_dec(v___y_116_);
lean_dec(v_mantissa_124_);
return v___x_126_;
}
v___jp_129_:
{
lean_object* v___x_131_; lean_object* v_fst_132_; lean_object* v___x_133_; 
v___x_131_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_productMantissa_127_, v_productExponent_128_, v___y_130_);
lean_dec(v_productExponent_128_);
lean_dec(v_productMantissa_127_);
v_fst_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v___x_131_);
v___x_133_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_113_, v_exponent_114_, v___y_130_);
lean_dec(v_exponent_114_);
lean_dec(v_mantissa_113_);
if (v_sign_99_ == 0)
{
if (v_sign_102_ == 0)
{
lean_object* v_fst_134_; uint8_t v___x_135_; 
v_fst_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_fst_134_);
lean_dec_ref(v___x_133_);
v___x_135_ = 1;
v___y_116_ = v___y_130_;
v___y_117_ = v_fst_134_;
v___y_118_ = v_fst_132_;
v___y_119_ = v___x_135_;
goto v___jp_115_;
}
else
{
lean_object* v_fst_136_; 
v_fst_136_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_fst_136_);
lean_dec_ref(v___x_133_);
v___y_116_ = v___y_130_;
v___y_117_ = v_fst_136_;
v___y_118_ = v_fst_132_;
v___y_119_ = v_sign_99_;
goto v___jp_115_;
}
}
else
{
lean_object* v_fst_137_; 
v_fst_137_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_fst_137_);
lean_dec_ref(v___x_133_);
v___y_116_ = v___y_130_;
v___y_117_ = v_fst_137_;
v___y_118_ = v_fst_132_;
v___y_119_ = v_sign_102_;
goto v___jp_115_;
}
}
}
default: 
{
lean_dec(v_exponent_104_);
lean_dec(v_mantissa_103_);
lean_dec(v_exponent_101_);
lean_dec(v_mantissa_100_);
return v_x_10_;
}
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_nat_mul(v_mantissa_100_, v_mantissa_103_);
lean_dec(v_mantissa_103_);
lean_dec(v_mantissa_100_);
v___x_108_ = lean_int_add(v_exponent_101_, v_exponent_104_);
lean_dec(v_exponent_104_);
lean_dec(v_exponent_101_);
v___x_109_ = lean_box(0);
v___x_110_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_7_, v___y_106_, v___x_107_, v___x_108_, v___x_109_);
lean_dec(v___x_108_);
return v___x_110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_fma___boxed(lean_object* v_spec_139_, lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Float_Model_UnpackedFloat_fma(v_spec_139_, v_x_140_, v_x_141_, v_x_142_);
lean_dec_ref(v_spec_139_);
return v_res_143_;
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
