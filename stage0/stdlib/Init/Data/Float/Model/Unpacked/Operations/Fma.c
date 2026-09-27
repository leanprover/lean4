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
if (lean_obj_tag(v_x_10_) == 1)
{
return v_x_10_;
}
else
{
lean_object* v___x_24_; 
lean_dec(v_x_10_);
v___x_24_ = lean_box(1);
return v___x_24_;
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
uint8_t v_sign_25_; uint8_t v_sign_26_; uint8_t v_sign_27_; uint8_t v___y_29_; 
v_sign_25_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_26_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
v_sign_27_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_25_ == 0)
{
if (v_sign_26_ == 0)
{
uint8_t v___x_34_; 
v___x_34_ = 1;
v___y_29_ = v___x_34_;
goto v___jp_28_;
}
else
{
v___y_29_ = v_sign_25_;
goto v___jp_28_;
}
}
else
{
v___y_29_ = v_sign_26_;
goto v___jp_28_;
}
v___jp_28_:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_30_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_29_);
v___x_31_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_27_);
v___x_32_ = lean_nat_dec_eq(v___x_30_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_30_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_33_ = lean_box(1);
return v___x_33_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_35_; 
lean_dec(v_x_10_);
v_sign_35_ = lean_ctor_get_uint8(v_x_8_, 0);
if (v_sign_35_ == 0)
{
uint8_t v_sign_36_; 
v_sign_36_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
if (v_sign_36_ == 0)
{
lean_object* v___x_37_; 
lean_dec_ref_known(v_x_8_, 0);
v___x_37_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_37_;
}
else
{
return v_x_8_;
}
}
else
{
lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_45_; 
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_45_ == 0)
{
v___x_39_ = v_x_8_;
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
else
{
lean_dec(v_x_8_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
uint8_t v_sign_41_; lean_object* v___x_43_; 
v_sign_41_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
if (v_isShared_40_ == 0)
{
v___x_43_ = v___x_39_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 0, 1);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
lean_ctor_set_uint8(v___x_43_, 0, v_sign_41_);
return v___x_43_;
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
lean_object* v___x_46_; 
lean_dec(v_x_10_);
v___x_46_ = lean_box(1);
return v___x_46_;
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
uint8_t v_sign_47_; uint8_t v_sign_48_; uint8_t v_sign_49_; uint8_t v___y_51_; 
v_sign_47_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_48_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_49_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_47_ == 0)
{
if (v_sign_48_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 1;
v___y_51_ = v___x_56_;
goto v___jp_50_;
}
else
{
v___y_51_ = v_sign_47_;
goto v___jp_50_;
}
}
else
{
v___y_51_ = v_sign_48_;
goto v___jp_50_;
}
v___jp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_52_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_51_);
v___x_53_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_49_);
v___x_54_ = lean_nat_dec_eq(v___x_52_, v___x_53_);
lean_dec(v___x_53_);
lean_dec(v___x_52_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_55_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_55_;
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
uint8_t v_sign_57_; uint8_t v_sign_58_; uint8_t v_sign_59_; uint8_t v___y_61_; 
v_sign_57_ = lean_ctor_get_uint8(v_x_8_, 0);
lean_dec_ref_known(v_x_8_, 0);
v_sign_58_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
lean_dec_ref_known(v_x_9_, 2);
v_sign_59_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_57_ == 0)
{
if (v_sign_58_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 1;
v___y_61_ = v___x_66_;
goto v___jp_60_;
}
else
{
v___y_61_ = v_sign_57_;
goto v___jp_60_;
}
}
else
{
v___y_61_ = v_sign_58_;
goto v___jp_60_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_61_);
v___x_63_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_59_);
v___x_64_ = lean_nat_dec_eq(v___x_62_, v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_62_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_65_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_65_;
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
uint8_t v_sign_67_; uint8_t v_sign_68_; uint8_t v_sign_69_; uint8_t v___y_71_; 
v_sign_67_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
v_sign_68_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_69_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_67_ == 0)
{
if (v_sign_68_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = 1;
v___y_71_ = v___x_76_;
goto v___jp_70_;
}
else
{
v___y_71_ = v_sign_67_;
goto v___jp_70_;
}
}
else
{
v___y_71_ = v_sign_68_;
goto v___jp_70_;
}
v___jp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_71_);
v___x_73_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_69_);
v___x_74_ = lean_nat_dec_eq(v___x_72_, v___x_73_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_75_ = lean_box(1);
return v___x_75_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
uint8_t v_sign_77_; 
lean_dec(v_x_10_);
v_sign_77_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
if (v_sign_77_ == 0)
{
uint8_t v_sign_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_86_; 
v_sign_78_ = lean_ctor_get_uint8(v_x_9_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_86_ == 0)
{
v___x_80_ = v_x_9_;
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
else
{
lean_dec(v_x_9_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
if (v_sign_78_ == 0)
{
lean_object* v___x_82_; 
lean_del_object(v___x_80_);
v___x_82_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__0));
return v___x_82_;
}
else
{
lean_object* v___x_84_; 
if (v_isShared_81_ == 0)
{
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 0, 1);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_ctor_set_uint8(v___x_84_, 0, v_sign_77_);
return v___x_84_;
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
uint8_t v_sign_87_; uint8_t v_sign_88_; uint8_t v_sign_89_; uint8_t v___y_91_; 
v_sign_87_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
lean_dec_ref_known(v_x_8_, 2);
v_sign_88_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
v_sign_89_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_87_ == 0)
{
if (v_sign_88_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
v___y_91_ = v___x_96_;
goto v___jp_90_;
}
else
{
v___y_91_ = v_sign_87_;
goto v___jp_90_;
}
}
else
{
v___y_91_ = v_sign_88_;
goto v___jp_90_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_92_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_91_);
v___x_93_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_89_);
v___x_94_ = lean_nat_dec_eq(v___x_92_, v___x_93_);
lean_dec(v___x_93_);
lean_dec(v___x_92_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_95_ = ((lean_object*)(l_Float_Model_UnpackedFloat_fma___closed__1));
return v___x_95_;
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
uint8_t v_sign_97_; lean_object* v_mantissa_98_; lean_object* v_exponent_99_; uint8_t v_sign_100_; lean_object* v_mantissa_101_; lean_object* v_exponent_102_; uint8_t v___y_104_; 
v_sign_97_ = lean_ctor_get_uint8(v_x_8_, sizeof(void*)*2);
v_mantissa_98_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_mantissa_98_);
v_exponent_99_ = lean_ctor_get(v_x_8_, 1);
lean_inc(v_exponent_99_);
lean_dec_ref_known(v_x_8_, 2);
v_sign_100_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
v_mantissa_101_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_mantissa_101_);
v_exponent_102_ = lean_ctor_get(v_x_9_, 1);
lean_inc(v_exponent_102_);
lean_dec_ref_known(v_x_9_, 2);
switch(lean_obj_tag(v_x_10_))
{
case 2:
{
lean_dec_ref_known(v_x_10_, 0);
if (v_sign_97_ == 0)
{
if (v_sign_100_ == 0)
{
uint8_t v___x_109_; 
v___x_109_ = 1;
v___y_104_ = v___x_109_;
goto v___jp_103_;
}
else
{
v___y_104_ = v_sign_97_;
goto v___jp_103_;
}
}
else
{
v___y_104_ = v_sign_100_;
goto v___jp_103_;
}
}
case 3:
{
uint8_t v_sign_110_; lean_object* v_mantissa_111_; lean_object* v_exponent_112_; lean_object* v___y_114_; lean_object* v___y_115_; lean_object* v___y_116_; uint8_t v___y_117_; lean_object* v_productMantissa_125_; lean_object* v_productExponent_126_; lean_object* v___y_128_; uint8_t v___x_136_; 
v_sign_110_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_111_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_mantissa_111_);
v_exponent_112_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_exponent_112_);
lean_dec_ref_known(v_x_10_, 2);
v_productMantissa_125_ = lean_nat_mul(v_mantissa_98_, v_mantissa_101_);
lean_dec(v_mantissa_101_);
lean_dec(v_mantissa_98_);
v_productExponent_126_ = lean_int_add(v_exponent_99_, v_exponent_102_);
lean_dec(v_exponent_102_);
lean_dec(v_exponent_99_);
v___x_136_ = lean_int_dec_le(v_productExponent_126_, v_exponent_112_);
if (v___x_136_ == 0)
{
lean_inc(v_exponent_112_);
v___y_128_ = v_exponent_112_;
goto v___jp_127_;
}
else
{
lean_inc(v_productExponent_126_);
v___y_128_ = v_productExponent_126_;
goto v___jp_127_;
}
v___jp_113_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_mantissa_122_; uint8_t v___x_123_; lean_object* v___x_124_; 
v___x_118_ = lean_nat_to_int(v___y_115_);
v___x_119_ = l_Float_Model_UnpackedFloat_Sign_apply(v___y_117_, v___x_118_);
lean_dec(v___x_118_);
v___x_120_ = lean_nat_to_int(v___y_114_);
v___x_121_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_110_, v___x_120_);
lean_dec(v___x_120_);
v_mantissa_122_ = lean_int_add(v___x_119_, v___x_121_);
lean_dec(v___x_121_);
lean_dec(v___x_119_);
v___x_123_ = 1;
v___x_124_ = l_Float_Model_UnpackedFloat_normalize(v_spec_7_, v_mantissa_122_, v___y_116_, v___x_123_);
lean_dec(v___y_116_);
lean_dec(v_mantissa_122_);
return v___x_124_;
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v_fst_130_; lean_object* v___x_131_; 
v___x_129_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_productMantissa_125_, v_productExponent_126_, v___y_128_);
lean_dec(v_productExponent_126_);
lean_dec(v_productMantissa_125_);
v_fst_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_fst_130_);
lean_dec_ref(v___x_129_);
v___x_131_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_111_, v_exponent_112_, v___y_128_);
lean_dec(v_exponent_112_);
lean_dec(v_mantissa_111_);
if (v_sign_97_ == 0)
{
if (v_sign_100_ == 0)
{
lean_object* v_fst_132_; uint8_t v___x_133_; 
v_fst_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v___x_131_);
v___x_133_ = 1;
v___y_114_ = v_fst_132_;
v___y_115_ = v_fst_130_;
v___y_116_ = v___y_128_;
v___y_117_ = v___x_133_;
goto v___jp_113_;
}
else
{
lean_object* v_fst_134_; 
v_fst_134_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_fst_134_);
lean_dec_ref(v___x_131_);
v___y_114_ = v_fst_134_;
v___y_115_ = v_fst_130_;
v___y_116_ = v___y_128_;
v___y_117_ = v_sign_97_;
goto v___jp_113_;
}
}
else
{
lean_object* v_fst_135_; 
v_fst_135_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_fst_135_);
lean_dec_ref(v___x_131_);
v___y_114_ = v_fst_135_;
v___y_115_ = v_fst_130_;
v___y_116_ = v___y_128_;
v___y_117_ = v_sign_100_;
goto v___jp_113_;
}
}
}
default: 
{
lean_dec(v_exponent_102_);
lean_dec(v_mantissa_101_);
lean_dec(v_exponent_99_);
lean_dec(v_mantissa_98_);
return v_x_10_;
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_nat_mul(v_mantissa_98_, v_mantissa_101_);
lean_dec(v_mantissa_101_);
lean_dec(v_mantissa_98_);
v___x_106_ = lean_int_add(v_exponent_99_, v_exponent_102_);
lean_dec(v_exponent_102_);
lean_dec(v_exponent_99_);
v___x_107_ = lean_box(0);
v___x_108_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_7_, v___y_104_, v___x_105_, v___x_106_, v___x_107_);
lean_dec(v___x_106_);
return v___x_108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_fma___boxed(lean_object* v_spec_137_, lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Float_Model_UnpackedFloat_fma(v_spec_137_, v_x_138_, v_x_139_, v_x_140_);
lean_dec_ref(v_spec_137_);
return v_res_141_;
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
