// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Compare
// Imports: public import Init.Data.Float.Model.Unpacked.Basic
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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
static const lean_ctor_object l_Float_Model_UnpackedFloat_compare___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Float_Model_UnpackedFloat_compare___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_compare___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_compare___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Float_Model_UnpackedFloat_compare___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_compare___closed__1_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_compare___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Float_Model_UnpackedFloat_compare___closed__2 = (const lean_object*)&l_Float_Model_UnpackedFloat_compare___closed__2_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_compare___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_le___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Float_Model_UnpackedFloat_lt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Float_Model_UnpackedFloat_lt_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_compare(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
switch(lean_obj_tag(v_x_10_))
{
case 0:
{
switch(lean_obj_tag(v_x_11_))
{
case 1:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
case 0:
{
uint8_t v_sign_21_; 
v_sign_21_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_21_ == 0)
{
uint8_t v_sign_22_; 
v_sign_22_ = lean_ctor_get_uint8(v_x_11_, 0);
if (v_sign_22_ == 0)
{
lean_object* v___x_23_; 
v___x_23_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__2));
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_24_;
}
}
else
{
uint8_t v_sign_25_; 
v_sign_25_ = lean_ctor_get_uint8(v_x_11_, 0);
if (v_sign_25_ == 0)
{
lean_object* v___x_26_; 
v___x_26_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_26_;
}
else
{
lean_object* v___x_27_; 
v___x_27_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__2));
return v___x_27_;
}
}
}
default: 
{
uint8_t v_sign_28_; 
v_sign_28_ = lean_ctor_get_uint8(v_x_10_, 0);
if (v_sign_28_ == 0)
{
goto v___jp_12_;
}
else
{
goto v___jp_14_;
}
}
}
}
case 1:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(0);
return v___x_29_;
}
case 2:
{
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
uint8_t v_sign_30_; 
v_sign_30_ = lean_ctor_get_uint8(v_x_11_, 0);
if (v_sign_30_ == 0)
{
goto v___jp_14_;
}
else
{
goto v___jp_12_;
}
}
case 1:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
case 2:
{
lean_object* v___x_32_; 
v___x_32_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__2));
return v___x_32_;
}
default: 
{
uint8_t v_sign_33_; 
v_sign_33_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
if (v_sign_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
v___x_35_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_35_;
}
}
}
}
default: 
{
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
uint8_t v_sign_36_; 
v_sign_36_ = lean_ctor_get_uint8(v_x_11_, 0);
if (v_sign_36_ == 0)
{
goto v___jp_14_;
}
else
{
goto v___jp_12_;
}
}
case 1:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
case 2:
{
uint8_t v_sign_38_; 
v_sign_38_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
if (v_sign_38_ == 0)
{
lean_object* v___x_39_; 
v___x_39_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_39_;
}
else
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_40_;
}
}
default: 
{
uint8_t v_sign_41_; 
v_sign_41_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
if (v_sign_41_ == 0)
{
uint8_t v_sign_42_; 
v_sign_42_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
if (v_sign_42_ == 0)
{
lean_object* v_mantissa_43_; lean_object* v_exponent_44_; lean_object* v_mantissa_45_; lean_object* v_exponent_46_; uint8_t v___x_47_; 
v_mantissa_43_ = lean_ctor_get(v_x_10_, 0);
v_exponent_44_ = lean_ctor_get(v_x_10_, 1);
v_mantissa_45_ = lean_ctor_get(v_x_11_, 0);
v_exponent_46_ = lean_ctor_get(v_x_11_, 1);
v___x_47_ = lean_int_dec_lt(v_exponent_44_, v_exponent_46_);
if (v___x_47_ == 0)
{
uint8_t v___x_48_; 
v___x_48_ = lean_int_dec_eq(v_exponent_44_, v_exponent_46_);
if (v___x_48_ == 0)
{
goto v___jp_18_;
}
else
{
uint8_t v___x_49_; 
v___x_49_ = lean_nat_dec_lt(v_mantissa_43_, v_mantissa_45_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = lean_nat_dec_eq(v_mantissa_43_, v_mantissa_45_);
if (v___x_50_ == 0)
{
goto v___jp_18_;
}
else
{
lean_object* v___x_51_; 
v___x_51_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__2));
return v___x_51_;
}
}
else
{
goto v___jp_16_;
}
}
}
else
{
goto v___jp_16_;
}
}
else
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_52_;
}
}
else
{
uint8_t v_sign_53_; 
v_sign_53_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
if (v_sign_53_ == 0)
{
lean_object* v___x_54_; 
v___x_54_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_54_;
}
else
{
lean_object* v_mantissa_55_; lean_object* v_exponent_56_; lean_object* v_mantissa_57_; lean_object* v_exponent_58_; uint8_t v___x_59_; 
v_mantissa_55_ = lean_ctor_get(v_x_10_, 0);
v_exponent_56_ = lean_ctor_get(v_x_10_, 1);
v_mantissa_57_ = lean_ctor_get(v_x_11_, 0);
v_exponent_58_ = lean_ctor_get(v_x_11_, 1);
v___x_59_ = lean_int_dec_lt(v_exponent_56_, v_exponent_58_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
v___x_60_ = lean_int_dec_eq(v_exponent_56_, v_exponent_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_61_;
}
else
{
uint8_t v___x_62_; 
v___x_62_ = lean_nat_dec_lt(v_mantissa_55_, v_mantissa_57_);
if (v___x_62_ == 0)
{
uint8_t v___x_63_; 
v___x_63_ = lean_nat_dec_eq(v_mantissa_55_, v_mantissa_57_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_64_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__2));
return v___x_65_;
}
}
else
{
lean_object* v___x_66_; 
v___x_66_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_66_;
}
}
}
else
{
lean_object* v___x_67_; 
v___x_67_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_67_;
}
}
}
}
}
}
}
v___jp_12_:
{
lean_object* v___x_13_; 
v___x_13_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_13_;
}
v___jp_14_:
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_15_;
}
v___jp_16_:
{
lean_object* v___x_17_; 
v___x_17_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__1));
return v___x_17_;
}
v___jp_18_:
{
lean_object* v___x_19_; 
v___x_19_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_compare___boxed(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Float_Model_UnpackedFloat_compare(v_x_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_x_68_);
return v_res_70_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_le(lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Float_Model_UnpackedFloat_compare(v_a_71_, v_b_72_);
if (lean_obj_tag(v___x_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
else
{
lean_object* v_val_75_; uint8_t v___x_76_; 
v_val_75_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v___x_73_, 1);
v___x_76_ = lean_unbox(v_val_75_);
lean_dec(v_val_75_);
if (v___x_76_ == 2)
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_le___boxed(lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Float_Model_UnpackedFloat_le(v_a_79_, v_b_80_);
lean_dec(v_b_80_);
lean_dec(v_a_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Float_Model_UnpackedFloat_lt_spec__0(lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
if (lean_obj_tag(v_x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
else
{
if (lean_obj_tag(v_x_84_) == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v_val_89_; uint8_t v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; 
v_val_88_ = lean_ctor_get(v_x_83_, 0);
v_val_89_ = lean_ctor_get(v_x_84_, 0);
v___x_90_ = lean_unbox(v_val_88_);
v___x_91_ = lean_unbox(v_val_89_);
v___x_92_ = l_instDecidableEqOrdering(v___x_90_, v___x_91_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Float_Model_UnpackedFloat_lt_spec__0___boxed(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Option_instBEq_beq___at___00Float_Model_UnpackedFloat_lt_spec__0(v_x_93_, v_x_94_);
lean_dec(v_x_94_);
lean_dec(v_x_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_lt(lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = l_Float_Model_UnpackedFloat_compare(v_a_97_, v_b_98_);
v___x_100_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__0));
v___x_101_ = l_Option_instBEq_beq___at___00Float_Model_UnpackedFloat_lt_spec__0(v___x_99_, v___x_100_);
lean_dec(v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_lt___boxed(lean_object* v_a_102_, lean_object* v_b_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Float_Model_UnpackedFloat_lt(v_a_102_, v_b_103_);
lean_dec(v_b_103_);
lean_dec(v_a_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_beq(lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = l_Float_Model_UnpackedFloat_compare(v_a_106_, v_b_107_);
v___x_109_ = ((lean_object*)(l_Float_Model_UnpackedFloat_compare___closed__2));
v___x_110_ = l_Option_instBEq_beq___at___00Float_Model_UnpackedFloat_lt_spec__0(v___x_108_, v___x_109_);
lean_dec(v___x_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_beq___boxed(lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Float_Model_UnpackedFloat_beq(v_a_111_, v_b_112_);
lean_dec(v_b_112_);
lean_dec(v_a_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(builtin);
}
#ifdef __cplusplus
}
#endif
