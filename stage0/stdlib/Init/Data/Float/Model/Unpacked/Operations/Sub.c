// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Sub
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_decreaseExponent(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_normalize(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_sub_spec__0(lean_object*);
static const lean_ctor_object l_Float_Model_UnpackedFloat_sub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_sub___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_sub___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_sub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_sub___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_sub___closed__1_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_sub___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_sub___closed__2 = (const lean_object*)&l_Float_Model_UnpackedFloat_sub___closed__2_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_sub_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sub(lean_object* v_spec_9_, lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_s_13_; 
switch(lean_obj_tag(v_x_10_))
{
case 0:
{
uint8_t v_sign_16_; uint8_t v___y_18_; 
v_sign_16_ = lean_ctor_get_uint8(v_x_10_, 0);
switch(lean_obj_tag(v_x_11_))
{
case 1:
{
lean_dec_ref_known(v_x_10_, 0);
return v_x_11_;
}
case 0:
{
uint8_t v_sign_25_; 
v_sign_25_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
if (v_sign_25_ == 0)
{
uint8_t v___x_26_; 
v___x_26_ = 1;
v___y_18_ = v___x_26_;
goto v___jp_17_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = 0;
v___y_18_ = v___x_27_;
goto v___jp_17_;
}
}
default: 
{
lean_dec(v_x_11_);
return v_x_10_;
}
}
v___jp_17_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_19_ = lean_box(v_sign_16_);
v___x_20_ = lean_obj_tag_nat(v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = lean_box(v___y_18_);
v___x_22_ = lean_obj_tag_nat(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_nat_dec_eq(v___x_20_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_24_ = lean_box(1);
return v___x_24_;
}
else
{
return v_x_10_;
}
}
}
case 1:
{
lean_dec(v_x_11_);
return v_x_10_;
}
case 2:
{
uint8_t v_sign_28_; uint8_t v___y_30_; 
v_sign_28_ = lean_ctor_get_uint8(v_x_10_, 0);
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
uint8_t v_sign_37_; 
lean_dec_ref_known(v_x_10_, 0);
v_sign_37_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
v_s_13_ = v_sign_37_;
goto v___jp_12_;
}
case 1:
{
lean_dec_ref_known(v_x_10_, 0);
return v_x_11_;
}
case 2:
{
uint8_t v_sign_38_; 
v_sign_38_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
if (v_sign_38_ == 0)
{
uint8_t v___x_39_; 
v___x_39_ = 1;
v___y_30_ = v___x_39_;
goto v___jp_29_;
}
else
{
uint8_t v___x_40_; 
v___x_40_ = 0;
v___y_30_ = v___x_40_;
goto v___jp_29_;
}
}
default: 
{
uint8_t v_sign_41_; 
lean_dec_ref_known(v_x_10_, 0);
v_sign_41_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
if (v_sign_41_ == 0)
{
lean_object* v_mantissa_42_; lean_object* v_exponent_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_mantissa_42_ = lean_ctor_get(v_x_11_, 0);
v_exponent_43_ = lean_ctor_get(v_x_11_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v_x_11_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_exponent_43_);
lean_inc(v_mantissa_42_);
lean_dec(v_x_11_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
uint8_t v___x_47_; lean_object* v___x_49_; 
v___x_47_ = 1;
if (v_isShared_46_ == 0)
{
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_mantissa_42_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_exponent_43_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*2, v___x_47_);
return v___x_49_;
}
}
}
else
{
lean_object* v_mantissa_52_; lean_object* v_exponent_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_61_; 
v_mantissa_52_ = lean_ctor_get(v_x_11_, 0);
v_exponent_53_ = lean_ctor_get(v_x_11_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_61_ == 0)
{
v___x_55_ = v_x_11_;
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_exponent_53_);
lean_inc(v_mantissa_52_);
lean_dec(v_x_11_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; lean_object* v___x_59_; 
v___x_57_ = 0;
if (v_isShared_56_ == 0)
{
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_mantissa_52_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_exponent_53_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*2, v___x_57_);
return v___x_59_;
}
}
}
}
}
v___jp_29_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_31_ = lean_box(v_sign_28_);
v___x_32_ = lean_obj_tag_nat(v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_box(v___y_30_);
v___x_34_ = lean_obj_tag_nat(v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = lean_nat_dec_eq(v___x_32_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_36_ = ((lean_object*)(l_Float_Model_UnpackedFloat_sub___closed__2));
return v___x_36_;
}
else
{
return v_x_10_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
uint8_t v_sign_62_; 
lean_dec_ref_known(v_x_10_, 2);
v_sign_62_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
v_s_13_ = v_sign_62_;
goto v___jp_12_;
}
case 1:
{
lean_dec_ref_known(v_x_10_, 2);
return v_x_11_;
}
case 2:
{
uint8_t v_sign_63_; lean_object* v_mantissa_64_; lean_object* v_exponent_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_dec_ref_known(v_x_11_, 0);
v_sign_63_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_64_ = lean_ctor_get(v_x_10_, 0);
v_exponent_65_ = lean_ctor_get(v_x_10_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v_x_10_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v_x_10_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_exponent_65_);
lean_inc(v_mantissa_64_);
lean_dec(v_x_10_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_mantissa_64_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_exponent_65_);
lean_ctor_set_uint8(v_reuseFailAlloc_71_, sizeof(void*)*2, v_sign_63_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
default: 
{
uint8_t v_sign_73_; lean_object* v_mantissa_74_; lean_object* v_exponent_75_; uint8_t v_sign_76_; lean_object* v_mantissa_77_; lean_object* v_exponent_78_; lean_object* v___y_80_; uint8_t v___x_92_; 
v_sign_73_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_74_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_mantissa_74_);
v_exponent_75_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_exponent_75_);
lean_dec_ref_known(v_x_10_, 2);
v_sign_76_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
v_mantissa_77_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_mantissa_77_);
v_exponent_78_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_exponent_78_);
lean_dec_ref_known(v_x_11_, 2);
v___x_92_ = lean_int_dec_le(v_exponent_75_, v_exponent_78_);
if (v___x_92_ == 0)
{
lean_inc(v_exponent_78_);
v___y_80_ = v_exponent_78_;
goto v___jp_79_;
}
else
{
lean_inc(v_exponent_75_);
v___y_80_ = v_exponent_75_;
goto v___jp_79_;
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v_fst_82_; lean_object* v___x_83_; lean_object* v_fst_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_mantissa_89_; uint8_t v___x_90_; lean_object* v___x_91_; 
v___x_81_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_74_, v_exponent_75_, v___y_80_);
lean_dec(v_exponent_75_);
lean_dec(v_mantissa_74_);
v_fst_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_fst_82_);
lean_dec_ref(v___x_81_);
v___x_83_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_77_, v_exponent_78_, v___y_80_);
lean_dec(v_exponent_78_);
lean_dec(v_mantissa_77_);
v_fst_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_fst_84_);
lean_dec_ref(v___x_83_);
v___x_85_ = lean_nat_to_int(v_fst_82_);
v___x_86_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_73_, v___x_85_);
lean_dec(v___x_85_);
v___x_87_ = lean_nat_to_int(v_fst_84_);
v___x_88_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_76_, v___x_87_);
lean_dec(v___x_87_);
v_mantissa_89_ = lean_int_sub(v___x_86_, v___x_88_);
lean_dec(v___x_88_);
lean_dec(v___x_86_);
v___x_90_ = 1;
v___x_91_ = l_Float_Model_UnpackedFloat_normalize(v_spec_9_, v_mantissa_89_, v___y_80_, v___x_90_);
lean_dec(v___y_80_);
lean_dec(v_mantissa_89_);
return v___x_91_;
}
}
}
}
}
v___jp_12_:
{
if (v_s_13_ == 0)
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l_Float_Model_UnpackedFloat_sub___closed__0));
return v___x_14_;
}
else
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Float_Model_UnpackedFloat_sub___closed__1));
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sub___boxed(lean_object* v_spec_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Float_Model_UnpackedFloat_sub(v_spec_93_, v_x_94_, v_x_95_);
lean_dec_ref(v_spec_93_);
return v_res_96_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Sub(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Sub(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Sub(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Sub(builtin);
}
#ifdef __cplusplus
}
#endif
