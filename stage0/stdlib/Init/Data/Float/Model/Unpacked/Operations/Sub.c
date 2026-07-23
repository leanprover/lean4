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
uint8_t l_Float_Model_UnpackedFloat_instBEqSign_beq(uint8_t, uint8_t);
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
uint8_t v_sign_21_; 
v_sign_21_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
if (v_sign_21_ == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 1;
v___y_18_ = v___x_22_;
goto v___jp_17_;
}
else
{
uint8_t v___x_23_; 
v___x_23_ = 0;
v___y_18_ = v___x_23_;
goto v___jp_17_;
}
}
case 2:
{
lean_dec_ref_known(v_x_11_, 0);
return v_x_10_;
}
default: 
{
lean_dec(v_x_11_);
return v_x_10_;
}
}
v___jp_17_:
{
uint8_t v___x_19_; 
v___x_19_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_sign_16_, v___y_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_20_ = lean_box(1);
return v___x_20_;
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
uint8_t v_sign_24_; uint8_t v___y_26_; 
v_sign_24_ = lean_ctor_get_uint8(v_x_10_, 0);
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
uint8_t v_sign_29_; 
lean_dec_ref_known(v_x_10_, 0);
v_sign_29_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
v_s_13_ = v_sign_29_;
goto v___jp_12_;
}
case 1:
{
lean_dec_ref_known(v_x_10_, 0);
return v_x_11_;
}
case 2:
{
uint8_t v_sign_30_; 
v_sign_30_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
if (v_sign_30_ == 0)
{
uint8_t v___x_31_; 
v___x_31_ = 1;
v___y_26_ = v___x_31_;
goto v___jp_25_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 0;
v___y_26_ = v___x_32_;
goto v___jp_25_;
}
}
default: 
{
uint8_t v_sign_33_; 
lean_dec_ref_known(v_x_10_, 0);
v_sign_33_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
if (v_sign_33_ == 0)
{
lean_object* v_mantissa_34_; lean_object* v_exponent_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_mantissa_34_ = lean_ctor_get(v_x_11_, 0);
v_exponent_35_ = lean_ctor_get(v_x_11_, 1);
v_isSharedCheck_43_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v_x_11_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_exponent_35_);
lean_inc(v_mantissa_34_);
lean_dec(v_x_11_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
uint8_t v___x_39_; lean_object* v___x_41_; 
v___x_39_ = 1;
if (v_isShared_38_ == 0)
{
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_mantissa_34_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_exponent_35_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_ctor_set_uint8(v___x_41_, sizeof(void*)*2, v___x_39_);
return v___x_41_;
}
}
}
else
{
lean_object* v_mantissa_44_; lean_object* v_exponent_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_53_; 
v_mantissa_44_ = lean_ctor_get(v_x_11_, 0);
v_exponent_45_ = lean_ctor_get(v_x_11_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_53_ == 0)
{
v___x_47_ = v_x_11_;
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_exponent_45_);
lean_inc(v_mantissa_44_);
lean_dec(v_x_11_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
uint8_t v___x_49_; lean_object* v___x_51_; 
v___x_49_ = 0;
if (v_isShared_48_ == 0)
{
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_mantissa_44_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_exponent_45_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*2, v___x_49_);
return v___x_51_;
}
}
}
}
}
v___jp_25_:
{
uint8_t v___x_27_; 
v___x_27_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_sign_24_, v___y_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_28_ = ((lean_object*)(l_Float_Model_UnpackedFloat_sub___closed__2));
return v___x_28_;
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
uint8_t v_sign_54_; 
lean_dec_ref_known(v_x_10_, 2);
v_sign_54_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
v_s_13_ = v_sign_54_;
goto v___jp_12_;
}
case 1:
{
lean_dec_ref_known(v_x_10_, 2);
return v_x_11_;
}
case 2:
{
uint8_t v_sign_55_; lean_object* v_mantissa_56_; lean_object* v_exponent_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
lean_dec_ref_known(v_x_11_, 0);
v_sign_55_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_56_ = lean_ctor_get(v_x_10_, 0);
v_exponent_57_ = lean_ctor_get(v_x_10_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_x_10_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v_x_10_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_exponent_57_);
lean_inc(v_mantissa_56_);
lean_dec(v_x_10_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_mantissa_56_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_exponent_57_);
lean_ctor_set_uint8(v_reuseFailAlloc_63_, sizeof(void*)*2, v_sign_55_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
default: 
{
uint8_t v_sign_65_; lean_object* v_mantissa_66_; lean_object* v_exponent_67_; uint8_t v_sign_68_; lean_object* v_mantissa_69_; lean_object* v_exponent_70_; lean_object* v___y_72_; uint8_t v___x_84_; 
v_sign_65_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_66_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_mantissa_66_);
v_exponent_67_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_exponent_67_);
lean_dec_ref_known(v_x_10_, 2);
v_sign_68_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
v_mantissa_69_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_mantissa_69_);
v_exponent_70_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_exponent_70_);
lean_dec_ref_known(v_x_11_, 2);
v___x_84_ = lean_int_dec_le(v_exponent_67_, v_exponent_70_);
if (v___x_84_ == 0)
{
lean_inc(v_exponent_70_);
v___y_72_ = v_exponent_70_;
goto v___jp_71_;
}
else
{
lean_inc(v_exponent_67_);
v___y_72_ = v_exponent_67_;
goto v___jp_71_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v_fst_74_; lean_object* v___x_75_; lean_object* v_fst_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_mantissa_81_; uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_73_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_66_, v_exponent_67_, v___y_72_);
lean_dec(v_exponent_67_);
lean_dec(v_mantissa_66_);
v_fst_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_fst_74_);
lean_dec_ref(v___x_73_);
v___x_75_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_69_, v_exponent_70_, v___y_72_);
lean_dec(v_exponent_70_);
lean_dec(v_mantissa_69_);
v_fst_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_fst_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lean_nat_to_int(v_fst_74_);
v___x_78_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_65_, v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = lean_nat_to_int(v_fst_76_);
v___x_80_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_68_, v___x_79_);
lean_dec(v___x_79_);
v_mantissa_81_ = lean_int_sub(v___x_78_, v___x_80_);
lean_dec(v___x_80_);
lean_dec(v___x_78_);
v___x_82_ = 1;
v___x_83_ = l_Float_Model_UnpackedFloat_normalize(v_spec_9_, v_mantissa_81_, v___y_72_, v___x_82_);
lean_dec(v___y_72_);
lean_dec(v_mantissa_81_);
return v___x_83_;
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sub___boxed(lean_object* v_spec_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Float_Model_UnpackedFloat_sub(v_spec_85_, v_x_86_, v_x_87_);
lean_dec_ref(v_spec_85_);
return v_res_88_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Sub(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
