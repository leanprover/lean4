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
lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx(uint8_t);
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
uint8_t v_sign_23_; 
v_sign_23_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
if (v_sign_23_ == 0)
{
uint8_t v___x_24_; 
v___x_24_ = 1;
v___y_18_ = v___x_24_;
goto v___jp_17_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = 0;
v___y_18_ = v___x_25_;
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
lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_19_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_16_);
v___x_20_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_18_);
v___x_21_ = lean_nat_dec_eq(v___x_19_, v___x_20_);
lean_dec(v___x_20_);
lean_dec(v___x_19_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_22_ = lean_box(1);
return v___x_22_;
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
uint8_t v_sign_26_; uint8_t v___y_28_; 
v_sign_26_ = lean_ctor_get_uint8(v_x_10_, 0);
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
uint8_t v_sign_33_; 
lean_dec_ref_known(v_x_10_, 0);
v_sign_33_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
v_s_13_ = v_sign_33_;
goto v___jp_12_;
}
case 1:
{
lean_dec_ref_known(v_x_10_, 0);
return v_x_11_;
}
case 2:
{
uint8_t v_sign_34_; 
v_sign_34_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
if (v_sign_34_ == 0)
{
uint8_t v___x_35_; 
v___x_35_ = 1;
v___y_28_ = v___x_35_;
goto v___jp_27_;
}
else
{
uint8_t v___x_36_; 
v___x_36_ = 0;
v___y_28_ = v___x_36_;
goto v___jp_27_;
}
}
default: 
{
uint8_t v_sign_37_; 
lean_dec_ref_known(v_x_10_, 0);
v_sign_37_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
if (v_sign_37_ == 0)
{
lean_object* v_mantissa_38_; lean_object* v_exponent_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
v_mantissa_38_ = lean_ctor_get(v_x_11_, 0);
v_exponent_39_ = lean_ctor_get(v_x_11_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_47_ == 0)
{
v___x_41_ = v_x_11_;
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_exponent_39_);
lean_inc(v_mantissa_38_);
lean_dec(v_x_11_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
uint8_t v___x_43_; lean_object* v___x_45_; 
v___x_43_ = 1;
if (v_isShared_42_ == 0)
{
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_mantissa_38_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_exponent_39_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*2, v___x_43_);
return v___x_45_;
}
}
}
else
{
lean_object* v_mantissa_48_; lean_object* v_exponent_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_57_; 
v_mantissa_48_ = lean_ctor_get(v_x_11_, 0);
v_exponent_49_ = lean_ctor_get(v_x_11_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_57_ == 0)
{
v___x_51_ = v_x_11_;
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_exponent_49_);
lean_inc(v_mantissa_48_);
lean_dec(v_x_11_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v___x_53_; lean_object* v___x_55_; 
v___x_53_ = 0;
if (v_isShared_52_ == 0)
{
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_mantissa_48_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_exponent_49_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*2, v___x_53_);
return v___x_55_;
}
}
}
}
}
v___jp_27_:
{
lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_29_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_26_);
v___x_30_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v___y_28_);
v___x_31_ = lean_nat_dec_eq(v___x_29_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v___x_29_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
lean_dec_ref_known(v_x_10_, 0);
v___x_32_ = ((lean_object*)(l_Float_Model_UnpackedFloat_sub___closed__2));
return v___x_32_;
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
uint8_t v_sign_58_; 
lean_dec_ref_known(v_x_10_, 2);
v_sign_58_ = lean_ctor_get_uint8(v_x_11_, 0);
lean_dec_ref_known(v_x_11_, 0);
v_s_13_ = v_sign_58_;
goto v___jp_12_;
}
case 1:
{
lean_dec_ref_known(v_x_10_, 2);
return v_x_11_;
}
case 2:
{
uint8_t v_sign_59_; lean_object* v_mantissa_60_; lean_object* v_exponent_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec_ref_known(v_x_11_, 0);
v_sign_59_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_60_ = lean_ctor_get(v_x_10_, 0);
v_exponent_61_ = lean_ctor_get(v_x_10_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_10_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v_x_10_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_exponent_61_);
lean_inc(v_mantissa_60_);
lean_dec(v_x_10_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_mantissa_60_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_exponent_61_);
lean_ctor_set_uint8(v_reuseFailAlloc_67_, sizeof(void*)*2, v_sign_59_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
default: 
{
uint8_t v_sign_69_; lean_object* v_mantissa_70_; lean_object* v_exponent_71_; uint8_t v_sign_72_; lean_object* v_mantissa_73_; lean_object* v_exponent_74_; lean_object* v___y_76_; uint8_t v___x_88_; 
v_sign_69_ = lean_ctor_get_uint8(v_x_10_, sizeof(void*)*2);
v_mantissa_70_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_mantissa_70_);
v_exponent_71_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_exponent_71_);
lean_dec_ref_known(v_x_10_, 2);
v_sign_72_ = lean_ctor_get_uint8(v_x_11_, sizeof(void*)*2);
v_mantissa_73_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_mantissa_73_);
v_exponent_74_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_exponent_74_);
lean_dec_ref_known(v_x_11_, 2);
v___x_88_ = lean_int_dec_le(v_exponent_71_, v_exponent_74_);
if (v___x_88_ == 0)
{
lean_inc(v_exponent_74_);
v___y_76_ = v_exponent_74_;
goto v___jp_75_;
}
else
{
lean_inc(v_exponent_71_);
v___y_76_ = v_exponent_71_;
goto v___jp_75_;
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v_fst_78_; lean_object* v___x_79_; lean_object* v_fst_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_mantissa_85_; uint8_t v___x_86_; lean_object* v___x_87_; 
v___x_77_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_70_, v_exponent_71_, v___y_76_);
lean_dec(v_exponent_71_);
lean_dec(v_mantissa_70_);
v_fst_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_fst_78_);
lean_dec_ref(v___x_77_);
v___x_79_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_73_, v_exponent_74_, v___y_76_);
lean_dec(v_exponent_74_);
lean_dec(v_mantissa_73_);
v_fst_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_fst_80_);
lean_dec_ref(v___x_79_);
v___x_81_ = lean_nat_to_int(v_fst_78_);
v___x_82_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_69_, v___x_81_);
lean_dec(v___x_81_);
v___x_83_ = lean_nat_to_int(v_fst_80_);
v___x_84_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_72_, v___x_83_);
lean_dec(v___x_83_);
v_mantissa_85_ = lean_int_sub(v___x_82_, v___x_84_);
lean_dec(v___x_84_);
lean_dec(v___x_82_);
v___x_86_ = 1;
v___x_87_ = l_Float_Model_UnpackedFloat_normalize(v_spec_9_, v_mantissa_85_, v___y_76_, v___x_86_);
lean_dec(v___y_76_);
lean_dec(v_mantissa_85_);
return v___x_87_;
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sub___boxed(lean_object* v_spec_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Float_Model_UnpackedFloat_sub(v_spec_89_, v_x_90_, v_x_91_);
lean_dec_ref(v_spec_89_);
return v_res_92_;
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
