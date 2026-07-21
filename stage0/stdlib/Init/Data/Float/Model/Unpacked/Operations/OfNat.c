// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.OfNat
// Imports: public import Init.Data.Float.Model.Unpacked.Round public import Init.Data.SInt.Basic
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
lean_object* lean_int32_to_int(uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_normalize(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_int8_to_int(uint8_t);
lean_object* lean_isize_to_int(size_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* lean_int16_to_int(uint16_t);
lean_object* lean_uint64_to_nat(uint64_t);
static lean_once_cell_t l_Float_Model_UnpackedFloat_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_ofInt___closed__0;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_ofNat_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt8(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt16(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt32(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt32___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt64(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt64___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUSize(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt8(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt16(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt32(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt32___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt64(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt64___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofISize(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofISize___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Float_Model_UnpackedFloat_ofInt___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt(lean_object* v_spec_3_, lean_object* v_n_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_obj_once(&l_Float_Model_UnpackedFloat_ofInt___closed__0, &l_Float_Model_UnpackedFloat_ofInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_ofInt___closed__0);
v___x_6_ = 1;
v___x_7_ = l_Float_Model_UnpackedFloat_normalize(v_spec_3_, v_n_4_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt___boxed(lean_object* v_spec_8_, lean_object* v_n_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_8_, v_n_9_);
lean_dec(v_n_9_);
lean_dec_ref(v_spec_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_ofNat_spec__0(lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_nat_to_int(v_a_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofNat(lean_object* v_spec_13_, lean_object* v_n_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_nat_to_int(v_n_14_);
v___x_16_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_13_, v___x_15_);
lean_dec(v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofNat___boxed(lean_object* v_spec_17_, lean_object* v_n_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_17_, v_n_18_);
lean_dec_ref(v_spec_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt8(lean_object* v_spec_20_, uint8_t v_n_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_uint8_to_nat(v_n_21_);
v___x_23_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt8___boxed(lean_object* v_spec_24_, lean_object* v_n_25_){
_start:
{
uint8_t v_n_boxed_26_; lean_object* v_res_27_; 
v_n_boxed_26_ = lean_unbox(v_n_25_);
v_res_27_ = l_Float_Model_UnpackedFloat_ofUInt8(v_spec_24_, v_n_boxed_26_);
lean_dec_ref(v_spec_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt16(lean_object* v_spec_28_, uint16_t v_n_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_uint16_to_nat(v_n_29_);
v___x_31_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_28_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt16___boxed(lean_object* v_spec_32_, lean_object* v_n_33_){
_start:
{
uint16_t v_n_boxed_34_; lean_object* v_res_35_; 
v_n_boxed_34_ = lean_unbox(v_n_33_);
v_res_35_ = l_Float_Model_UnpackedFloat_ofUInt16(v_spec_32_, v_n_boxed_34_);
lean_dec_ref(v_spec_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt32(lean_object* v_spec_36_, uint32_t v_n_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_uint32_to_nat(v_n_37_);
v___x_39_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_36_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt32___boxed(lean_object* v_spec_40_, lean_object* v_n_41_){
_start:
{
uint32_t v_n_boxed_42_; lean_object* v_res_43_; 
v_n_boxed_42_ = lean_unbox_uint32(v_n_41_);
lean_dec(v_n_41_);
v_res_43_ = l_Float_Model_UnpackedFloat_ofUInt32(v_spec_40_, v_n_boxed_42_);
lean_dec_ref(v_spec_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt64(lean_object* v_spec_44_, uint64_t v_n_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_uint64_to_nat(v_n_45_);
v___x_47_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_44_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt64___boxed(lean_object* v_spec_48_, lean_object* v_n_49_){
_start:
{
uint64_t v_n_boxed_50_; lean_object* v_res_51_; 
v_n_boxed_50_ = lean_unbox_uint64(v_n_49_);
lean_dec_ref(v_n_49_);
v_res_51_ = l_Float_Model_UnpackedFloat_ofUInt64(v_spec_48_, v_n_boxed_50_);
lean_dec_ref(v_spec_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUSize(lean_object* v_spec_52_, size_t v_n_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_usize_to_nat(v_n_53_);
v___x_55_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_52_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUSize___boxed(lean_object* v_spec_56_, lean_object* v_n_57_){
_start:
{
size_t v_n_boxed_58_; lean_object* v_res_59_; 
v_n_boxed_58_ = lean_unbox_usize(v_n_57_);
lean_dec(v_n_57_);
v_res_59_ = l_Float_Model_UnpackedFloat_ofUSize(v_spec_56_, v_n_boxed_58_);
lean_dec_ref(v_spec_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt8(lean_object* v_spec_60_, uint8_t v_n_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_int8_to_int(v_n_61_);
v___x_63_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_60_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt8___boxed(lean_object* v_spec_64_, lean_object* v_n_65_){
_start:
{
uint8_t v_n_boxed_66_; lean_object* v_res_67_; 
v_n_boxed_66_ = lean_unbox(v_n_65_);
v_res_67_ = l_Float_Model_UnpackedFloat_ofInt8(v_spec_64_, v_n_boxed_66_);
lean_dec_ref(v_spec_64_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt16(lean_object* v_spec_68_, uint16_t v_n_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_int16_to_int(v_n_69_);
v___x_71_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_68_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt16___boxed(lean_object* v_spec_72_, lean_object* v_n_73_){
_start:
{
uint16_t v_n_boxed_74_; lean_object* v_res_75_; 
v_n_boxed_74_ = lean_unbox(v_n_73_);
v_res_75_ = l_Float_Model_UnpackedFloat_ofInt16(v_spec_72_, v_n_boxed_74_);
lean_dec_ref(v_spec_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt32(lean_object* v_spec_76_, uint32_t v_n_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_int32_to_int(v_n_77_);
v___x_79_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_76_, v___x_78_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt32___boxed(lean_object* v_spec_80_, lean_object* v_n_81_){
_start:
{
uint32_t v_n_boxed_82_; lean_object* v_res_83_; 
v_n_boxed_82_ = lean_unbox_uint32(v_n_81_);
lean_dec(v_n_81_);
v_res_83_ = l_Float_Model_UnpackedFloat_ofInt32(v_spec_80_, v_n_boxed_82_);
lean_dec_ref(v_spec_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt64(lean_object* v_spec_84_, uint64_t v_n_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_int64_to_int_sint(v_n_85_);
v___x_87_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_84_, v___x_86_);
lean_dec(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt64___boxed(lean_object* v_spec_88_, lean_object* v_n_89_){
_start:
{
uint64_t v_n_boxed_90_; lean_object* v_res_91_; 
v_n_boxed_90_ = lean_unbox_uint64(v_n_89_);
lean_dec_ref(v_n_89_);
v_res_91_ = l_Float_Model_UnpackedFloat_ofInt64(v_spec_88_, v_n_boxed_90_);
lean_dec_ref(v_spec_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofISize(lean_object* v_spec_92_, size_t v_n_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_isize_to_int(v_n_93_);
v___x_95_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_92_, v___x_94_);
lean_dec(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofISize___boxed(lean_object* v_spec_96_, lean_object* v_n_97_){
_start:
{
size_t v_n_boxed_98_; lean_object* v_res_99_; 
v_n_boxed_98_ = lean_unbox_usize(v_n_97_);
lean_dec(v_n_97_);
v_res_99_ = l_Float_Model_UnpackedFloat_ofISize(v_spec_96_, v_n_boxed_98_);
lean_dec_ref(v_spec_96_);
return v_res_99_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_OfNat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_OfNat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_OfNat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_OfNat(builtin);
}
#ifdef __cplusplus
}
#endif
