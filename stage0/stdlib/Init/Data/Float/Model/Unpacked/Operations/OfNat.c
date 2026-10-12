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
lean_object* l_Float_Model_UnpackedFloat_ofUInt8(lean_object* v_spec_20_, uint8_t v_n_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_uint8_to_nat(v_n_21_);
v___x_23_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofUInt8_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_20_ = stack[0].m_obj;
uint8_t v_n_21_ = stack[1].m_num;
lean_object* v_res_24_;
v_res_24_ = l_Float_Model_UnpackedFloat_ofUInt8(v_spec_20_, v_n_21_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt8___boxed(lean_object* v_spec_25_, lean_object* v_n_26_){
_start:
{
uint8_t v_n_boxed_27_; lean_object* v_res_28_; 
v_n_boxed_27_ = lean_unbox(v_n_26_);
v_res_28_ = l_Float_Model_UnpackedFloat_ofUInt8(v_spec_25_, v_n_boxed_27_);
lean_dec_ref(v_spec_25_);
return v_res_28_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofUInt16(lean_object* v_spec_29_, uint16_t v_n_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_uint16_to_nat(v_n_30_);
v___x_32_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_29_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofUInt16_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_29_ = stack[0].m_obj;
uint16_t v_n_30_ = stack[1].m_num;
lean_object* v_res_33_;
v_res_33_ = l_Float_Model_UnpackedFloat_ofUInt16(v_spec_29_, v_n_30_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt16___boxed(lean_object* v_spec_34_, lean_object* v_n_35_){
_start:
{
uint16_t v_n_boxed_36_; lean_object* v_res_37_; 
v_n_boxed_36_ = lean_unbox(v_n_35_);
v_res_37_ = l_Float_Model_UnpackedFloat_ofUInt16(v_spec_34_, v_n_boxed_36_);
lean_dec_ref(v_spec_34_);
return v_res_37_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofUInt32(lean_object* v_spec_38_, uint32_t v_n_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_uint32_to_nat(v_n_39_);
v___x_41_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_38_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofUInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_38_ = stack[0].m_obj;
uint32_t v_n_39_ = stack[1].m_num;
lean_object* v_res_42_;
v_res_42_ = l_Float_Model_UnpackedFloat_ofUInt32(v_spec_38_, v_n_39_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt32___boxed(lean_object* v_spec_43_, lean_object* v_n_44_){
_start:
{
uint32_t v_n_boxed_45_; lean_object* v_res_46_; 
v_n_boxed_45_ = lean_unbox_uint32(v_n_44_);
lean_dec(v_n_44_);
v_res_46_ = l_Float_Model_UnpackedFloat_ofUInt32(v_spec_43_, v_n_boxed_45_);
lean_dec_ref(v_spec_43_);
return v_res_46_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofUInt64(lean_object* v_spec_47_, uint64_t v_n_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_uint64_to_nat(v_n_48_);
v___x_50_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_47_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofUInt64_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_47_ = stack[0].m_obj;
uint64_t v_n_48_ = stack[1].m_num;
lean_object* v_res_51_;
v_res_51_ = l_Float_Model_UnpackedFloat_ofUInt64(v_spec_47_, v_n_48_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUInt64___boxed(lean_object* v_spec_52_, lean_object* v_n_53_){
_start:
{
uint64_t v_n_boxed_54_; lean_object* v_res_55_; 
v_n_boxed_54_ = lean_unbox_uint64(v_n_53_);
lean_dec_ref(v_n_53_);
v_res_55_ = l_Float_Model_UnpackedFloat_ofUInt64(v_spec_52_, v_n_boxed_54_);
lean_dec_ref(v_spec_52_);
return v_res_55_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofUSize(lean_object* v_spec_56_, size_t v_n_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_usize_to_nat(v_n_57_);
v___x_59_ = l_Float_Model_UnpackedFloat_ofNat(v_spec_56_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofUSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_56_ = stack[0].m_obj;
size_t v_n_57_ = stack[1].m_num;
lean_object* v_res_60_;
v_res_60_ = l_Float_Model_UnpackedFloat_ofUSize(v_spec_56_, v_n_57_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofUSize___boxed(lean_object* v_spec_61_, lean_object* v_n_62_){
_start:
{
size_t v_n_boxed_63_; lean_object* v_res_64_; 
v_n_boxed_63_ = lean_unbox_usize(v_n_62_);
lean_dec(v_n_62_);
v_res_64_ = l_Float_Model_UnpackedFloat_ofUSize(v_spec_61_, v_n_boxed_63_);
lean_dec_ref(v_spec_61_);
return v_res_64_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofInt8(lean_object* v_spec_65_, uint8_t v_n_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_int8_to_int(v_n_66_);
v___x_68_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_65_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofInt8_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_65_ = stack[0].m_obj;
uint8_t v_n_66_ = stack[1].m_num;
lean_object* v_res_69_;
v_res_69_ = l_Float_Model_UnpackedFloat_ofInt8(v_spec_65_, v_n_66_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt8___boxed(lean_object* v_spec_70_, lean_object* v_n_71_){
_start:
{
uint8_t v_n_boxed_72_; lean_object* v_res_73_; 
v_n_boxed_72_ = lean_unbox(v_n_71_);
v_res_73_ = l_Float_Model_UnpackedFloat_ofInt8(v_spec_70_, v_n_boxed_72_);
lean_dec_ref(v_spec_70_);
return v_res_73_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofInt16(lean_object* v_spec_74_, uint16_t v_n_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_int16_to_int(v_n_75_);
v___x_77_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_74_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofInt16_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_74_ = stack[0].m_obj;
uint16_t v_n_75_ = stack[1].m_num;
lean_object* v_res_78_;
v_res_78_ = l_Float_Model_UnpackedFloat_ofInt16(v_spec_74_, v_n_75_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt16___boxed(lean_object* v_spec_79_, lean_object* v_n_80_){
_start:
{
uint16_t v_n_boxed_81_; lean_object* v_res_82_; 
v_n_boxed_81_ = lean_unbox(v_n_80_);
v_res_82_ = l_Float_Model_UnpackedFloat_ofInt16(v_spec_79_, v_n_boxed_81_);
lean_dec_ref(v_spec_79_);
return v_res_82_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofInt32(lean_object* v_spec_83_, uint32_t v_n_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_int32_to_int(v_n_84_);
v___x_86_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_83_, v___x_85_);
lean_dec(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_83_ = stack[0].m_obj;
uint32_t v_n_84_ = stack[1].m_num;
lean_object* v_res_87_;
v_res_87_ = l_Float_Model_UnpackedFloat_ofInt32(v_spec_83_, v_n_84_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt32___boxed(lean_object* v_spec_88_, lean_object* v_n_89_){
_start:
{
uint32_t v_n_boxed_90_; lean_object* v_res_91_; 
v_n_boxed_90_ = lean_unbox_uint32(v_n_89_);
lean_dec(v_n_89_);
v_res_91_ = l_Float_Model_UnpackedFloat_ofInt32(v_spec_88_, v_n_boxed_90_);
lean_dec_ref(v_spec_88_);
return v_res_91_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofInt64(lean_object* v_spec_92_, uint64_t v_n_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_int64_to_int_sint(v_n_93_);
v___x_95_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_92_, v___x_94_);
lean_dec(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofInt64_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_92_ = stack[0].m_obj;
uint64_t v_n_93_ = stack[1].m_num;
lean_object* v_res_96_;
v_res_96_ = l_Float_Model_UnpackedFloat_ofInt64(v_spec_92_, v_n_93_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofInt64___boxed(lean_object* v_spec_97_, lean_object* v_n_98_){
_start:
{
uint64_t v_n_boxed_99_; lean_object* v_res_100_; 
v_n_boxed_99_ = lean_unbox_uint64(v_n_98_);
lean_dec_ref(v_n_98_);
v_res_100_ = l_Float_Model_UnpackedFloat_ofInt64(v_spec_97_, v_n_boxed_99_);
lean_dec_ref(v_spec_97_);
return v_res_100_;
}
}
lean_object* l_Float_Model_UnpackedFloat_ofISize(lean_object* v_spec_101_, size_t v_n_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_isize_to_int(v_n_102_);
v___x_104_ = l_Float_Model_UnpackedFloat_ofInt(v_spec_101_, v___x_103_);
lean_dec(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_ofISize_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_101_ = stack[0].m_obj;
size_t v_n_102_ = stack[1].m_num;
lean_object* v_res_105_;
v_res_105_ = l_Float_Model_UnpackedFloat_ofISize(v_spec_101_, v_n_102_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofISize___boxed(lean_object* v_spec_106_, lean_object* v_n_107_){
_start:
{
size_t v_n_boxed_108_; lean_object* v_res_109_; 
v_n_boxed_108_ = lean_unbox_usize(v_n_107_);
lean_dec(v_n_107_);
v_res_109_ = l_Float_Model_UnpackedFloat_ofISize(v_spec_106_, v_n_boxed_108_);
lean_dec_ref(v_spec_106_);
return v_res_109_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_OfNat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
