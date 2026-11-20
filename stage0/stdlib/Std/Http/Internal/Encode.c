// Lean compiler output
// Module: Std.Http.Internal.Encode
// Imports: public import Init.Data.ByteArray.Basic public import Std.Http.Data.Version import Init.Omega
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11String___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instEncodeV11String___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instEncodeV11String___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instEncodeV11String___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11String___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instEncodeV11String = (const lean_object*)&l_Std_Http_Internal_instEncodeV11String___closed__0_value;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Char___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Internal_instEncodeV11Char___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Char___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Char___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Char___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instEncodeV11Char___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instEncodeV11Char___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instEncodeV11Char___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Char___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instEncodeV11Char = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Char___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendNat___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instEncodeV11Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_appendNat___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instEncodeV11Nat___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instEncodeV11Nat = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Nat___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Internal_appendHex___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendHex___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendHex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendHex___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__5;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__6 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__6_value;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__8;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__9 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__9_value;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10;
static lean_once_cell_t l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instEncodeV11Version___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instEncodeV11Version = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11___redArg(lean_object* v_inst_1_){
_start:
{
lean_inc_ref(v_inst_1_);
return v_inst_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11___redArg___boxed(lean_object* v_inst_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11___redArg(v_inst_2_);
lean_dec_ref(v_inst_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11(lean_object* v_t_4_, lean_object* v_inst_5_){
_start:
{
lean_inc_ref(v_inst_5_);
return v_inst_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11___boxed(lean_object* v_t_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_Http_Internal_instHAppendByteArrayOfEncodeV11(v_t_6_, v_inst_7_);
lean_dec_ref(v_inst_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11String___lam__0(lean_object* v_out_9_, lean_object* v_s_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; 
v___x_11_ = lean_string_to_utf8(v_s_10_);
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_byte_array_size(v_out_9_);
v___x_14_ = lean_byte_array_size(v___x_11_);
v___x_15_ = 0;
v___x_16_ = lean_byte_array_copy_slice(v___x_11_, v___x_12_, v_out_9_, v___x_13_, v___x_14_, v___x_15_);
lean_dec_ref(v___x_11_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Char___lam__0(lean_object* v_out_20_, uint32_t v_c_21_){
_start:
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 128;
v___x_23_ = lean_uint32_dec_lt(v_c_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_24_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Char___lam__0___closed__0));
v___x_25_ = lean_string_push(v___x_24_, v_c_21_);
v___x_26_ = lean_string_to_utf8(v___x_25_);
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_byte_array_size(v_out_20_);
v___x_29_ = lean_byte_array_size(v___x_26_);
v___x_30_ = lean_byte_array_copy_slice(v___x_26_, v___x_27_, v_out_20_, v___x_28_, v___x_29_, v___x_23_);
lean_dec_ref(v___x_26_);
return v___x_30_;
}
else
{
uint8_t v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_uint32_to_uint8(v_c_21_);
v___x_32_ = lean_byte_array_push(v_out_20_, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Char___lam__0___boxed(lean_object* v_out_33_, lean_object* v_c_34_){
_start:
{
uint32_t v_c_boxed_35_; lean_object* v_res_36_; 
v_c_boxed_35_ = lean_unbox_uint32(v_c_34_);
lean_dec(v_c_34_);
v_res_36_ = l_Std_Http_Internal_instEncodeV11Char___lam__0(v_out_33_, v_c_boxed_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendNat(lean_object* v_out_39_, lean_object* v_n_40_){
_start:
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(10u);
v___x_42_ = lean_nat_dec_lt(v_n_40_, v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; uint8_t v___x_48_; lean_object* v___x_49_; 
v___x_43_ = lean_nat_div(v_n_40_, v___x_41_);
v___x_44_ = l_Std_Http_Internal_appendNat(v_out_39_, v___x_43_);
lean_dec(v___x_43_);
v___x_45_ = 48;
v___x_46_ = lean_nat_mod(v_n_40_, v___x_41_);
v___x_47_ = lean_uint8_of_nat(v___x_46_);
lean_dec(v___x_46_);
v___x_48_ = lean_uint8_add(v___x_45_, v___x_47_);
v___x_49_ = lean_byte_array_push(v___x_44_, v___x_48_);
return v___x_49_;
}
else
{
uint8_t v___x_50_; uint8_t v___x_51_; uint8_t v___x_52_; lean_object* v___x_53_; 
v___x_50_ = 48;
v___x_51_ = lean_uint8_of_nat(v_n_40_);
v___x_52_ = lean_uint8_add(v___x_50_, v___x_51_);
v___x_53_ = lean_byte_array_push(v_out_39_, v___x_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendNat___boxed(lean_object* v_out_54_, lean_object* v_n_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Http_Internal_appendNat(v_out_54_, v_n_55_);
lean_dec(v_n_55_);
return v_res_56_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_appendHex___lam__0(lean_object* v_d_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(10u);
v___x_61_ = lean_nat_dec_lt(v_d_59_, v___x_60_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; uint8_t v___x_65_; 
v___x_62_ = 97;
v___x_63_ = lean_nat_sub(v_d_59_, v___x_60_);
v___x_64_ = lean_uint8_of_nat(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_uint8_add(v___x_62_, v___x_64_);
return v___x_65_;
}
else
{
uint8_t v___x_66_; uint8_t v___x_67_; uint8_t v___x_68_; 
v___x_66_ = 48;
v___x_67_ = lean_uint8_of_nat(v_d_59_);
v___x_68_ = lean_uint8_add(v___x_66_, v___x_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendHex___lam__0___boxed(lean_object* v_d_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_Http_Internal_appendHex___lam__0(v_d_69_);
lean_dec(v_d_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendHex(lean_object* v_out_72_, lean_object* v_n_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(16u);
v___x_75_ = lean_nat_dec_lt(v_n_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; 
v___x_76_ = lean_unsigned_to_nat(4u);
v___x_77_ = lean_nat_shiftr(v_n_73_, v___x_76_);
v___x_78_ = l_Std_Http_Internal_appendHex(v_out_72_, v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = lean_nat_mod(v_n_73_, v___x_74_);
v___x_80_ = l_Std_Http_Internal_appendHex___lam__0(v___x_79_);
lean_dec(v___x_79_);
v___x_81_ = lean_byte_array_push(v___x_78_, v___x_80_);
return v___x_81_;
}
else
{
uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_82_ = l_Std_Http_Internal_appendHex___lam__0(v_n_73_);
v___x_83_ = lean_byte_array_push(v_out_72_, v___x_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendHex___boxed(lean_object* v_out_84_, lean_object* v_n_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Http_Internal_appendHex(v_out_84_, v_n_85_);
lean_dec(v_n_85_);
return v_res_86_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0));
v___x_89_ = lean_string_to_utf8(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1);
v___x_91_ = lean_byte_array_size(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3));
v___x_94_ = lean_string_to_utf8(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__5(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4);
v___x_96_ = lean_byte_array_size(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__6));
v___x_99_ = lean_string_to_utf8(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__8(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7);
v___x_101_ = lean_byte_array_size(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__9));
v___x_104_ = lean_string_to_utf8(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__11(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10);
v___x_106_ = lean_byte_array_size(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0(lean_object* v_out_107_, uint8_t v_x_108_){
_start:
{
switch(v_x_108_)
{
case 0:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; 
v___x_109_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_byte_array_size(v_out_107_);
v___x_112_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2);
v___x_113_ = 0;
v___x_114_ = lean_byte_array_copy_slice(v___x_109_, v___x_110_, v_out_107_, v___x_111_, v___x_112_, v___x_113_);
return v___x_114_;
}
case 1:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; 
v___x_115_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__4);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_byte_array_size(v_out_107_);
v___x_118_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__5, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__5_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__5);
v___x_119_ = 0;
v___x_120_ = lean_byte_array_copy_slice(v___x_115_, v___x_116_, v_out_107_, v___x_117_, v___x_118_, v___x_119_);
return v___x_120_;
}
case 2:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; 
v___x_121_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__7);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_byte_array_size(v_out_107_);
v___x_124_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__8, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__8_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__8);
v___x_125_ = 0;
v___x_126_ = lean_byte_array_copy_slice(v___x_121_, v___x_122_, v_out_107_, v___x_123_, v___x_124_, v___x_125_);
return v___x_126_;
}
default: 
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; 
v___x_127_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__10);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_byte_array_size(v_out_107_);
v___x_130_ = lean_obj_once(&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__11, &l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__11_once, _init_l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__11);
v___x_131_ = 0;
v___x_132_ = lean_byte_array_copy_slice(v___x_127_, v___x_128_, v_out_107_, v___x_129_, v___x_130_, v___x_131_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed(lean_object* v_out_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_x_195__boxed_135_; lean_object* v_res_136_; 
v_x_195__boxed_135_ = lean_unbox(v_x_134_);
v_res_136_ = l_Std_Http_Internal_instEncodeV11Version___lam__0(v_out_133_, v_x_195__boxed_135_);
return v_res_136_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Version(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Version(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_Encode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_Encode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_Encode(builtin);
}
#ifdef __cplusplus
}
#endif
