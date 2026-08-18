// Lean compiler output
// Module: Init.Data.UInt.BasicAux
// Imports: public import Init.Data.BitVec.BasicAux public import Init.Data.Fin.Basic import Init.Data.Nat.Div.Basic
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
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_uint8_of_nat(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
uint16_t lean_uint16_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_toFin(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toFin___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_ofNatClamp(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_ofNatClamp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_ofNatTruncate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_toUInt8(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_toFin(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toFin___boxed(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_ofNatClamp(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_ofNatClamp___boxed(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_ofNatTruncate___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Nat_toUInt16(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object*);
uint8_t lean_uint16_to_uint8(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object*);
uint16_t lean_uint8_to_uint16(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_toFin(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toFin___boxed(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_ofNatClamp(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_ofNatClamp___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_ofNatTruncate___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Nat_toUInt32(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object*);
uint16_t lean_uint32_to_uint16(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object*);
uint32_t lean_uint16_to_uint32(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instOfNat___boxed(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instAddUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddUInt32___closed__0 = (const lean_object*)&l_instAddUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddUInt32 = (const lean_object*)&l_instAddUInt32___closed__0_value;
static const lean_closure_object l_instSubUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubUInt32___closed__0 = (const lean_object*)&l_instSubUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubUInt32 = (const lean_object*)&l_instSubUInt32___closed__0_value;
LEAN_EXPORT lean_object* l_UInt64_toFin(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toFin___boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object*);
static lean_once_cell_t l_UInt64_ofNatClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_ofNatClamp___closed__0;
LEAN_EXPORT uint64_t l_UInt64_ofNatClamp(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_ofNatClamp___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_ofNatTruncate___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Nat_toUInt64(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object*);
uint8_t lean_uint64_to_uint8(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object*);
uint16_t lean_uint64_to_uint16(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object*);
uint32_t lean_uint64_to_uint32(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object*);
uint64_t lean_uint16_to_uint64(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_USize_toFin(size_t);
LEAN_EXPORT lean_object* l_USize_toFin___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object*);
static lean_once_cell_t l_USize_ofNatClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_ofNatClamp___closed__0;
static lean_once_cell_t l_USize_ofNatClamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_ofNatClamp___closed__1;
static lean_once_cell_t l_USize_ofNatClamp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_USize_ofNatClamp___closed__2;
LEAN_EXPORT size_t l_USize_ofNatClamp(lean_object*);
LEAN_EXPORT lean_object* l_USize_ofNatClamp___boxed(lean_object*);
LEAN_EXPORT size_t l_USize_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_USize_ofNatTruncate___boxed(lean_object*);
LEAN_EXPORT size_t l_Nat_toUSize(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_USize_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_USize_instOfNat___boxed(lean_object*);
static const lean_closure_object l_instAddUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddUSize___closed__0 = (const lean_object*)&l_instAddUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddUSize = (const lean_object*)&l_instAddUSize___closed__0_value;
static const lean_closure_object l_instSubUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubUSize___closed__0 = (const lean_object*)&l_instSubUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubUSize = (const lean_object*)&l_instSubUSize___closed__0_value;
LEAN_EXPORT lean_object* l_instLTUSize;
LEAN_EXPORT lean_object* l_instLEUSize;
LEAN_EXPORT uint8_t l_USize_decLt___aux__1(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_USize_decLe___aux__1(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_decLe___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_toFin(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_uint8_to_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toFin___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_x_boxed_4_; lean_object* v_res_5_; 
v_x_boxed_4_ = lean_unbox(v_x_3_);
v_res_5_ = l_UInt8_toFin(v_x_boxed_4_);
return v_res_5_;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofNatClamp(lean_object* v_n_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(256u);
v___x_8_ = lean_nat_dec_lt(v_n_6_, v___x_7_);
if (v___x_8_ == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 255;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = lean_uint8_of_nat(v_n_6_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_ofNatClamp___boxed(lean_object* v_n_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_UInt8_ofNatClamp(v_n_11_);
lean_dec(v_n_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofNatTruncate(lean_object* v_n_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_UInt8_ofNatClamp(v_n_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofNatTruncate___boxed(lean_object* v_n_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_UInt8_ofNatTruncate(v_n_16_);
lean_dec(v_n_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_Nat_toUInt8(lean_object* v_n_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = lean_uint8_of_nat(v_n_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object* v_n_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Nat_toUInt8(v_n_21_);
lean_dec(v_n_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object* v_n_25_){
_start:
{
uint8_t v_n_boxed_26_; lean_object* v_res_27_; 
v_n_boxed_26_ = lean_unbox(v_n_25_);
v_res_27_ = lean_uint8_to_nat(v_n_boxed_26_);
return v_res_27_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instOfNat(lean_object* v_n_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lean_uint8_of_nat(v_n_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instOfNat___boxed(lean_object* v_n_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_UInt8_instOfNat(v_n_30_);
lean_dec(v_n_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin(uint16_t v_x_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_uint16_to_nat(v_x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin___boxed(lean_object* v_x_35_){
_start:
{
uint16_t v_x_boxed_36_; lean_object* v_res_37_; 
v_x_boxed_36_ = lean_unbox(v_x_35_);
v_res_37_ = l_UInt16_toFin(v_x_boxed_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object* v_n_39_){
_start:
{
uint16_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = lean_uint16_of_nat(v_n_39_);
lean_dec(v_n_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofNatClamp(lean_object* v_n_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(65536u);
v___x_44_ = lean_nat_dec_lt(v_n_42_, v___x_43_);
if (v___x_44_ == 0)
{
uint16_t v___x_45_; 
v___x_45_ = 65535;
return v___x_45_;
}
else
{
uint16_t v___x_46_; 
v___x_46_ = lean_uint16_of_nat(v_n_42_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNatClamp___boxed(lean_object* v_n_47_){
_start:
{
uint16_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_UInt16_ofNatClamp(v_n_47_);
lean_dec(v_n_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofNatTruncate(lean_object* v_n_50_){
_start:
{
uint16_t v___x_51_; 
v___x_51_ = l_UInt16_ofNatClamp(v_n_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNatTruncate___boxed(lean_object* v_n_52_){
_start:
{
uint16_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_UInt16_ofNatTruncate(v_n_52_);
lean_dec(v_n_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint16_t l_Nat_toUInt16(lean_object* v_n_55_){
_start:
{
uint16_t v___x_56_; 
v___x_56_ = lean_uint16_of_nat(v_n_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object* v_n_57_){
_start:
{
uint16_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Nat_toUInt16(v_n_57_);
lean_dec(v_n_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object* v_n_61_){
_start:
{
uint16_t v_n_boxed_62_; lean_object* v_res_63_; 
v_n_boxed_62_ = lean_unbox(v_n_61_);
v_res_63_ = lean_uint16_to_nat(v_n_boxed_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object* v_a_65_){
_start:
{
uint16_t v_a_boxed_66_; uint8_t v_res_67_; lean_object* v_r_68_; 
v_a_boxed_66_ = lean_unbox(v_a_65_);
v_res_67_ = lean_uint16_to_uint8(v_a_boxed_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object* v_a_70_){
_start:
{
uint8_t v_a_boxed_71_; uint16_t v_res_72_; lean_object* v_r_73_; 
v_a_boxed_71_ = lean_unbox(v_a_70_);
v_res_72_ = lean_uint8_to_uint16(v_a_boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint16_t l_UInt16_instOfNat(lean_object* v_n_74_){
_start:
{
uint16_t v___x_75_; 
v___x_75_ = lean_uint16_of_nat(v_n_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instOfNat___boxed(lean_object* v_n_76_){
_start:
{
uint16_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_UInt16_instOfNat(v_n_76_);
lean_dec(v_n_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin(uint32_t v_x_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_uint32_to_nat(v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin___boxed(lean_object* v_x_81_){
_start:
{
uint32_t v_x_boxed_82_; lean_object* v_res_83_; 
v_x_boxed_82_ = lean_unbox_uint32(v_x_81_);
lean_dec(v_x_81_);
v_res_83_ = l_UInt32_toFin(v_x_boxed_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object* v_n_85_){
_start:
{
uint32_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = lean_uint32_of_nat(v_n_85_);
lean_dec(v_n_85_);
v_r_87_ = lean_box_uint32(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofNatClamp(lean_object* v_n_88_){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_cstr_to_nat("4294967296");
v___x_90_ = lean_nat_dec_lt(v_n_88_, v___x_89_);
if (v___x_90_ == 0)
{
uint32_t v___x_91_; 
v___x_91_ = 4294967295;
return v___x_91_;
}
else
{
uint32_t v___x_92_; 
v___x_92_ = lean_uint32_of_nat(v_n_88_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNatClamp___boxed(lean_object* v_n_93_){
_start:
{
uint32_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_UInt32_ofNatClamp(v_n_93_);
lean_dec(v_n_93_);
v_r_95_ = lean_box_uint32(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofNatTruncate(lean_object* v_n_96_){
_start:
{
uint32_t v___x_97_; 
v___x_97_ = l_UInt32_ofNatClamp(v_n_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNatTruncate___boxed(lean_object* v_n_98_){
_start:
{
uint32_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_UInt32_ofNatTruncate(v_n_98_);
lean_dec(v_n_98_);
v_r_100_ = lean_box_uint32(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint32_t l_Nat_toUInt32(lean_object* v_n_101_){
_start:
{
uint32_t v___x_102_; 
v___x_102_ = lean_uint32_of_nat(v_n_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object* v_n_103_){
_start:
{
uint32_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Nat_toUInt32(v_n_103_);
lean_dec(v_n_103_);
v_r_105_ = lean_box_uint32(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object* v_a_107_){
_start:
{
uint32_t v_a_boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_a_boxed_108_ = lean_unbox_uint32(v_a_107_);
lean_dec(v_a_107_);
v_res_109_ = lean_uint32_to_uint8(v_a_boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object* v_a_112_){
_start:
{
uint32_t v_a_boxed_113_; uint16_t v_res_114_; lean_object* v_r_115_; 
v_a_boxed_113_ = lean_unbox_uint32(v_a_112_);
lean_dec(v_a_112_);
v_res_114_ = lean_uint32_to_uint16(v_a_boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object* v_a_117_){
_start:
{
uint8_t v_a_boxed_118_; uint32_t v_res_119_; lean_object* v_r_120_; 
v_a_boxed_118_ = lean_unbox(v_a_117_);
v_res_119_ = lean_uint8_to_uint32(v_a_boxed_118_);
v_r_120_ = lean_box_uint32(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object* v_a_122_){
_start:
{
uint16_t v_a_boxed_123_; uint32_t v_res_124_; lean_object* v_r_125_; 
v_a_boxed_123_ = lean_unbox(v_a_122_);
v_res_124_ = lean_uint16_to_uint32(v_a_boxed_123_);
v_r_125_ = lean_box_uint32(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint32_t l_UInt32_instOfNat(lean_object* v_n_126_){
_start:
{
uint32_t v___x_127_; 
v___x_127_ = lean_uint32_of_nat(v_n_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instOfNat___boxed(lean_object* v_n_128_){
_start:
{
uint32_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_UInt32_instOfNat(v_n_128_);
lean_dec(v_n_128_);
v_r_130_ = lean_box_uint32(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object* v_a_133_, lean_object* v_b_134_){
_start:
{
uint32_t v_a_boxed_135_; uint32_t v_b_boxed_136_; uint32_t v_res_137_; lean_object* v_r_138_; 
v_a_boxed_135_ = lean_unbox_uint32(v_a_133_);
lean_dec(v_a_133_);
v_b_boxed_136_ = lean_unbox_uint32(v_b_134_);
lean_dec(v_b_134_);
v_res_137_ = lean_uint32_add(v_a_boxed_135_, v_b_boxed_136_);
v_r_138_ = lean_box_uint32(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object* v_a_141_, lean_object* v_b_142_){
_start:
{
uint32_t v_a_boxed_143_; uint32_t v_b_boxed_144_; uint32_t v_res_145_; lean_object* v_r_146_; 
v_a_boxed_143_ = lean_unbox_uint32(v_a_141_);
lean_dec(v_a_141_);
v_b_boxed_144_ = lean_unbox_uint32(v_b_142_);
lean_dec(v_b_142_);
v_res_145_ = lean_uint32_sub(v_a_boxed_143_, v_b_boxed_144_);
v_r_146_ = lean_box_uint32(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin(uint64_t v_x_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_uint64_to_nat(v_x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin___boxed(lean_object* v_x_153_){
_start:
{
uint64_t v_x_boxed_154_; lean_object* v_res_155_; 
v_x_boxed_154_ = lean_unbox_uint64(v_x_153_);
lean_dec_ref(v_x_153_);
v_res_155_ = l_UInt64_toFin(v_x_boxed_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object* v_n_157_){
_start:
{
uint64_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = lean_uint64_of_nat(v_n_157_);
lean_dec(v_n_157_);
v_r_159_ = lean_box_uint64(v_res_158_);
return v_r_159_;
}
}
static lean_object* _init_l_UInt64_ofNatClamp___closed__0(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_cstr_to_nat("18446744073709551616");
return v___x_160_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofNatClamp(lean_object* v_n_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_obj_once(&l_UInt64_ofNatClamp___closed__0, &l_UInt64_ofNatClamp___closed__0_once, _init_l_UInt64_ofNatClamp___closed__0);
v___x_163_ = lean_nat_dec_lt(v_n_161_, v___x_162_);
if (v___x_163_ == 0)
{
uint64_t v___x_164_; 
v___x_164_ = 18446744073709551615ULL;
return v___x_164_;
}
else
{
uint64_t v___x_165_; 
v___x_165_ = lean_uint64_of_nat(v_n_161_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNatClamp___boxed(lean_object* v_n_166_){
_start:
{
uint64_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_UInt64_ofNatClamp(v_n_166_);
lean_dec(v_n_166_);
v_r_168_ = lean_box_uint64(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofNatTruncate(lean_object* v_n_169_){
_start:
{
uint64_t v___x_170_; 
v___x_170_ = l_UInt64_ofNatClamp(v_n_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNatTruncate___boxed(lean_object* v_n_171_){
_start:
{
uint64_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_UInt64_ofNatTruncate(v_n_171_);
lean_dec(v_n_171_);
v_r_173_ = lean_box_uint64(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint64_t l_Nat_toUInt64(lean_object* v_n_174_){
_start:
{
uint64_t v___x_175_; 
v___x_175_ = lean_uint64_of_nat(v_n_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object* v_n_176_){
_start:
{
uint64_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Nat_toUInt64(v_n_176_);
lean_dec(v_n_176_);
v_r_178_ = lean_box_uint64(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object* v_n_180_){
_start:
{
uint64_t v_n_boxed_181_; lean_object* v_res_182_; 
v_n_boxed_181_ = lean_unbox_uint64(v_n_180_);
lean_dec_ref(v_n_180_);
v_res_182_ = lean_uint64_to_nat(v_n_boxed_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object* v_a_184_){
_start:
{
uint64_t v_a_boxed_185_; uint8_t v_res_186_; lean_object* v_r_187_; 
v_a_boxed_185_ = lean_unbox_uint64(v_a_184_);
lean_dec_ref(v_a_184_);
v_res_186_ = lean_uint64_to_uint8(v_a_boxed_185_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object* v_a_189_){
_start:
{
uint64_t v_a_boxed_190_; uint16_t v_res_191_; lean_object* v_r_192_; 
v_a_boxed_190_ = lean_unbox_uint64(v_a_189_);
lean_dec_ref(v_a_189_);
v_res_191_ = lean_uint64_to_uint16(v_a_boxed_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object* v_a_194_){
_start:
{
uint64_t v_a_boxed_195_; uint32_t v_res_196_; lean_object* v_r_197_; 
v_a_boxed_195_ = lean_unbox_uint64(v_a_194_);
lean_dec_ref(v_a_194_);
v_res_196_ = lean_uint64_to_uint32(v_a_boxed_195_);
v_r_197_ = lean_box_uint32(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object* v_a_199_){
_start:
{
uint8_t v_a_boxed_200_; uint64_t v_res_201_; lean_object* v_r_202_; 
v_a_boxed_200_ = lean_unbox(v_a_199_);
v_res_201_ = lean_uint8_to_uint64(v_a_boxed_200_);
v_r_202_ = lean_box_uint64(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object* v_a_204_){
_start:
{
uint16_t v_a_boxed_205_; uint64_t v_res_206_; lean_object* v_r_207_; 
v_a_boxed_205_ = lean_unbox(v_a_204_);
v_res_206_ = lean_uint16_to_uint64(v_a_boxed_205_);
v_r_207_ = lean_box_uint64(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object* v_a_209_){
_start:
{
uint32_t v_a_boxed_210_; uint64_t v_res_211_; lean_object* v_r_212_; 
v_a_boxed_210_ = lean_unbox_uint32(v_a_209_);
lean_dec(v_a_209_);
v_res_211_ = lean_uint32_to_uint64(v_a_boxed_210_);
v_r_212_ = lean_box_uint64(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint64_t l_UInt64_instOfNat(lean_object* v_n_213_){
_start:
{
uint64_t v___x_214_; 
v___x_214_ = lean_uint64_of_nat(v_n_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instOfNat___boxed(lean_object* v_n_215_){
_start:
{
uint64_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_UInt64_instOfNat(v_n_215_);
lean_dec(v_n_215_);
v_r_217_ = lean_box_uint64(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin(size_t v_x_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_usize_to_nat(v_x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin___boxed(lean_object* v_x_220_){
_start:
{
size_t v_x_boxed_221_; lean_object* v_res_222_; 
v_x_boxed_221_ = lean_unbox_usize(v_x_220_);
lean_dec(v_x_220_);
v_res_222_ = l_USize_toFin(v_x_boxed_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object* v_n_224_){
_start:
{
size_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = lean_usize_of_nat(v_n_224_);
lean_dec(v_n_224_);
v_r_226_ = lean_box_usize(v_res_225_);
return v_r_226_;
}
}
static lean_object* _init_l_USize_ofNatClamp___closed__0(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = l_System_Platform_numBits;
v___x_228_ = lean_unsigned_to_nat(2u);
v___x_229_ = lean_nat_pow(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_USize_ofNatClamp___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_obj_once(&l_USize_ofNatClamp___closed__0, &l_USize_ofNatClamp___closed__0_once, _init_l_USize_ofNatClamp___closed__0);
v___x_232_ = lean_nat_sub(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static size_t _init_l_USize_ofNatClamp___closed__2(void){
_start:
{
lean_object* v___x_233_; size_t v___x_234_; 
v___x_233_ = lean_obj_once(&l_USize_ofNatClamp___closed__1, &l_USize_ofNatClamp___closed__1_once, _init_l_USize_ofNatClamp___closed__1);
v___x_234_ = lean_usize_of_nat(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT size_t l_USize_ofNatClamp(lean_object* v_n_235_){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_obj_once(&l_USize_ofNatClamp___closed__0, &l_USize_ofNatClamp___closed__0_once, _init_l_USize_ofNatClamp___closed__0);
v___x_237_ = lean_nat_dec_lt(v_n_235_, v___x_236_);
if (v___x_237_ == 0)
{
size_t v___x_238_; 
v___x_238_ = lean_usize_once(&l_USize_ofNatClamp___closed__2, &l_USize_ofNatClamp___closed__2_once, _init_l_USize_ofNatClamp___closed__2);
return v___x_238_;
}
else
{
size_t v___x_239_; 
v___x_239_ = lean_usize_of_nat(v_n_235_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_USize_ofNatClamp___boxed(lean_object* v_n_240_){
_start:
{
size_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_USize_ofNatClamp(v_n_240_);
lean_dec(v_n_240_);
v_r_242_ = lean_box_usize(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT size_t l_USize_ofNatTruncate(lean_object* v_n_243_){
_start:
{
size_t v___x_244_; 
v___x_244_ = l_USize_ofNatClamp(v_n_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNatTruncate___boxed(lean_object* v_n_245_){
_start:
{
size_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_USize_ofNatTruncate(v_n_245_);
lean_dec(v_n_245_);
v_r_247_ = lean_box_usize(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT size_t l_Nat_toUSize(lean_object* v_n_248_){
_start:
{
size_t v___x_249_; 
v___x_249_ = lean_usize_of_nat(v_n_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object* v_n_250_){
_start:
{
size_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Nat_toUSize(v_n_250_);
lean_dec(v_n_250_);
v_r_252_ = lean_box_usize(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object* v_n_254_){
_start:
{
size_t v_n_boxed_255_; lean_object* v_res_256_; 
v_n_boxed_255_ = lean_unbox_usize(v_n_254_);
lean_dec(v_n_254_);
v_res_256_ = lean_usize_to_nat(v_n_boxed_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
size_t v_a_boxed_261_; size_t v_b_boxed_262_; size_t v_res_263_; lean_object* v_r_264_; 
v_a_boxed_261_ = lean_unbox_usize(v_a_259_);
lean_dec(v_a_259_);
v_b_boxed_262_ = lean_unbox_usize(v_b_260_);
lean_dec(v_b_260_);
v_res_263_ = lean_usize_add(v_a_boxed_261_, v_b_boxed_262_);
v_r_264_ = lean_box_usize(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
size_t v_a_boxed_269_; size_t v_b_boxed_270_; size_t v_res_271_; lean_object* v_r_272_; 
v_a_boxed_269_ = lean_unbox_usize(v_a_267_);
lean_dec(v_a_267_);
v_b_boxed_270_ = lean_unbox_usize(v_b_268_);
lean_dec(v_b_268_);
v_res_271_ = lean_usize_sub(v_a_boxed_269_, v_b_boxed_270_);
v_r_272_ = lean_box_usize(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT size_t l_USize_instOfNat(lean_object* v_n_273_){
_start:
{
size_t v___x_274_; 
v___x_274_ = lean_usize_of_nat(v_n_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_USize_instOfNat___boxed(lean_object* v_n_275_){
_start:
{
size_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_USize_instOfNat(v_n_275_);
lean_dec(v_n_275_);
v_r_277_ = lean_box_usize(v_res_276_);
return v_r_277_;
}
}
static lean_object* _init_l_instLTUSize(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_box(0);
return v___x_282_;
}
}
static lean_object* _init_l_instLEUSize(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_box(0);
return v___x_283_;
}
}
LEAN_EXPORT uint8_t l_USize_decLt___aux__1(size_t v_a_284_, size_t v_b_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_usize_to_nat(v_a_284_);
v___x_287_ = lean_usize_to_nat(v_b_285_);
v___x_288_ = lean_nat_dec_lt(v___x_286_, v___x_287_);
lean_dec(v___x_287_);
lean_dec(v___x_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___aux__1___boxed(lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
size_t v_a_boxed_291_; size_t v_b_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_a_boxed_291_ = lean_unbox_usize(v_a_289_);
lean_dec(v_a_289_);
v_b_boxed_292_ = lean_unbox_usize(v_b_290_);
lean_dec(v_b_290_);
v_res_293_ = l_USize_decLt___aux__1(v_a_boxed_291_, v_b_boxed_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object* v_a_297_, lean_object* v_b_298_){
_start:
{
size_t v_a_boxed_299_; size_t v_b_boxed_300_; uint8_t v_res_301_; lean_object* v_r_302_; 
v_a_boxed_299_ = lean_unbox_usize(v_a_297_);
lean_dec(v_a_297_);
v_b_boxed_300_ = lean_unbox_usize(v_b_298_);
lean_dec(v_b_298_);
v_res_301_ = lean_usize_dec_lt(v_a_boxed_299_, v_b_boxed_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_USize_decLe___aux__1(size_t v_a_303_, size_t v_b_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_usize_to_nat(v_a_303_);
v___x_306_ = lean_usize_to_nat(v_b_304_);
v___x_307_ = lean_nat_dec_le(v___x_305_, v___x_306_);
lean_dec(v___x_306_);
lean_dec(v___x_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___aux__1___boxed(lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
size_t v_a_boxed_310_; size_t v_b_boxed_311_; uint8_t v_res_312_; lean_object* v_r_313_; 
v_a_boxed_310_ = lean_unbox_usize(v_a_308_);
lean_dec(v_a_308_);
v_b_boxed_311_ = lean_unbox_usize(v_b_309_);
lean_dec(v_b_309_);
v_res_312_ = l_USize_decLe___aux__1(v_a_boxed_310_, v_b_boxed_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
size_t v_a_boxed_318_; size_t v_b_boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_a_boxed_318_ = lean_unbox_usize(v_a_316_);
lean_dec(v_a_316_);
v_b_boxed_319_ = lean_unbox_usize(v_b_317_);
lean_dec(v_b_317_);
v_res_320_ = lean_usize_dec_le(v_a_boxed_318_, v_b_boxed_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instLTUSize = _init_l_instLTUSize();
lean_mark_persistent(l_instLTUSize);
l_instLEUSize = _init_l_instLEUSize();
lean_mark_persistent(l_instLEUSize);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_UInt_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_UInt_BasicAux(builtin);
}
#ifdef __cplusplus
}
#endif
