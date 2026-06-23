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
static lean_once_cell_t l_UInt8_ofNatClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_UInt8_ofNatClamp___closed__0;
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
static lean_once_cell_t l_UInt16_ofNatClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_UInt16_ofNatClamp___closed__0;
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
static lean_once_cell_t l_UInt32_ofNatClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_UInt32_ofNatClamp___closed__0;
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
static lean_once_cell_t l_UInt64_ofNatClamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_ofNatClamp___closed__1;
static lean_once_cell_t l_UInt64_ofNatClamp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_UInt64_ofNatClamp___closed__2;
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
static uint8_t _init_l_UInt8_ofNatClamp___closed__0(void){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(255u);
v___x_7_ = lean_uint8_of_nat(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofNatClamp(lean_object* v_n_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(256u);
v___x_10_ = lean_nat_dec_lt(v_n_8_, v___x_9_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
v___x_11_ = lean_uint8_once(&l_UInt8_ofNatClamp___closed__0, &l_UInt8_ofNatClamp___closed__0_once, _init_l_UInt8_ofNatClamp___closed__0);
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = lean_uint8_of_nat(v_n_8_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_ofNatClamp___boxed(lean_object* v_n_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_UInt8_ofNatClamp(v_n_13_);
lean_dec(v_n_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofNatTruncate(lean_object* v_n_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_UInt8_ofNatClamp(v_n_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofNatTruncate___boxed(lean_object* v_n_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_UInt8_ofNatTruncate(v_n_18_);
lean_dec(v_n_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint8_t l_Nat_toUInt8(lean_object* v_n_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = lean_uint8_of_nat(v_n_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object* v_n_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Nat_toUInt8(v_n_23_);
lean_dec(v_n_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object* v_n_27_){
_start:
{
uint8_t v_n_boxed_28_; lean_object* v_res_29_; 
v_n_boxed_28_ = lean_unbox(v_n_27_);
v_res_29_ = lean_uint8_to_nat(v_n_boxed_28_);
return v_res_29_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instOfNat(lean_object* v_n_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_uint8_of_nat(v_n_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instOfNat___boxed(lean_object* v_n_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_UInt8_instOfNat(v_n_32_);
lean_dec(v_n_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin(uint16_t v_x_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_uint16_to_nat(v_x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin___boxed(lean_object* v_x_37_){
_start:
{
uint16_t v_x_boxed_38_; lean_object* v_res_39_; 
v_x_boxed_38_ = lean_unbox(v_x_37_);
v_res_39_ = l_UInt16_toFin(v_x_boxed_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object* v_n_41_){
_start:
{
uint16_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lean_uint16_of_nat(v_n_41_);
lean_dec(v_n_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
static uint16_t _init_l_UInt16_ofNatClamp___closed__0(void){
_start:
{
lean_object* v___x_44_; uint16_t v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(65535u);
v___x_45_ = lean_uint16_of_nat(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofNatClamp(lean_object* v_n_46_){
_start:
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(65536u);
v___x_48_ = lean_nat_dec_lt(v_n_46_, v___x_47_);
if (v___x_48_ == 0)
{
uint16_t v___x_49_; 
v___x_49_ = lean_uint16_once(&l_UInt16_ofNatClamp___closed__0, &l_UInt16_ofNatClamp___closed__0_once, _init_l_UInt16_ofNatClamp___closed__0);
return v___x_49_;
}
else
{
uint16_t v___x_50_; 
v___x_50_ = lean_uint16_of_nat(v_n_46_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNatClamp___boxed(lean_object* v_n_51_){
_start:
{
uint16_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_UInt16_ofNatClamp(v_n_51_);
lean_dec(v_n_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofNatTruncate(lean_object* v_n_54_){
_start:
{
uint16_t v___x_55_; 
v___x_55_ = l_UInt16_ofNatClamp(v_n_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNatTruncate___boxed(lean_object* v_n_56_){
_start:
{
uint16_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_UInt16_ofNatTruncate(v_n_56_);
lean_dec(v_n_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint16_t l_Nat_toUInt16(lean_object* v_n_59_){
_start:
{
uint16_t v___x_60_; 
v___x_60_ = lean_uint16_of_nat(v_n_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object* v_n_61_){
_start:
{
uint16_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Nat_toUInt16(v_n_61_);
lean_dec(v_n_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object* v_n_65_){
_start:
{
uint16_t v_n_boxed_66_; lean_object* v_res_67_; 
v_n_boxed_66_ = lean_unbox(v_n_65_);
v_res_67_ = lean_uint16_to_nat(v_n_boxed_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object* v_a_69_){
_start:
{
uint16_t v_a_boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_a_boxed_70_ = lean_unbox(v_a_69_);
v_res_71_ = lean_uint16_to_uint8(v_a_boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object* v_a_74_){
_start:
{
uint8_t v_a_boxed_75_; uint16_t v_res_76_; lean_object* v_r_77_; 
v_a_boxed_75_ = lean_unbox(v_a_74_);
v_res_76_ = lean_uint8_to_uint16(v_a_boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint16_t l_UInt16_instOfNat(lean_object* v_n_78_){
_start:
{
uint16_t v___x_79_; 
v___x_79_ = lean_uint16_of_nat(v_n_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instOfNat___boxed(lean_object* v_n_80_){
_start:
{
uint16_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_UInt16_instOfNat(v_n_80_);
lean_dec(v_n_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin(uint32_t v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_uint32_to_nat(v_x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin___boxed(lean_object* v_x_85_){
_start:
{
uint32_t v_x_boxed_86_; lean_object* v_res_87_; 
v_x_boxed_86_ = lean_unbox_uint32(v_x_85_);
lean_dec(v_x_85_);
v_res_87_ = l_UInt32_toFin(v_x_boxed_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object* v_n_89_){
_start:
{
uint32_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = lean_uint32_of_nat(v_n_89_);
lean_dec(v_n_89_);
v_r_91_ = lean_box_uint32(v_res_90_);
return v_r_91_;
}
}
static uint32_t _init_l_UInt32_ofNatClamp___closed__0(void){
_start:
{
lean_object* v___x_92_; uint32_t v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(4294967295u);
v___x_93_ = lean_uint32_of_nat(v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofNatClamp(lean_object* v_n_94_){
_start:
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_cstr_to_nat("4294967296");
v___x_96_ = lean_nat_dec_lt(v_n_94_, v___x_95_);
if (v___x_96_ == 0)
{
uint32_t v___x_97_; 
v___x_97_ = lean_uint32_once(&l_UInt32_ofNatClamp___closed__0, &l_UInt32_ofNatClamp___closed__0_once, _init_l_UInt32_ofNatClamp___closed__0);
return v___x_97_;
}
else
{
uint32_t v___x_98_; 
v___x_98_ = lean_uint32_of_nat(v_n_94_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNatClamp___boxed(lean_object* v_n_99_){
_start:
{
uint32_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_UInt32_ofNatClamp(v_n_99_);
lean_dec(v_n_99_);
v_r_101_ = lean_box_uint32(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofNatTruncate(lean_object* v_n_102_){
_start:
{
uint32_t v___x_103_; 
v___x_103_ = l_UInt32_ofNatClamp(v_n_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNatTruncate___boxed(lean_object* v_n_104_){
_start:
{
uint32_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_UInt32_ofNatTruncate(v_n_104_);
lean_dec(v_n_104_);
v_r_106_ = lean_box_uint32(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint32_t l_Nat_toUInt32(lean_object* v_n_107_){
_start:
{
uint32_t v___x_108_; 
v___x_108_ = lean_uint32_of_nat(v_n_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object* v_n_109_){
_start:
{
uint32_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Nat_toUInt32(v_n_109_);
lean_dec(v_n_109_);
v_r_111_ = lean_box_uint32(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object* v_a_113_){
_start:
{
uint32_t v_a_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_a_boxed_114_ = lean_unbox_uint32(v_a_113_);
lean_dec(v_a_113_);
v_res_115_ = lean_uint32_to_uint8(v_a_boxed_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object* v_a_118_){
_start:
{
uint32_t v_a_boxed_119_; uint16_t v_res_120_; lean_object* v_r_121_; 
v_a_boxed_119_ = lean_unbox_uint32(v_a_118_);
lean_dec(v_a_118_);
v_res_120_ = lean_uint32_to_uint16(v_a_boxed_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object* v_a_123_){
_start:
{
uint8_t v_a_boxed_124_; uint32_t v_res_125_; lean_object* v_r_126_; 
v_a_boxed_124_ = lean_unbox(v_a_123_);
v_res_125_ = lean_uint8_to_uint32(v_a_boxed_124_);
v_r_126_ = lean_box_uint32(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object* v_a_128_){
_start:
{
uint16_t v_a_boxed_129_; uint32_t v_res_130_; lean_object* v_r_131_; 
v_a_boxed_129_ = lean_unbox(v_a_128_);
v_res_130_ = lean_uint16_to_uint32(v_a_boxed_129_);
v_r_131_ = lean_box_uint32(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint32_t l_UInt32_instOfNat(lean_object* v_n_132_){
_start:
{
uint32_t v___x_133_; 
v___x_133_ = lean_uint32_of_nat(v_n_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instOfNat___boxed(lean_object* v_n_134_){
_start:
{
uint32_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_UInt32_instOfNat(v_n_134_);
lean_dec(v_n_134_);
v_r_136_ = lean_box_uint32(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
uint32_t v_a_boxed_141_; uint32_t v_b_boxed_142_; uint32_t v_res_143_; lean_object* v_r_144_; 
v_a_boxed_141_ = lean_unbox_uint32(v_a_139_);
lean_dec(v_a_139_);
v_b_boxed_142_ = lean_unbox_uint32(v_b_140_);
lean_dec(v_b_140_);
v_res_143_ = lean_uint32_add(v_a_boxed_141_, v_b_boxed_142_);
v_r_144_ = lean_box_uint32(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
uint32_t v_a_boxed_149_; uint32_t v_b_boxed_150_; uint32_t v_res_151_; lean_object* v_r_152_; 
v_a_boxed_149_ = lean_unbox_uint32(v_a_147_);
lean_dec(v_a_147_);
v_b_boxed_150_ = lean_unbox_uint32(v_b_148_);
lean_dec(v_b_148_);
v_res_151_ = lean_uint32_sub(v_a_boxed_149_, v_b_boxed_150_);
v_r_152_ = lean_box_uint32(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin(uint64_t v_x_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_uint64_to_nat(v_x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin___boxed(lean_object* v_x_159_){
_start:
{
uint64_t v_x_boxed_160_; lean_object* v_res_161_; 
v_x_boxed_160_ = lean_unbox_uint64(v_x_159_);
lean_dec_ref(v_x_159_);
v_res_161_ = l_UInt64_toFin(v_x_boxed_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object* v_n_163_){
_start:
{
uint64_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = lean_uint64_of_nat(v_n_163_);
lean_dec(v_n_163_);
v_r_165_ = lean_box_uint64(v_res_164_);
return v_r_165_;
}
}
static lean_object* _init_l_UInt64_ofNatClamp___closed__0(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_cstr_to_nat("18446744073709551616");
return v___x_166_;
}
}
static lean_object* _init_l_UInt64_ofNatClamp___closed__1(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_cstr_to_nat("18446744073709551615");
return v___x_167_;
}
}
static uint64_t _init_l_UInt64_ofNatClamp___closed__2(void){
_start:
{
lean_object* v___x_168_; uint64_t v___x_169_; 
v___x_168_ = lean_obj_once(&l_UInt64_ofNatClamp___closed__1, &l_UInt64_ofNatClamp___closed__1_once, _init_l_UInt64_ofNatClamp___closed__1);
v___x_169_ = lean_uint64_of_nat(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofNatClamp(lean_object* v_n_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_obj_once(&l_UInt64_ofNatClamp___closed__0, &l_UInt64_ofNatClamp___closed__0_once, _init_l_UInt64_ofNatClamp___closed__0);
v___x_172_ = lean_nat_dec_lt(v_n_170_, v___x_171_);
if (v___x_172_ == 0)
{
uint64_t v___x_173_; 
v___x_173_ = lean_uint64_once(&l_UInt64_ofNatClamp___closed__2, &l_UInt64_ofNatClamp___closed__2_once, _init_l_UInt64_ofNatClamp___closed__2);
return v___x_173_;
}
else
{
uint64_t v___x_174_; 
v___x_174_ = lean_uint64_of_nat(v_n_170_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNatClamp___boxed(lean_object* v_n_175_){
_start:
{
uint64_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_UInt64_ofNatClamp(v_n_175_);
lean_dec(v_n_175_);
v_r_177_ = lean_box_uint64(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofNatTruncate(lean_object* v_n_178_){
_start:
{
uint64_t v___x_179_; 
v___x_179_ = l_UInt64_ofNatClamp(v_n_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNatTruncate___boxed(lean_object* v_n_180_){
_start:
{
uint64_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_UInt64_ofNatTruncate(v_n_180_);
lean_dec(v_n_180_);
v_r_182_ = lean_box_uint64(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint64_t l_Nat_toUInt64(lean_object* v_n_183_){
_start:
{
uint64_t v___x_184_; 
v___x_184_ = lean_uint64_of_nat(v_n_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object* v_n_185_){
_start:
{
uint64_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Nat_toUInt64(v_n_185_);
lean_dec(v_n_185_);
v_r_187_ = lean_box_uint64(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object* v_n_189_){
_start:
{
uint64_t v_n_boxed_190_; lean_object* v_res_191_; 
v_n_boxed_190_ = lean_unbox_uint64(v_n_189_);
lean_dec_ref(v_n_189_);
v_res_191_ = lean_uint64_to_nat(v_n_boxed_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object* v_a_193_){
_start:
{
uint64_t v_a_boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_a_boxed_194_ = lean_unbox_uint64(v_a_193_);
lean_dec_ref(v_a_193_);
v_res_195_ = lean_uint64_to_uint8(v_a_boxed_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object* v_a_198_){
_start:
{
uint64_t v_a_boxed_199_; uint16_t v_res_200_; lean_object* v_r_201_; 
v_a_boxed_199_ = lean_unbox_uint64(v_a_198_);
lean_dec_ref(v_a_198_);
v_res_200_ = lean_uint64_to_uint16(v_a_boxed_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object* v_a_203_){
_start:
{
uint64_t v_a_boxed_204_; uint32_t v_res_205_; lean_object* v_r_206_; 
v_a_boxed_204_ = lean_unbox_uint64(v_a_203_);
lean_dec_ref(v_a_203_);
v_res_205_ = lean_uint64_to_uint32(v_a_boxed_204_);
v_r_206_ = lean_box_uint32(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object* v_a_208_){
_start:
{
uint8_t v_a_boxed_209_; uint64_t v_res_210_; lean_object* v_r_211_; 
v_a_boxed_209_ = lean_unbox(v_a_208_);
v_res_210_ = lean_uint8_to_uint64(v_a_boxed_209_);
v_r_211_ = lean_box_uint64(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object* v_a_213_){
_start:
{
uint16_t v_a_boxed_214_; uint64_t v_res_215_; lean_object* v_r_216_; 
v_a_boxed_214_ = lean_unbox(v_a_213_);
v_res_215_ = lean_uint16_to_uint64(v_a_boxed_214_);
v_r_216_ = lean_box_uint64(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object* v_a_218_){
_start:
{
uint32_t v_a_boxed_219_; uint64_t v_res_220_; lean_object* v_r_221_; 
v_a_boxed_219_ = lean_unbox_uint32(v_a_218_);
lean_dec(v_a_218_);
v_res_220_ = lean_uint32_to_uint64(v_a_boxed_219_);
v_r_221_ = lean_box_uint64(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint64_t l_UInt64_instOfNat(lean_object* v_n_222_){
_start:
{
uint64_t v___x_223_; 
v___x_223_ = lean_uint64_of_nat(v_n_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instOfNat___boxed(lean_object* v_n_224_){
_start:
{
uint64_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_UInt64_instOfNat(v_n_224_);
lean_dec(v_n_224_);
v_r_226_ = lean_box_uint64(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin(size_t v_x_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_usize_to_nat(v_x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin___boxed(lean_object* v_x_229_){
_start:
{
size_t v_x_boxed_230_; lean_object* v_res_231_; 
v_x_boxed_230_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_res_231_ = l_USize_toFin(v_x_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object* v_n_233_){
_start:
{
size_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = lean_usize_of_nat(v_n_233_);
lean_dec(v_n_233_);
v_r_235_ = lean_box_usize(v_res_234_);
return v_r_235_;
}
}
static lean_object* _init_l_USize_ofNatClamp___closed__0(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = l_System_Platform_numBits;
v___x_237_ = lean_unsigned_to_nat(2u);
v___x_238_ = lean_nat_pow(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_USize_ofNatClamp___closed__1(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_obj_once(&l_USize_ofNatClamp___closed__0, &l_USize_ofNatClamp___closed__0_once, _init_l_USize_ofNatClamp___closed__0);
v___x_241_ = lean_nat_sub(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static size_t _init_l_USize_ofNatClamp___closed__2(void){
_start:
{
lean_object* v___x_242_; size_t v___x_243_; 
v___x_242_ = lean_obj_once(&l_USize_ofNatClamp___closed__1, &l_USize_ofNatClamp___closed__1_once, _init_l_USize_ofNatClamp___closed__1);
v___x_243_ = lean_usize_of_nat(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT size_t l_USize_ofNatClamp(lean_object* v_n_244_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_obj_once(&l_USize_ofNatClamp___closed__0, &l_USize_ofNatClamp___closed__0_once, _init_l_USize_ofNatClamp___closed__0);
v___x_246_ = lean_nat_dec_lt(v_n_244_, v___x_245_);
if (v___x_246_ == 0)
{
size_t v___x_247_; 
v___x_247_ = lean_usize_once(&l_USize_ofNatClamp___closed__2, &l_USize_ofNatClamp___closed__2_once, _init_l_USize_ofNatClamp___closed__2);
return v___x_247_;
}
else
{
size_t v___x_248_; 
v___x_248_ = lean_usize_of_nat(v_n_244_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_USize_ofNatClamp___boxed(lean_object* v_n_249_){
_start:
{
size_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_USize_ofNatClamp(v_n_249_);
lean_dec(v_n_249_);
v_r_251_ = lean_box_usize(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT size_t l_USize_ofNatTruncate(lean_object* v_n_252_){
_start:
{
size_t v___x_253_; 
v___x_253_ = l_USize_ofNatClamp(v_n_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNatTruncate___boxed(lean_object* v_n_254_){
_start:
{
size_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_USize_ofNatTruncate(v_n_254_);
lean_dec(v_n_254_);
v_r_256_ = lean_box_usize(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT size_t l_Nat_toUSize(lean_object* v_n_257_){
_start:
{
size_t v___x_258_; 
v___x_258_ = lean_usize_of_nat(v_n_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object* v_n_259_){
_start:
{
size_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Nat_toUSize(v_n_259_);
lean_dec(v_n_259_);
v_r_261_ = lean_box_usize(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object* v_n_263_){
_start:
{
size_t v_n_boxed_264_; lean_object* v_res_265_; 
v_n_boxed_264_ = lean_unbox_usize(v_n_263_);
lean_dec(v_n_263_);
v_res_265_ = lean_usize_to_nat(v_n_boxed_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object* v_a_268_, lean_object* v_b_269_){
_start:
{
size_t v_a_boxed_270_; size_t v_b_boxed_271_; size_t v_res_272_; lean_object* v_r_273_; 
v_a_boxed_270_ = lean_unbox_usize(v_a_268_);
lean_dec(v_a_268_);
v_b_boxed_271_ = lean_unbox_usize(v_b_269_);
lean_dec(v_b_269_);
v_res_272_ = lean_usize_add(v_a_boxed_270_, v_b_boxed_271_);
v_r_273_ = lean_box_usize(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object* v_a_276_, lean_object* v_b_277_){
_start:
{
size_t v_a_boxed_278_; size_t v_b_boxed_279_; size_t v_res_280_; lean_object* v_r_281_; 
v_a_boxed_278_ = lean_unbox_usize(v_a_276_);
lean_dec(v_a_276_);
v_b_boxed_279_ = lean_unbox_usize(v_b_277_);
lean_dec(v_b_277_);
v_res_280_ = lean_usize_sub(v_a_boxed_278_, v_b_boxed_279_);
v_r_281_ = lean_box_usize(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT size_t l_USize_instOfNat(lean_object* v_n_282_){
_start:
{
size_t v___x_283_; 
v___x_283_ = lean_usize_of_nat(v_n_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_USize_instOfNat___boxed(lean_object* v_n_284_){
_start:
{
size_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_USize_instOfNat(v_n_284_);
lean_dec(v_n_284_);
v_r_286_ = lean_box_usize(v_res_285_);
return v_r_286_;
}
}
static lean_object* _init_l_instLTUSize(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_box(0);
return v___x_291_;
}
}
static lean_object* _init_l_instLEUSize(void){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
return v___x_292_;
}
}
LEAN_EXPORT uint8_t l_USize_decLt___aux__1(size_t v_a_293_, size_t v_b_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_usize_to_nat(v_a_293_);
v___x_296_ = lean_usize_to_nat(v_b_294_);
v___x_297_ = lean_nat_dec_lt(v___x_295_, v___x_296_);
lean_dec(v___x_296_);
lean_dec(v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___aux__1___boxed(lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
size_t v_a_boxed_300_; size_t v_b_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_a_boxed_300_ = lean_unbox_usize(v_a_298_);
lean_dec(v_a_298_);
v_b_boxed_301_ = lean_unbox_usize(v_b_299_);
lean_dec(v_b_299_);
v_res_302_ = l_USize_decLt___aux__1(v_a_boxed_300_, v_b_boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
size_t v_a_boxed_308_; size_t v_b_boxed_309_; uint8_t v_res_310_; lean_object* v_r_311_; 
v_a_boxed_308_ = lean_unbox_usize(v_a_306_);
lean_dec(v_a_306_);
v_b_boxed_309_ = lean_unbox_usize(v_b_307_);
lean_dec(v_b_307_);
v_res_310_ = lean_usize_dec_lt(v_a_boxed_308_, v_b_boxed_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_USize_decLe___aux__1(size_t v_a_312_, size_t v_b_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_usize_to_nat(v_a_312_);
v___x_315_ = lean_usize_to_nat(v_b_313_);
v___x_316_ = lean_nat_dec_le(v___x_314_, v___x_315_);
lean_dec(v___x_315_);
lean_dec(v___x_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___aux__1___boxed(lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
size_t v_a_boxed_319_; size_t v_b_boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_a_boxed_319_ = lean_unbox_usize(v_a_317_);
lean_dec(v_a_317_);
v_b_boxed_320_ = lean_unbox_usize(v_b_318_);
lean_dec(v_b_318_);
v_res_321_ = l_USize_decLe___aux__1(v_a_boxed_319_, v_b_boxed_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
size_t v_a_boxed_327_; size_t v_b_boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_a_boxed_327_ = lean_unbox_usize(v_a_325_);
lean_dec(v_a_325_);
v_b_boxed_328_ = lean_unbox_usize(v_b_326_);
lean_dec(v_b_326_);
v_res_329_ = lean_usize_dec_le(v_a_boxed_327_, v_b_boxed_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
