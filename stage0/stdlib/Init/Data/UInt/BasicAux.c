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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_uint8_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_toFin(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toFin___boxed(lean_object*);
static lean_once_cell_t l_UInt8_ofNatTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_UInt8_ofNatTruncate___closed__0;
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
static lean_once_cell_t l_UInt16_ofNatTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_UInt16_ofNatTruncate___closed__0;
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
static lean_once_cell_t l_UInt32_ofNatTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_UInt32_ofNatTruncate___closed__0;
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
static lean_once_cell_t l_UInt64_ofNatTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_ofNatTruncate___closed__0;
static lean_once_cell_t l_UInt64_ofNatTruncate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_ofNatTruncate___closed__1;
static lean_once_cell_t l_UInt64_ofNatTruncate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_UInt64_ofNatTruncate___closed__2;
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
static lean_once_cell_t l_USize_ofNatTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_ofNatTruncate___closed__0;
static lean_once_cell_t l_USize_ofNatTruncate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_ofNatTruncate___closed__1;
static lean_once_cell_t l_USize_ofNatTruncate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_USize_ofNatTruncate___closed__2;
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
static uint8_t _init_l_UInt8_ofNatTruncate___closed__0(void){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(255u);
v___x_7_ = lean_uint8_of_nat(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofNatTruncate(lean_object* v_n_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(256u);
v___x_10_ = lean_nat_dec_lt(v_n_8_, v___x_9_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
v___x_11_ = lean_uint8_once(&l_UInt8_ofNatTruncate___closed__0, &l_UInt8_ofNatTruncate___closed__0_once, _init_l_UInt8_ofNatTruncate___closed__0);
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
LEAN_EXPORT lean_object* l_UInt8_ofNatTruncate___boxed(lean_object* v_n_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_UInt8_ofNatTruncate(v_n_13_);
lean_dec(v_n_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_Nat_toUInt8(lean_object* v_n_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lean_uint8_of_nat(v_n_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object* v_n_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Nat_toUInt8(v_n_18_);
lean_dec(v_n_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object* v_n_22_){
_start:
{
uint8_t v_n_boxed_23_; lean_object* v_res_24_; 
v_n_boxed_23_ = lean_unbox(v_n_22_);
v_res_24_ = lean_uint8_to_nat(v_n_boxed_23_);
return v_res_24_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instOfNat(lean_object* v_n_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_uint8_of_nat(v_n_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instOfNat___boxed(lean_object* v_n_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_UInt8_instOfNat(v_n_27_);
lean_dec(v_n_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin(uint16_t v_x_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_uint16_to_nat(v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin___boxed(lean_object* v_x_32_){
_start:
{
uint16_t v_x_boxed_33_; lean_object* v_res_34_; 
v_x_boxed_33_ = lean_unbox(v_x_32_);
v_res_34_ = l_UInt16_toFin(v_x_boxed_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object* v_n_36_){
_start:
{
uint16_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = lean_uint16_of_nat(v_n_36_);
lean_dec(v_n_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
static uint16_t _init_l_UInt16_ofNatTruncate___closed__0(void){
_start:
{
lean_object* v___x_39_; uint16_t v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(65535u);
v___x_40_ = lean_uint16_of_nat(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofNatTruncate(lean_object* v_n_41_){
_start:
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(65536u);
v___x_43_ = lean_nat_dec_lt(v_n_41_, v___x_42_);
if (v___x_43_ == 0)
{
uint16_t v___x_44_; 
v___x_44_ = lean_uint16_once(&l_UInt16_ofNatTruncate___closed__0, &l_UInt16_ofNatTruncate___closed__0_once, _init_l_UInt16_ofNatTruncate___closed__0);
return v___x_44_;
}
else
{
uint16_t v___x_45_; 
v___x_45_ = lean_uint16_of_nat(v_n_41_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNatTruncate___boxed(lean_object* v_n_46_){
_start:
{
uint16_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_UInt16_ofNatTruncate(v_n_46_);
lean_dec(v_n_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint16_t l_Nat_toUInt16(lean_object* v_n_49_){
_start:
{
uint16_t v___x_50_; 
v___x_50_ = lean_uint16_of_nat(v_n_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object* v_n_51_){
_start:
{
uint16_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Nat_toUInt16(v_n_51_);
lean_dec(v_n_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object* v_n_55_){
_start:
{
uint16_t v_n_boxed_56_; lean_object* v_res_57_; 
v_n_boxed_56_ = lean_unbox(v_n_55_);
v_res_57_ = lean_uint16_to_nat(v_n_boxed_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object* v_a_59_){
_start:
{
uint16_t v_a_boxed_60_; uint8_t v_res_61_; lean_object* v_r_62_; 
v_a_boxed_60_ = lean_unbox(v_a_59_);
v_res_61_ = lean_uint16_to_uint8(v_a_boxed_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object* v_a_64_){
_start:
{
uint8_t v_a_boxed_65_; uint16_t v_res_66_; lean_object* v_r_67_; 
v_a_boxed_65_ = lean_unbox(v_a_64_);
v_res_66_ = lean_uint8_to_uint16(v_a_boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint16_t l_UInt16_instOfNat(lean_object* v_n_68_){
_start:
{
uint16_t v___x_69_; 
v___x_69_ = lean_uint16_of_nat(v_n_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instOfNat___boxed(lean_object* v_n_70_){
_start:
{
uint16_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_UInt16_instOfNat(v_n_70_);
lean_dec(v_n_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin(uint32_t v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_uint32_to_nat(v_x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin___boxed(lean_object* v_x_75_){
_start:
{
uint32_t v_x_boxed_76_; lean_object* v_res_77_; 
v_x_boxed_76_ = lean_unbox_uint32(v_x_75_);
lean_dec(v_x_75_);
v_res_77_ = l_UInt32_toFin(v_x_boxed_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object* v_n_79_){
_start:
{
uint32_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = lean_uint32_of_nat(v_n_79_);
lean_dec(v_n_79_);
v_r_81_ = lean_box_uint32(v_res_80_);
return v_r_81_;
}
}
static uint32_t _init_l_UInt32_ofNatTruncate___closed__0(void){
_start:
{
lean_object* v___x_82_; uint32_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(4294967295u);
v___x_83_ = lean_uint32_of_nat(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofNatTruncate(lean_object* v_n_84_){
_start:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = lean_cstr_to_nat("4294967296");
v___x_86_ = lean_nat_dec_lt(v_n_84_, v___x_85_);
if (v___x_86_ == 0)
{
uint32_t v___x_87_; 
v___x_87_ = lean_uint32_once(&l_UInt32_ofNatTruncate___closed__0, &l_UInt32_ofNatTruncate___closed__0_once, _init_l_UInt32_ofNatTruncate___closed__0);
return v___x_87_;
}
else
{
uint32_t v___x_88_; 
v___x_88_ = lean_uint32_of_nat(v_n_84_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNatTruncate___boxed(lean_object* v_n_89_){
_start:
{
uint32_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_UInt32_ofNatTruncate(v_n_89_);
lean_dec(v_n_89_);
v_r_91_ = lean_box_uint32(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint32_t l_Nat_toUInt32(lean_object* v_n_92_){
_start:
{
uint32_t v___x_93_; 
v___x_93_ = lean_uint32_of_nat(v_n_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object* v_n_94_){
_start:
{
uint32_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Nat_toUInt32(v_n_94_);
lean_dec(v_n_94_);
v_r_96_ = lean_box_uint32(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object* v_a_98_){
_start:
{
uint32_t v_a_boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_a_boxed_99_ = lean_unbox_uint32(v_a_98_);
lean_dec(v_a_98_);
v_res_100_ = lean_uint32_to_uint8(v_a_boxed_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object* v_a_103_){
_start:
{
uint32_t v_a_boxed_104_; uint16_t v_res_105_; lean_object* v_r_106_; 
v_a_boxed_104_ = lean_unbox_uint32(v_a_103_);
lean_dec(v_a_103_);
v_res_105_ = lean_uint32_to_uint16(v_a_boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object* v_a_108_){
_start:
{
uint8_t v_a_boxed_109_; uint32_t v_res_110_; lean_object* v_r_111_; 
v_a_boxed_109_ = lean_unbox(v_a_108_);
v_res_110_ = lean_uint8_to_uint32(v_a_boxed_109_);
v_r_111_ = lean_box_uint32(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object* v_a_113_){
_start:
{
uint16_t v_a_boxed_114_; uint32_t v_res_115_; lean_object* v_r_116_; 
v_a_boxed_114_ = lean_unbox(v_a_113_);
v_res_115_ = lean_uint16_to_uint32(v_a_boxed_114_);
v_r_116_ = lean_box_uint32(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint32_t l_UInt32_instOfNat(lean_object* v_n_117_){
_start:
{
uint32_t v___x_118_; 
v___x_118_ = lean_uint32_of_nat(v_n_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instOfNat___boxed(lean_object* v_n_119_){
_start:
{
uint32_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_UInt32_instOfNat(v_n_119_);
lean_dec(v_n_119_);
v_r_121_ = lean_box_uint32(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
uint32_t v_a_boxed_126_; uint32_t v_b_boxed_127_; uint32_t v_res_128_; lean_object* v_r_129_; 
v_a_boxed_126_ = lean_unbox_uint32(v_a_124_);
lean_dec(v_a_124_);
v_b_boxed_127_ = lean_unbox_uint32(v_b_125_);
lean_dec(v_b_125_);
v_res_128_ = lean_uint32_add(v_a_boxed_126_, v_b_boxed_127_);
v_r_129_ = lean_box_uint32(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
uint32_t v_a_boxed_134_; uint32_t v_b_boxed_135_; uint32_t v_res_136_; lean_object* v_r_137_; 
v_a_boxed_134_ = lean_unbox_uint32(v_a_132_);
lean_dec(v_a_132_);
v_b_boxed_135_ = lean_unbox_uint32(v_b_133_);
lean_dec(v_b_133_);
v_res_136_ = lean_uint32_sub(v_a_boxed_134_, v_b_boxed_135_);
v_r_137_ = lean_box_uint32(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin(uint64_t v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_uint64_to_nat(v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin___boxed(lean_object* v_x_144_){
_start:
{
uint64_t v_x_boxed_145_; lean_object* v_res_146_; 
v_x_boxed_145_ = lean_unbox_uint64(v_x_144_);
lean_dec_ref(v_x_144_);
v_res_146_ = l_UInt64_toFin(v_x_boxed_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object* v_n_148_){
_start:
{
uint64_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = lean_uint64_of_nat(v_n_148_);
lean_dec(v_n_148_);
v_r_150_ = lean_box_uint64(v_res_149_);
return v_r_150_;
}
}
static lean_object* _init_l_UInt64_ofNatTruncate___closed__0(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_cstr_to_nat("18446744073709551616");
return v___x_151_;
}
}
static lean_object* _init_l_UInt64_ofNatTruncate___closed__1(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_cstr_to_nat("18446744073709551615");
return v___x_152_;
}
}
static uint64_t _init_l_UInt64_ofNatTruncate___closed__2(void){
_start:
{
lean_object* v___x_153_; uint64_t v___x_154_; 
v___x_153_ = lean_obj_once(&l_UInt64_ofNatTruncate___closed__1, &l_UInt64_ofNatTruncate___closed__1_once, _init_l_UInt64_ofNatTruncate___closed__1);
v___x_154_ = lean_uint64_of_nat(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofNatTruncate(lean_object* v_n_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_obj_once(&l_UInt64_ofNatTruncate___closed__0, &l_UInt64_ofNatTruncate___closed__0_once, _init_l_UInt64_ofNatTruncate___closed__0);
v___x_157_ = lean_nat_dec_lt(v_n_155_, v___x_156_);
if (v___x_157_ == 0)
{
uint64_t v___x_158_; 
v___x_158_ = lean_uint64_once(&l_UInt64_ofNatTruncate___closed__2, &l_UInt64_ofNatTruncate___closed__2_once, _init_l_UInt64_ofNatTruncate___closed__2);
return v___x_158_;
}
else
{
uint64_t v___x_159_; 
v___x_159_ = lean_uint64_of_nat(v_n_155_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNatTruncate___boxed(lean_object* v_n_160_){
_start:
{
uint64_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_UInt64_ofNatTruncate(v_n_160_);
lean_dec(v_n_160_);
v_r_162_ = lean_box_uint64(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint64_t l_Nat_toUInt64(lean_object* v_n_163_){
_start:
{
uint64_t v___x_164_; 
v___x_164_ = lean_uint64_of_nat(v_n_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object* v_n_165_){
_start:
{
uint64_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Nat_toUInt64(v_n_165_);
lean_dec(v_n_165_);
v_r_167_ = lean_box_uint64(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object* v_n_169_){
_start:
{
uint64_t v_n_boxed_170_; lean_object* v_res_171_; 
v_n_boxed_170_ = lean_unbox_uint64(v_n_169_);
lean_dec_ref(v_n_169_);
v_res_171_ = lean_uint64_to_nat(v_n_boxed_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object* v_a_173_){
_start:
{
uint64_t v_a_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_a_boxed_174_ = lean_unbox_uint64(v_a_173_);
lean_dec_ref(v_a_173_);
v_res_175_ = lean_uint64_to_uint8(v_a_boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object* v_a_178_){
_start:
{
uint64_t v_a_boxed_179_; uint16_t v_res_180_; lean_object* v_r_181_; 
v_a_boxed_179_ = lean_unbox_uint64(v_a_178_);
lean_dec_ref(v_a_178_);
v_res_180_ = lean_uint64_to_uint16(v_a_boxed_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object* v_a_183_){
_start:
{
uint64_t v_a_boxed_184_; uint32_t v_res_185_; lean_object* v_r_186_; 
v_a_boxed_184_ = lean_unbox_uint64(v_a_183_);
lean_dec_ref(v_a_183_);
v_res_185_ = lean_uint64_to_uint32(v_a_boxed_184_);
v_r_186_ = lean_box_uint32(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object* v_a_188_){
_start:
{
uint8_t v_a_boxed_189_; uint64_t v_res_190_; lean_object* v_r_191_; 
v_a_boxed_189_ = lean_unbox(v_a_188_);
v_res_190_ = lean_uint8_to_uint64(v_a_boxed_189_);
v_r_191_ = lean_box_uint64(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object* v_a_193_){
_start:
{
uint16_t v_a_boxed_194_; uint64_t v_res_195_; lean_object* v_r_196_; 
v_a_boxed_194_ = lean_unbox(v_a_193_);
v_res_195_ = lean_uint16_to_uint64(v_a_boxed_194_);
v_r_196_ = lean_box_uint64(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object* v_a_198_){
_start:
{
uint32_t v_a_boxed_199_; uint64_t v_res_200_; lean_object* v_r_201_; 
v_a_boxed_199_ = lean_unbox_uint32(v_a_198_);
lean_dec(v_a_198_);
v_res_200_ = lean_uint32_to_uint64(v_a_boxed_199_);
v_r_201_ = lean_box_uint64(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint64_t l_UInt64_instOfNat(lean_object* v_n_202_){
_start:
{
uint64_t v___x_203_; 
v___x_203_ = lean_uint64_of_nat(v_n_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instOfNat___boxed(lean_object* v_n_204_){
_start:
{
uint64_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_UInt64_instOfNat(v_n_204_);
lean_dec(v_n_204_);
v_r_206_ = lean_box_uint64(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin(size_t v_x_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_usize_to_nat(v_x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin___boxed(lean_object* v_x_209_){
_start:
{
size_t v_x_boxed_210_; lean_object* v_res_211_; 
v_x_boxed_210_ = lean_unbox_usize(v_x_209_);
lean_dec(v_x_209_);
v_res_211_ = l_USize_toFin(v_x_boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object* v_n_213_){
_start:
{
size_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = lean_usize_of_nat(v_n_213_);
lean_dec(v_n_213_);
v_r_215_ = lean_box_usize(v_res_214_);
return v_r_215_;
}
}
static lean_object* _init_l_USize_ofNatTruncate___closed__0(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = l_System_Platform_numBits;
v___x_217_ = lean_unsigned_to_nat(2u);
v___x_218_ = lean_nat_pow(v___x_217_, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_USize_ofNatTruncate___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_obj_once(&l_USize_ofNatTruncate___closed__0, &l_USize_ofNatTruncate___closed__0_once, _init_l_USize_ofNatTruncate___closed__0);
v___x_221_ = lean_nat_sub(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static size_t _init_l_USize_ofNatTruncate___closed__2(void){
_start:
{
lean_object* v___x_222_; size_t v___x_223_; 
v___x_222_ = lean_obj_once(&l_USize_ofNatTruncate___closed__1, &l_USize_ofNatTruncate___closed__1_once, _init_l_USize_ofNatTruncate___closed__1);
v___x_223_ = lean_usize_of_nat(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT size_t l_USize_ofNatTruncate(lean_object* v_n_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = lean_obj_once(&l_USize_ofNatTruncate___closed__0, &l_USize_ofNatTruncate___closed__0_once, _init_l_USize_ofNatTruncate___closed__0);
v___x_226_ = lean_nat_dec_lt(v_n_224_, v___x_225_);
if (v___x_226_ == 0)
{
size_t v___x_227_; 
v___x_227_ = lean_usize_once(&l_USize_ofNatTruncate___closed__2, &l_USize_ofNatTruncate___closed__2_once, _init_l_USize_ofNatTruncate___closed__2);
return v___x_227_;
}
else
{
size_t v___x_228_; 
v___x_228_ = lean_usize_of_nat(v_n_224_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_USize_ofNatTruncate___boxed(lean_object* v_n_229_){
_start:
{
size_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_USize_ofNatTruncate(v_n_229_);
lean_dec(v_n_229_);
v_r_231_ = lean_box_usize(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT size_t l_Nat_toUSize(lean_object* v_n_232_){
_start:
{
size_t v___x_233_; 
v___x_233_ = lean_usize_of_nat(v_n_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object* v_n_234_){
_start:
{
size_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Nat_toUSize(v_n_234_);
lean_dec(v_n_234_);
v_r_236_ = lean_box_usize(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object* v_n_238_){
_start:
{
size_t v_n_boxed_239_; lean_object* v_res_240_; 
v_n_boxed_239_ = lean_unbox_usize(v_n_238_);
lean_dec(v_n_238_);
v_res_240_ = lean_usize_to_nat(v_n_boxed_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
size_t v_a_boxed_245_; size_t v_b_boxed_246_; size_t v_res_247_; lean_object* v_r_248_; 
v_a_boxed_245_ = lean_unbox_usize(v_a_243_);
lean_dec(v_a_243_);
v_b_boxed_246_ = lean_unbox_usize(v_b_244_);
lean_dec(v_b_244_);
v_res_247_ = lean_usize_add(v_a_boxed_245_, v_b_boxed_246_);
v_r_248_ = lean_box_usize(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object* v_a_251_, lean_object* v_b_252_){
_start:
{
size_t v_a_boxed_253_; size_t v_b_boxed_254_; size_t v_res_255_; lean_object* v_r_256_; 
v_a_boxed_253_ = lean_unbox_usize(v_a_251_);
lean_dec(v_a_251_);
v_b_boxed_254_ = lean_unbox_usize(v_b_252_);
lean_dec(v_b_252_);
v_res_255_ = lean_usize_sub(v_a_boxed_253_, v_b_boxed_254_);
v_r_256_ = lean_box_usize(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT size_t l_USize_instOfNat(lean_object* v_n_257_){
_start:
{
size_t v___x_258_; 
v___x_258_ = lean_usize_of_nat(v_n_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_USize_instOfNat___boxed(lean_object* v_n_259_){
_start:
{
size_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_USize_instOfNat(v_n_259_);
lean_dec(v_n_259_);
v_r_261_ = lean_box_usize(v_res_260_);
return v_r_261_;
}
}
static lean_object* _init_l_instLTUSize(void){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
static lean_object* _init_l_instLEUSize(void){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
LEAN_EXPORT uint8_t l_USize_decLt___aux__1(size_t v_a_268_, size_t v_b_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_usize_to_nat(v_a_268_);
v___x_271_ = lean_usize_to_nat(v_b_269_);
v___x_272_ = lean_nat_dec_lt(v___x_270_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___aux__1___boxed(lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
size_t v_a_boxed_275_; size_t v_b_boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_a_boxed_275_ = lean_unbox_usize(v_a_273_);
lean_dec(v_a_273_);
v_b_boxed_276_ = lean_unbox_usize(v_b_274_);
lean_dec(v_b_274_);
v_res_277_ = l_USize_decLt___aux__1(v_a_boxed_275_, v_b_boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
size_t v_a_boxed_283_; size_t v_b_boxed_284_; uint8_t v_res_285_; lean_object* v_r_286_; 
v_a_boxed_283_ = lean_unbox_usize(v_a_281_);
lean_dec(v_a_281_);
v_b_boxed_284_ = lean_unbox_usize(v_b_282_);
lean_dec(v_b_282_);
v_res_285_ = lean_usize_dec_lt(v_a_boxed_283_, v_b_boxed_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_USize_decLe___aux__1(size_t v_a_287_, size_t v_b_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_usize_to_nat(v_a_287_);
v___x_290_ = lean_usize_to_nat(v_b_288_);
v___x_291_ = lean_nat_dec_le(v___x_289_, v___x_290_);
lean_dec(v___x_290_);
lean_dec(v___x_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___aux__1___boxed(lean_object* v_a_292_, lean_object* v_b_293_){
_start:
{
size_t v_a_boxed_294_; size_t v_b_boxed_295_; uint8_t v_res_296_; lean_object* v_r_297_; 
v_a_boxed_294_ = lean_unbox_usize(v_a_292_);
lean_dec(v_a_292_);
v_b_boxed_295_ = lean_unbox_usize(v_b_293_);
lean_dec(v_b_293_);
v_res_296_ = l_USize_decLe___aux__1(v_a_boxed_294_, v_b_boxed_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object* v_a_300_, lean_object* v_b_301_){
_start:
{
size_t v_a_boxed_302_; size_t v_b_boxed_303_; uint8_t v_res_304_; lean_object* v_r_305_; 
v_a_boxed_302_ = lean_unbox_usize(v_a_300_);
lean_dec(v_a_300_);
v_b_boxed_303_ = lean_unbox_usize(v_b_301_);
lean_dec(v_b_301_);
v_res_304_ = lean_usize_dec_le(v_a_boxed_302_, v_b_boxed_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
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
