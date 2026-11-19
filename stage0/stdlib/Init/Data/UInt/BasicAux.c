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
lean_object* l_BitVec_ofNatClamp(lean_object*, lean_object*);
size_t lean_usize_of_nat_mk(lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
uint32_t lean_uint32_of_nat_mk(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint64_t lean_uint64_of_nat_mk(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_uint16_to_nat(uint16_t);
uint16_t lean_uint16_of_nat_mk(lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object*, lean_object*);
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
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(8u);
v___x_8_ = l_BitVec_ofNatClamp(v___x_7_, v_n_6_);
v___x_9_ = lean_uint8_of_nat_mk(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofNatClamp___boxed(lean_object* v_n_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_UInt8_ofNatClamp(v_n_10_);
lean_dec(v_n_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofNatTruncate(lean_object* v_n_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = l_UInt8_ofNatClamp(v_n_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofNatTruncate___boxed(lean_object* v_n_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_UInt8_ofNatTruncate(v_n_15_);
lean_dec(v_n_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Nat_toUInt8(lean_object* v_n_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_uint8_of_nat(v_n_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object* v_n_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Nat_toUInt8(v_n_20_);
lean_dec(v_n_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object* v_n_24_){
_start:
{
uint8_t v_n_boxed_25_; lean_object* v_res_26_; 
v_n_boxed_25_ = lean_unbox(v_n_24_);
v_res_26_ = lean_uint8_to_nat(v_n_boxed_25_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instOfNat(lean_object* v_n_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = lean_uint8_of_nat(v_n_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instOfNat___boxed(lean_object* v_n_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_UInt8_instOfNat(v_n_29_);
lean_dec(v_n_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin(uint16_t v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_uint16_to_nat(v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFin___boxed(lean_object* v_x_34_){
_start:
{
uint16_t v_x_boxed_35_; lean_object* v_res_36_; 
v_x_boxed_35_ = lean_unbox(v_x_34_);
v_res_36_ = l_UInt16_toFin(v_x_boxed_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object* v_n_38_){
_start:
{
uint16_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = lean_uint16_of_nat(v_n_38_);
lean_dec(v_n_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofNatClamp(lean_object* v_n_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; uint16_t v___x_44_; 
v___x_42_ = lean_unsigned_to_nat(16u);
v___x_43_ = l_BitVec_ofNatClamp(v___x_42_, v_n_41_);
v___x_44_ = lean_uint16_of_nat_mk(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNatClamp___boxed(lean_object* v_n_45_){
_start:
{
uint16_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_UInt16_ofNatClamp(v_n_45_);
lean_dec(v_n_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofNatTruncate(lean_object* v_n_48_){
_start:
{
uint16_t v___x_49_; 
v___x_49_ = l_UInt16_ofNatClamp(v_n_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNatTruncate___boxed(lean_object* v_n_50_){
_start:
{
uint16_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_UInt16_ofNatTruncate(v_n_50_);
lean_dec(v_n_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint16_t l_Nat_toUInt16(lean_object* v_n_53_){
_start:
{
uint16_t v___x_54_; 
v___x_54_ = lean_uint16_of_nat(v_n_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object* v_n_55_){
_start:
{
uint16_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Nat_toUInt16(v_n_55_);
lean_dec(v_n_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object* v_n_59_){
_start:
{
uint16_t v_n_boxed_60_; lean_object* v_res_61_; 
v_n_boxed_60_ = lean_unbox(v_n_59_);
v_res_61_ = lean_uint16_to_nat(v_n_boxed_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object* v_a_63_){
_start:
{
uint16_t v_a_boxed_64_; uint8_t v_res_65_; lean_object* v_r_66_; 
v_a_boxed_64_ = lean_unbox(v_a_63_);
v_res_65_ = lean_uint16_to_uint8(v_a_boxed_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object* v_a_68_){
_start:
{
uint8_t v_a_boxed_69_; uint16_t v_res_70_; lean_object* v_r_71_; 
v_a_boxed_69_ = lean_unbox(v_a_68_);
v_res_70_ = lean_uint8_to_uint16(v_a_boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint16_t l_UInt16_instOfNat(lean_object* v_n_72_){
_start:
{
uint16_t v___x_73_; 
v___x_73_ = lean_uint16_of_nat(v_n_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instOfNat___boxed(lean_object* v_n_74_){
_start:
{
uint16_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_UInt16_instOfNat(v_n_74_);
lean_dec(v_n_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin(uint32_t v_x_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_uint32_to_nat(v_x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFin___boxed(lean_object* v_x_79_){
_start:
{
uint32_t v_x_boxed_80_; lean_object* v_res_81_; 
v_x_boxed_80_ = lean_unbox_uint32(v_x_79_);
lean_dec(v_x_79_);
v_res_81_ = l_UInt32_toFin(v_x_boxed_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object* v_n_83_){
_start:
{
uint32_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = lean_uint32_of_nat(v_n_83_);
lean_dec(v_n_83_);
v_r_85_ = lean_box_uint32(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofNatClamp(lean_object* v_n_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint32_t v___x_89_; 
v___x_87_ = lean_unsigned_to_nat(32u);
v___x_88_ = l_BitVec_ofNatClamp(v___x_87_, v_n_86_);
v___x_89_ = lean_uint32_of_nat_mk(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNatClamp___boxed(lean_object* v_n_90_){
_start:
{
uint32_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_UInt32_ofNatClamp(v_n_90_);
lean_dec(v_n_90_);
v_r_92_ = lean_box_uint32(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofNatTruncate(lean_object* v_n_93_){
_start:
{
uint32_t v___x_94_; 
v___x_94_ = l_UInt32_ofNatClamp(v_n_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNatTruncate___boxed(lean_object* v_n_95_){
_start:
{
uint32_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_UInt32_ofNatTruncate(v_n_95_);
lean_dec(v_n_95_);
v_r_97_ = lean_box_uint32(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint32_t l_Nat_toUInt32(lean_object* v_n_98_){
_start:
{
uint32_t v___x_99_; 
v___x_99_ = lean_uint32_of_nat(v_n_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object* v_n_100_){
_start:
{
uint32_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Nat_toUInt32(v_n_100_);
lean_dec(v_n_100_);
v_r_102_ = lean_box_uint32(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object* v_a_104_){
_start:
{
uint32_t v_a_boxed_105_; uint8_t v_res_106_; lean_object* v_r_107_; 
v_a_boxed_105_ = lean_unbox_uint32(v_a_104_);
lean_dec(v_a_104_);
v_res_106_ = lean_uint32_to_uint8(v_a_boxed_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object* v_a_109_){
_start:
{
uint32_t v_a_boxed_110_; uint16_t v_res_111_; lean_object* v_r_112_; 
v_a_boxed_110_ = lean_unbox_uint32(v_a_109_);
lean_dec(v_a_109_);
v_res_111_ = lean_uint32_to_uint16(v_a_boxed_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object* v_a_114_){
_start:
{
uint8_t v_a_boxed_115_; uint32_t v_res_116_; lean_object* v_r_117_; 
v_a_boxed_115_ = lean_unbox(v_a_114_);
v_res_116_ = lean_uint8_to_uint32(v_a_boxed_115_);
v_r_117_ = lean_box_uint32(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object* v_a_119_){
_start:
{
uint16_t v_a_boxed_120_; uint32_t v_res_121_; lean_object* v_r_122_; 
v_a_boxed_120_ = lean_unbox(v_a_119_);
v_res_121_ = lean_uint16_to_uint32(v_a_boxed_120_);
v_r_122_ = lean_box_uint32(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint32_t l_UInt32_instOfNat(lean_object* v_n_123_){
_start:
{
uint32_t v___x_124_; 
v___x_124_ = lean_uint32_of_nat(v_n_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instOfNat___boxed(lean_object* v_n_125_){
_start:
{
uint32_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_UInt32_instOfNat(v_n_125_);
lean_dec(v_n_125_);
v_r_127_ = lean_box_uint32(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object* v_a_130_, lean_object* v_b_131_){
_start:
{
uint32_t v_a_boxed_132_; uint32_t v_b_boxed_133_; uint32_t v_res_134_; lean_object* v_r_135_; 
v_a_boxed_132_ = lean_unbox_uint32(v_a_130_);
lean_dec(v_a_130_);
v_b_boxed_133_ = lean_unbox_uint32(v_b_131_);
lean_dec(v_b_131_);
v_res_134_ = lean_uint32_add(v_a_boxed_132_, v_b_boxed_133_);
v_r_135_ = lean_box_uint32(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
uint32_t v_a_boxed_140_; uint32_t v_b_boxed_141_; uint32_t v_res_142_; lean_object* v_r_143_; 
v_a_boxed_140_ = lean_unbox_uint32(v_a_138_);
lean_dec(v_a_138_);
v_b_boxed_141_ = lean_unbox_uint32(v_b_139_);
lean_dec(v_b_139_);
v_res_142_ = lean_uint32_sub(v_a_boxed_140_, v_b_boxed_141_);
v_r_143_ = lean_box_uint32(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin(uint64_t v_x_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_uint64_to_nat(v_x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFin___boxed(lean_object* v_x_150_){
_start:
{
uint64_t v_x_boxed_151_; lean_object* v_res_152_; 
v_x_boxed_151_ = lean_unbox_uint64(v_x_150_);
lean_dec_ref(v_x_150_);
v_res_152_ = l_UInt64_toFin(v_x_boxed_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object* v_n_154_){
_start:
{
uint64_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = lean_uint64_of_nat(v_n_154_);
lean_dec(v_n_154_);
v_r_156_ = lean_box_uint64(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofNatClamp(lean_object* v_n_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint64_t v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(64u);
v___x_159_ = l_BitVec_ofNatClamp(v___x_158_, v_n_157_);
v___x_160_ = lean_uint64_of_nat_mk(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNatClamp___boxed(lean_object* v_n_161_){
_start:
{
uint64_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_UInt64_ofNatClamp(v_n_161_);
lean_dec(v_n_161_);
v_r_163_ = lean_box_uint64(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofNatTruncate(lean_object* v_n_164_){
_start:
{
uint64_t v___x_165_; 
v___x_165_ = l_UInt64_ofNatClamp(v_n_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNatTruncate___boxed(lean_object* v_n_166_){
_start:
{
uint64_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_UInt64_ofNatTruncate(v_n_166_);
lean_dec(v_n_166_);
v_r_168_ = lean_box_uint64(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint64_t l_Nat_toUInt64(lean_object* v_n_169_){
_start:
{
uint64_t v___x_170_; 
v___x_170_ = lean_uint64_of_nat(v_n_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object* v_n_171_){
_start:
{
uint64_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Nat_toUInt64(v_n_171_);
lean_dec(v_n_171_);
v_r_173_ = lean_box_uint64(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object* v_n_175_){
_start:
{
uint64_t v_n_boxed_176_; lean_object* v_res_177_; 
v_n_boxed_176_ = lean_unbox_uint64(v_n_175_);
lean_dec_ref(v_n_175_);
v_res_177_ = lean_uint64_to_nat(v_n_boxed_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object* v_a_179_){
_start:
{
uint64_t v_a_boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v_a_boxed_180_ = lean_unbox_uint64(v_a_179_);
lean_dec_ref(v_a_179_);
v_res_181_ = lean_uint64_to_uint8(v_a_boxed_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object* v_a_184_){
_start:
{
uint64_t v_a_boxed_185_; uint16_t v_res_186_; lean_object* v_r_187_; 
v_a_boxed_185_ = lean_unbox_uint64(v_a_184_);
lean_dec_ref(v_a_184_);
v_res_186_ = lean_uint64_to_uint16(v_a_boxed_185_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object* v_a_189_){
_start:
{
uint64_t v_a_boxed_190_; uint32_t v_res_191_; lean_object* v_r_192_; 
v_a_boxed_190_ = lean_unbox_uint64(v_a_189_);
lean_dec_ref(v_a_189_);
v_res_191_ = lean_uint64_to_uint32(v_a_boxed_190_);
v_r_192_ = lean_box_uint32(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object* v_a_194_){
_start:
{
uint8_t v_a_boxed_195_; uint64_t v_res_196_; lean_object* v_r_197_; 
v_a_boxed_195_ = lean_unbox(v_a_194_);
v_res_196_ = lean_uint8_to_uint64(v_a_boxed_195_);
v_r_197_ = lean_box_uint64(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object* v_a_199_){
_start:
{
uint16_t v_a_boxed_200_; uint64_t v_res_201_; lean_object* v_r_202_; 
v_a_boxed_200_ = lean_unbox(v_a_199_);
v_res_201_ = lean_uint16_to_uint64(v_a_boxed_200_);
v_r_202_ = lean_box_uint64(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object* v_a_204_){
_start:
{
uint32_t v_a_boxed_205_; uint64_t v_res_206_; lean_object* v_r_207_; 
v_a_boxed_205_ = lean_unbox_uint32(v_a_204_);
lean_dec(v_a_204_);
v_res_206_ = lean_uint32_to_uint64(v_a_boxed_205_);
v_r_207_ = lean_box_uint64(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint64_t l_UInt64_instOfNat(lean_object* v_n_208_){
_start:
{
uint64_t v___x_209_; 
v___x_209_ = lean_uint64_of_nat(v_n_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instOfNat___boxed(lean_object* v_n_210_){
_start:
{
uint64_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_UInt64_instOfNat(v_n_210_);
lean_dec(v_n_210_);
v_r_212_ = lean_box_uint64(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin(size_t v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_usize_to_nat(v_x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_USize_toFin___boxed(lean_object* v_x_215_){
_start:
{
size_t v_x_boxed_216_; lean_object* v_res_217_; 
v_x_boxed_216_ = lean_unbox_usize(v_x_215_);
lean_dec(v_x_215_);
v_res_217_ = l_USize_toFin(v_x_boxed_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object* v_n_219_){
_start:
{
size_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = lean_usize_of_nat(v_n_219_);
lean_dec(v_n_219_);
v_r_221_ = lean_box_usize(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT size_t l_USize_ofNatClamp(lean_object* v_n_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; size_t v___x_225_; 
v___x_223_ = l_System_Platform_numBits;
v___x_224_ = l_BitVec_ofNatClamp(v___x_223_, v_n_222_);
v___x_225_ = lean_usize_of_nat_mk(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNatClamp___boxed(lean_object* v_n_226_){
_start:
{
size_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_USize_ofNatClamp(v_n_226_);
lean_dec(v_n_226_);
v_r_228_ = lean_box_usize(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT size_t l_USize_ofNatTruncate(lean_object* v_n_229_){
_start:
{
size_t v___x_230_; 
v___x_230_ = l_USize_ofNatClamp(v_n_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNatTruncate___boxed(lean_object* v_n_231_){
_start:
{
size_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_USize_ofNatTruncate(v_n_231_);
lean_dec(v_n_231_);
v_r_233_ = lean_box_usize(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT size_t l_Nat_toUSize(lean_object* v_n_234_){
_start:
{
size_t v___x_235_; 
v___x_235_ = lean_usize_of_nat(v_n_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object* v_n_236_){
_start:
{
size_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Nat_toUSize(v_n_236_);
lean_dec(v_n_236_);
v_r_238_ = lean_box_usize(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object* v_n_240_){
_start:
{
size_t v_n_boxed_241_; lean_object* v_res_242_; 
v_n_boxed_241_ = lean_unbox_usize(v_n_240_);
lean_dec(v_n_240_);
v_res_242_ = lean_usize_to_nat(v_n_boxed_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
size_t v_a_boxed_247_; size_t v_b_boxed_248_; size_t v_res_249_; lean_object* v_r_250_; 
v_a_boxed_247_ = lean_unbox_usize(v_a_245_);
lean_dec(v_a_245_);
v_b_boxed_248_ = lean_unbox_usize(v_b_246_);
lean_dec(v_b_246_);
v_res_249_ = lean_usize_add(v_a_boxed_247_, v_b_boxed_248_);
v_r_250_ = lean_box_usize(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object* v_a_253_, lean_object* v_b_254_){
_start:
{
size_t v_a_boxed_255_; size_t v_b_boxed_256_; size_t v_res_257_; lean_object* v_r_258_; 
v_a_boxed_255_ = lean_unbox_usize(v_a_253_);
lean_dec(v_a_253_);
v_b_boxed_256_ = lean_unbox_usize(v_b_254_);
lean_dec(v_b_254_);
v_res_257_ = lean_usize_sub(v_a_boxed_255_, v_b_boxed_256_);
v_r_258_ = lean_box_usize(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT size_t l_USize_instOfNat(lean_object* v_n_259_){
_start:
{
size_t v___x_260_; 
v___x_260_ = lean_usize_of_nat(v_n_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_USize_instOfNat___boxed(lean_object* v_n_261_){
_start:
{
size_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_USize_instOfNat(v_n_261_);
lean_dec(v_n_261_);
v_r_263_ = lean_box_usize(v_res_262_);
return v_r_263_;
}
}
static lean_object* _init_l_instLTUSize(void){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
static lean_object* _init_l_instLEUSize(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_box(0);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
size_t v_a_boxed_274_; size_t v_b_boxed_275_; uint8_t v_res_276_; lean_object* v_r_277_; 
v_a_boxed_274_ = lean_unbox_usize(v_a_272_);
lean_dec(v_a_272_);
v_b_boxed_275_ = lean_unbox_usize(v_b_273_);
lean_dec(v_b_273_);
v_res_276_ = lean_usize_dec_lt(v_a_boxed_274_, v_b_boxed_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
size_t v_a_boxed_282_; size_t v_b_boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_a_boxed_282_ = lean_unbox_usize(v_a_280_);
lean_dec(v_a_280_);
v_b_boxed_283_ = lean_unbox_usize(v_b_281_);
lean_dec(v_b_281_);
v_res_284_ = lean_usize_dec_le(v_a_boxed_282_, v_b_boxed_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
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
