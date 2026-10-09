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
lean_object* l_UInt8_toFin(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_uint8_to_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT void l_UInt8_toFin_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_3_;
v_res_3_ = l_UInt8_toFin(v_x_1_);
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_UInt8_toFin___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_UInt8_toFin(v_x_boxed_5_);
return v_res_6_;
}
}
uint8_t l_UInt8_ofNatClamp(lean_object* v_n_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(8u);
v___x_9_ = l_BitVec_ofNatClamp(v___x_8_, v_n_7_);
v___x_10_ = lean_uint8_of_nat_mk(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT void l_UInt8_ofNatClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_7_ = stack[0].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_UInt8_ofNatClamp(v_n_7_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_UInt8_ofNatClamp___boxed(lean_object* v_n_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_UInt8_ofNatClamp(v_n_12_);
lean_dec(v_n_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_UInt8_ofNatTruncate(lean_object* v_n_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_UInt8_ofNatClamp(v_n_15_);
return v___x_16_;
}
}
LEAN_EXPORT void l_UInt8_ofNatTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_15_ = stack[0].m_obj;
uint8_t v_res_17_;
v_res_17_ = l_UInt8_ofNatTruncate(v_n_15_);
stack->m_num = v_res_17_;
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
uint8_t l_Nat_toUInt8(lean_object* v_n_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = lean_uint8_of_nat(v_n_21_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Nat_toUInt8_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_21_ = stack[0].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_Nat_toUInt8(v_n_21_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object* v_n_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Nat_toUInt8(v_n_24_);
lean_dec(v_n_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT void l_UInt8_toNat_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_27_ = stack[0].m_num;
lean_object* v_res_28_;
v_res_28_ = lean_uint8_to_nat(v_n_27_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object* v_n_29_){
_start:
{
uint8_t v_n_boxed_30_; lean_object* v_res_31_; 
v_n_boxed_30_ = lean_unbox(v_n_29_);
v_res_31_ = lean_uint8_to_nat(v_n_boxed_30_);
return v_res_31_;
}
}
uint8_t l_UInt8_instOfNat(lean_object* v_n_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = lean_uint8_of_nat(v_n_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_UInt8_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_32_ = stack[0].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_UInt8_instOfNat(v_n_32_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_UInt8_instOfNat___boxed(lean_object* v_n_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_UInt8_instOfNat(v_n_35_);
lean_dec(v_n_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
lean_object* l_UInt16_toFin(uint16_t v_x_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_uint16_to_nat(v_x_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_UInt16_toFin_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_38_ = stack[0].m_num;
lean_object* v_res_40_;
v_res_40_ = l_UInt16_toFin(v_x_38_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_UInt16_toFin___boxed(lean_object* v_x_41_){
_start:
{
uint16_t v_x_boxed_42_; lean_object* v_res_43_; 
v_x_boxed_42_ = lean_unbox(v_x_41_);
v_res_43_ = l_UInt16_toFin(v_x_boxed_42_);
return v_res_43_;
}
}
LEAN_EXPORT void l_UInt16_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_44_ = stack[0].m_obj;
uint16_t v_res_45_;
v_res_45_ = lean_uint16_of_nat(v_n_44_);
stack->m_num = v_res_45_;
}
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object* v_n_46_){
_start:
{
uint16_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = lean_uint16_of_nat(v_n_46_);
lean_dec(v_n_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
uint16_t l_UInt16_ofNatClamp(lean_object* v_n_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; uint16_t v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(16u);
v___x_51_ = l_BitVec_ofNatClamp(v___x_50_, v_n_49_);
v___x_52_ = lean_uint16_of_nat_mk(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT void l_UInt16_ofNatClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_49_ = stack[0].m_obj;
uint16_t v_res_53_;
v_res_53_ = l_UInt16_ofNatClamp(v_n_49_);
stack->m_num = v_res_53_;
}
LEAN_EXPORT lean_object* l_UInt16_ofNatClamp___boxed(lean_object* v_n_54_){
_start:
{
uint16_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_UInt16_ofNatClamp(v_n_54_);
lean_dec(v_n_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
uint16_t l_UInt16_ofNatTruncate(lean_object* v_n_57_){
_start:
{
uint16_t v___x_58_; 
v___x_58_ = l_UInt16_ofNatClamp(v_n_57_);
return v___x_58_;
}
}
LEAN_EXPORT void l_UInt16_ofNatTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_57_ = stack[0].m_obj;
uint16_t v_res_59_;
v_res_59_ = l_UInt16_ofNatTruncate(v_n_57_);
stack->m_num = v_res_59_;
}
LEAN_EXPORT lean_object* l_UInt16_ofNatTruncate___boxed(lean_object* v_n_60_){
_start:
{
uint16_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_UInt16_ofNatTruncate(v_n_60_);
lean_dec(v_n_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
uint16_t l_Nat_toUInt16(lean_object* v_n_63_){
_start:
{
uint16_t v___x_64_; 
v___x_64_ = lean_uint16_of_nat(v_n_63_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Nat_toUInt16_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_63_ = stack[0].m_obj;
uint16_t v_res_65_;
v_res_65_ = l_Nat_toUInt16(v_n_63_);
stack->m_num = v_res_65_;
}
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object* v_n_66_){
_start:
{
uint16_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Nat_toUInt16(v_n_66_);
lean_dec(v_n_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT void l_UInt16_toNat_0interp(lean_interpreter_value* stack)
{
uint16_t v_n_69_ = stack[0].m_num;
lean_object* v_res_70_;
v_res_70_ = lean_uint16_to_nat(v_n_69_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object* v_n_71_){
_start:
{
uint16_t v_n_boxed_72_; lean_object* v_res_73_; 
v_n_boxed_72_ = lean_unbox(v_n_71_);
v_res_73_ = lean_uint16_to_nat(v_n_boxed_72_);
return v_res_73_;
}
}
LEAN_EXPORT void l_UInt16_toUInt8_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_74_ = stack[0].m_num;
uint8_t v_res_75_;
v_res_75_ = lean_uint16_to_uint8(v_a_74_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object* v_a_76_){
_start:
{
uint16_t v_a_boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_a_boxed_77_ = lean_unbox(v_a_76_);
v_res_78_ = lean_uint16_to_uint8(v_a_boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT void l_UInt8_toUInt16_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_80_ = stack[0].m_num;
uint16_t v_res_81_;
v_res_81_ = lean_uint8_to_uint16(v_a_80_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object* v_a_82_){
_start:
{
uint8_t v_a_boxed_83_; uint16_t v_res_84_; lean_object* v_r_85_; 
v_a_boxed_83_ = lean_unbox(v_a_82_);
v_res_84_ = lean_uint8_to_uint16(v_a_boxed_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint16_t l_UInt16_instOfNat(lean_object* v_n_86_){
_start:
{
uint16_t v___x_87_; 
v___x_87_ = lean_uint16_of_nat(v_n_86_);
return v___x_87_;
}
}
LEAN_EXPORT void l_UInt16_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_86_ = stack[0].m_obj;
uint16_t v_res_88_;
v_res_88_ = l_UInt16_instOfNat(v_n_86_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_UInt16_instOfNat___boxed(lean_object* v_n_89_){
_start:
{
uint16_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_UInt16_instOfNat(v_n_89_);
lean_dec(v_n_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
lean_object* l_UInt32_toFin(uint32_t v_x_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_uint32_to_nat(v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT void l_UInt32_toFin_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_92_ = stack[0].m_num;
lean_object* v_res_94_;
v_res_94_ = l_UInt32_toFin(v_x_92_);
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l_UInt32_toFin___boxed(lean_object* v_x_95_){
_start:
{
uint32_t v_x_boxed_96_; lean_object* v_res_97_; 
v_x_boxed_96_ = lean_unbox_uint32(v_x_95_);
lean_dec(v_x_95_);
v_res_97_ = l_UInt32_toFin(v_x_boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT void l_UInt32_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_98_ = stack[0].m_obj;
uint32_t v_res_99_;
v_res_99_ = lean_uint32_of_nat(v_n_98_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object* v_n_100_){
_start:
{
uint32_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = lean_uint32_of_nat(v_n_100_);
lean_dec(v_n_100_);
v_r_102_ = lean_box_uint32(v_res_101_);
return v_r_102_;
}
}
uint32_t l_UInt32_ofNatClamp(lean_object* v_n_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint32_t v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(32u);
v___x_105_ = l_BitVec_ofNatClamp(v___x_104_, v_n_103_);
v___x_106_ = lean_uint32_of_nat_mk(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT void l_UInt32_ofNatClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_103_ = stack[0].m_obj;
uint32_t v_res_107_;
v_res_107_ = l_UInt32_ofNatClamp(v_n_103_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l_UInt32_ofNatClamp___boxed(lean_object* v_n_108_){
_start:
{
uint32_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_UInt32_ofNatClamp(v_n_108_);
lean_dec(v_n_108_);
v_r_110_ = lean_box_uint32(v_res_109_);
return v_r_110_;
}
}
uint32_t l_UInt32_ofNatTruncate(lean_object* v_n_111_){
_start:
{
uint32_t v___x_112_; 
v___x_112_ = l_UInt32_ofNatClamp(v_n_111_);
return v___x_112_;
}
}
LEAN_EXPORT void l_UInt32_ofNatTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_111_ = stack[0].m_obj;
uint32_t v_res_113_;
v_res_113_ = l_UInt32_ofNatTruncate(v_n_111_);
stack->m_num = v_res_113_;
}
LEAN_EXPORT lean_object* l_UInt32_ofNatTruncate___boxed(lean_object* v_n_114_){
_start:
{
uint32_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_UInt32_ofNatTruncate(v_n_114_);
lean_dec(v_n_114_);
v_r_116_ = lean_box_uint32(v_res_115_);
return v_r_116_;
}
}
uint32_t l_Nat_toUInt32(lean_object* v_n_117_){
_start:
{
uint32_t v___x_118_; 
v___x_118_ = lean_uint32_of_nat(v_n_117_);
return v___x_118_;
}
}
LEAN_EXPORT void l_Nat_toUInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_117_ = stack[0].m_obj;
uint32_t v_res_119_;
v_res_119_ = l_Nat_toUInt32(v_n_117_);
stack->m_num = v_res_119_;
}
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object* v_n_120_){
_start:
{
uint32_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Nat_toUInt32(v_n_120_);
lean_dec(v_n_120_);
v_r_122_ = lean_box_uint32(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT void l_UInt32_toUInt8_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_123_ = stack[0].m_num;
uint8_t v_res_124_;
v_res_124_ = lean_uint32_to_uint8(v_a_123_);
stack->m_num = v_res_124_;
}
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object* v_a_125_){
_start:
{
uint32_t v_a_boxed_126_; uint8_t v_res_127_; lean_object* v_r_128_; 
v_a_boxed_126_ = lean_unbox_uint32(v_a_125_);
lean_dec(v_a_125_);
v_res_127_ = lean_uint32_to_uint8(v_a_boxed_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT void l_UInt32_toUInt16_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_129_ = stack[0].m_num;
uint16_t v_res_130_;
v_res_130_ = lean_uint32_to_uint16(v_a_129_);
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object* v_a_131_){
_start:
{
uint32_t v_a_boxed_132_; uint16_t v_res_133_; lean_object* v_r_134_; 
v_a_boxed_132_ = lean_unbox_uint32(v_a_131_);
lean_dec(v_a_131_);
v_res_133_ = lean_uint32_to_uint16(v_a_boxed_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT void l_UInt8_toUInt32_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_135_ = stack[0].m_num;
uint32_t v_res_136_;
v_res_136_ = lean_uint8_to_uint32(v_a_135_);
stack->m_num = v_res_136_;
}
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object* v_a_137_){
_start:
{
uint8_t v_a_boxed_138_; uint32_t v_res_139_; lean_object* v_r_140_; 
v_a_boxed_138_ = lean_unbox(v_a_137_);
v_res_139_ = lean_uint8_to_uint32(v_a_boxed_138_);
v_r_140_ = lean_box_uint32(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT void l_UInt16_toUInt32_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_141_ = stack[0].m_num;
uint32_t v_res_142_;
v_res_142_ = lean_uint16_to_uint32(v_a_141_);
stack->m_num = v_res_142_;
}
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object* v_a_143_){
_start:
{
uint16_t v_a_boxed_144_; uint32_t v_res_145_; lean_object* v_r_146_; 
v_a_boxed_144_ = lean_unbox(v_a_143_);
v_res_145_ = lean_uint16_to_uint32(v_a_boxed_144_);
v_r_146_ = lean_box_uint32(v_res_145_);
return v_r_146_;
}
}
uint32_t l_UInt32_instOfNat(lean_object* v_n_147_){
_start:
{
uint32_t v___x_148_; 
v___x_148_ = lean_uint32_of_nat(v_n_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l_UInt32_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_147_ = stack[0].m_obj;
uint32_t v_res_149_;
v_res_149_ = l_UInt32_instOfNat(v_n_147_);
stack->m_num = v_res_149_;
}
LEAN_EXPORT lean_object* l_UInt32_instOfNat___boxed(lean_object* v_n_150_){
_start:
{
uint32_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_UInt32_instOfNat(v_n_150_);
lean_dec(v_n_150_);
v_r_152_ = lean_box_uint32(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT void l_UInt32_add_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_153_ = stack[0].m_num;
uint32_t v_b_154_ = stack[1].m_num;
uint32_t v_res_155_;
v_res_155_ = lean_uint32_add(v_a_153_, v_b_154_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint32_t v_a_boxed_158_; uint32_t v_b_boxed_159_; uint32_t v_res_160_; lean_object* v_r_161_; 
v_a_boxed_158_ = lean_unbox_uint32(v_a_156_);
lean_dec(v_a_156_);
v_b_boxed_159_ = lean_unbox_uint32(v_b_157_);
lean_dec(v_b_157_);
v_res_160_ = lean_uint32_add(v_a_boxed_158_, v_b_boxed_159_);
v_r_161_ = lean_box_uint32(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT void l_UInt32_sub_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_162_ = stack[0].m_num;
uint32_t v_b_163_ = stack[1].m_num;
uint32_t v_res_164_;
v_res_164_ = lean_uint32_sub(v_a_162_, v_b_163_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object* v_a_165_, lean_object* v_b_166_){
_start:
{
uint32_t v_a_boxed_167_; uint32_t v_b_boxed_168_; uint32_t v_res_169_; lean_object* v_r_170_; 
v_a_boxed_167_ = lean_unbox_uint32(v_a_165_);
lean_dec(v_a_165_);
v_b_boxed_168_ = lean_unbox_uint32(v_b_166_);
lean_dec(v_b_166_);
v_res_169_ = lean_uint32_sub(v_a_boxed_167_, v_b_boxed_168_);
v_r_170_ = lean_box_uint32(v_res_169_);
return v_r_170_;
}
}
lean_object* l_UInt64_toFin(uint64_t v_x_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_uint64_to_nat(v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT void l_UInt64_toFin_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_175_ = stack[0].m_num;
lean_object* v_res_177_;
v_res_177_ = l_UInt64_toFin(v_x_175_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l_UInt64_toFin___boxed(lean_object* v_x_178_){
_start:
{
uint64_t v_x_boxed_179_; lean_object* v_res_180_; 
v_x_boxed_179_ = lean_unbox_uint64(v_x_178_);
lean_dec_ref(v_x_178_);
v_res_180_ = l_UInt64_toFin(v_x_boxed_179_);
return v_res_180_;
}
}
LEAN_EXPORT void l_UInt64_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_181_ = stack[0].m_obj;
uint64_t v_res_182_;
v_res_182_ = lean_uint64_of_nat(v_n_181_);
stack->m_num = v_res_182_;
}
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object* v_n_183_){
_start:
{
uint64_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = lean_uint64_of_nat(v_n_183_);
lean_dec(v_n_183_);
v_r_185_ = lean_box_uint64(v_res_184_);
return v_r_185_;
}
}
uint64_t l_UInt64_ofNatClamp(lean_object* v_n_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint64_t v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(64u);
v___x_188_ = l_BitVec_ofNatClamp(v___x_187_, v_n_186_);
v___x_189_ = lean_uint64_of_nat_mk(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT void l_UInt64_ofNatClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_186_ = stack[0].m_obj;
uint64_t v_res_190_;
v_res_190_ = l_UInt64_ofNatClamp(v_n_186_);
stack->m_num = v_res_190_;
}
LEAN_EXPORT lean_object* l_UInt64_ofNatClamp___boxed(lean_object* v_n_191_){
_start:
{
uint64_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_UInt64_ofNatClamp(v_n_191_);
lean_dec(v_n_191_);
v_r_193_ = lean_box_uint64(v_res_192_);
return v_r_193_;
}
}
uint64_t l_UInt64_ofNatTruncate(lean_object* v_n_194_){
_start:
{
uint64_t v___x_195_; 
v___x_195_ = l_UInt64_ofNatClamp(v_n_194_);
return v___x_195_;
}
}
LEAN_EXPORT void l_UInt64_ofNatTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_194_ = stack[0].m_obj;
uint64_t v_res_196_;
v_res_196_ = l_UInt64_ofNatTruncate(v_n_194_);
stack->m_num = v_res_196_;
}
LEAN_EXPORT lean_object* l_UInt64_ofNatTruncate___boxed(lean_object* v_n_197_){
_start:
{
uint64_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_UInt64_ofNatTruncate(v_n_197_);
lean_dec(v_n_197_);
v_r_199_ = lean_box_uint64(v_res_198_);
return v_r_199_;
}
}
uint64_t l_Nat_toUInt64(lean_object* v_n_200_){
_start:
{
uint64_t v___x_201_; 
v___x_201_ = lean_uint64_of_nat(v_n_200_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Nat_toUInt64_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_200_ = stack[0].m_obj;
uint64_t v_res_202_;
v_res_202_ = l_Nat_toUInt64(v_n_200_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object* v_n_203_){
_start:
{
uint64_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Nat_toUInt64(v_n_203_);
lean_dec(v_n_203_);
v_r_205_ = lean_box_uint64(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT void l_UInt64_toNat_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_206_ = stack[0].m_num;
lean_object* v_res_207_;
v_res_207_ = lean_uint64_to_nat(v_n_206_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object* v_n_208_){
_start:
{
uint64_t v_n_boxed_209_; lean_object* v_res_210_; 
v_n_boxed_209_ = lean_unbox_uint64(v_n_208_);
lean_dec_ref(v_n_208_);
v_res_210_ = lean_uint64_to_nat(v_n_boxed_209_);
return v_res_210_;
}
}
LEAN_EXPORT void l_UInt64_toUInt8_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_211_ = stack[0].m_num;
uint8_t v_res_212_;
v_res_212_ = lean_uint64_to_uint8(v_a_211_);
stack->m_num = v_res_212_;
}
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object* v_a_213_){
_start:
{
uint64_t v_a_boxed_214_; uint8_t v_res_215_; lean_object* v_r_216_; 
v_a_boxed_214_ = lean_unbox_uint64(v_a_213_);
lean_dec_ref(v_a_213_);
v_res_215_ = lean_uint64_to_uint8(v_a_boxed_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT void l_UInt64_toUInt16_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_217_ = stack[0].m_num;
uint16_t v_res_218_;
v_res_218_ = lean_uint64_to_uint16(v_a_217_);
stack->m_num = v_res_218_;
}
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object* v_a_219_){
_start:
{
uint64_t v_a_boxed_220_; uint16_t v_res_221_; lean_object* v_r_222_; 
v_a_boxed_220_ = lean_unbox_uint64(v_a_219_);
lean_dec_ref(v_a_219_);
v_res_221_ = lean_uint64_to_uint16(v_a_boxed_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT void l_UInt64_toUInt32_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_223_ = stack[0].m_num;
uint32_t v_res_224_;
v_res_224_ = lean_uint64_to_uint32(v_a_223_);
stack->m_num = v_res_224_;
}
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object* v_a_225_){
_start:
{
uint64_t v_a_boxed_226_; uint32_t v_res_227_; lean_object* v_r_228_; 
v_a_boxed_226_ = lean_unbox_uint64(v_a_225_);
lean_dec_ref(v_a_225_);
v_res_227_ = lean_uint64_to_uint32(v_a_boxed_226_);
v_r_228_ = lean_box_uint32(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT void l_UInt8_toUInt64_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_229_ = stack[0].m_num;
uint64_t v_res_230_;
v_res_230_ = lean_uint8_to_uint64(v_a_229_);
stack->m_num = v_res_230_;
}
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object* v_a_231_){
_start:
{
uint8_t v_a_boxed_232_; uint64_t v_res_233_; lean_object* v_r_234_; 
v_a_boxed_232_ = lean_unbox(v_a_231_);
v_res_233_ = lean_uint8_to_uint64(v_a_boxed_232_);
v_r_234_ = lean_box_uint64(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT void l_UInt16_toUInt64_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_235_ = stack[0].m_num;
uint64_t v_res_236_;
v_res_236_ = lean_uint16_to_uint64(v_a_235_);
stack->m_num = v_res_236_;
}
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object* v_a_237_){
_start:
{
uint16_t v_a_boxed_238_; uint64_t v_res_239_; lean_object* v_r_240_; 
v_a_boxed_238_ = lean_unbox(v_a_237_);
v_res_239_ = lean_uint16_to_uint64(v_a_boxed_238_);
v_r_240_ = lean_box_uint64(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT void l_UInt32_toUInt64_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_241_ = stack[0].m_num;
uint64_t v_res_242_;
v_res_242_ = lean_uint32_to_uint64(v_a_241_);
stack->m_num = v_res_242_;
}
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object* v_a_243_){
_start:
{
uint32_t v_a_boxed_244_; uint64_t v_res_245_; lean_object* v_r_246_; 
v_a_boxed_244_ = lean_unbox_uint32(v_a_243_);
lean_dec(v_a_243_);
v_res_245_ = lean_uint32_to_uint64(v_a_boxed_244_);
v_r_246_ = lean_box_uint64(v_res_245_);
return v_r_246_;
}
}
uint64_t l_UInt64_instOfNat(lean_object* v_n_247_){
_start:
{
uint64_t v___x_248_; 
v___x_248_ = lean_uint64_of_nat(v_n_247_);
return v___x_248_;
}
}
LEAN_EXPORT void l_UInt64_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_247_ = stack[0].m_obj;
uint64_t v_res_249_;
v_res_249_ = l_UInt64_instOfNat(v_n_247_);
stack->m_num = v_res_249_;
}
LEAN_EXPORT lean_object* l_UInt64_instOfNat___boxed(lean_object* v_n_250_){
_start:
{
uint64_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_UInt64_instOfNat(v_n_250_);
lean_dec(v_n_250_);
v_r_252_ = lean_box_uint64(v_res_251_);
return v_r_252_;
}
}
lean_object* l_USize_toFin(size_t v_x_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_usize_to_nat(v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT void l_USize_toFin_0interp(lean_interpreter_value* stack)
{
size_t v_x_253_ = stack[0].m_num;
lean_object* v_res_255_;
v_res_255_ = l_USize_toFin(v_x_253_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_USize_toFin___boxed(lean_object* v_x_256_){
_start:
{
size_t v_x_boxed_257_; lean_object* v_res_258_; 
v_x_boxed_257_ = lean_unbox_usize(v_x_256_);
lean_dec(v_x_256_);
v_res_258_ = l_USize_toFin(v_x_boxed_257_);
return v_res_258_;
}
}
LEAN_EXPORT void l_USize_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_259_ = stack[0].m_obj;
size_t v_res_260_;
v_res_260_ = lean_usize_of_nat(v_n_259_);
stack->m_num = v_res_260_;
}
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object* v_n_261_){
_start:
{
size_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = lean_usize_of_nat(v_n_261_);
lean_dec(v_n_261_);
v_r_263_ = lean_box_usize(v_res_262_);
return v_r_263_;
}
}
size_t l_USize_ofNatClamp(lean_object* v_n_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; size_t v___x_267_; 
v___x_265_ = l_System_Platform_numBits;
v___x_266_ = l_BitVec_ofNatClamp(v___x_265_, v_n_264_);
v___x_267_ = lean_usize_of_nat_mk(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT void l_USize_ofNatClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_264_ = stack[0].m_obj;
size_t v_res_268_;
v_res_268_ = l_USize_ofNatClamp(v_n_264_);
stack->m_num = v_res_268_;
}
LEAN_EXPORT lean_object* l_USize_ofNatClamp___boxed(lean_object* v_n_269_){
_start:
{
size_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_USize_ofNatClamp(v_n_269_);
lean_dec(v_n_269_);
v_r_271_ = lean_box_usize(v_res_270_);
return v_r_271_;
}
}
size_t l_USize_ofNatTruncate(lean_object* v_n_272_){
_start:
{
size_t v___x_273_; 
v___x_273_ = l_USize_ofNatClamp(v_n_272_);
return v___x_273_;
}
}
LEAN_EXPORT void l_USize_ofNatTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_272_ = stack[0].m_obj;
size_t v_res_274_;
v_res_274_ = l_USize_ofNatTruncate(v_n_272_);
stack->m_num = v_res_274_;
}
LEAN_EXPORT lean_object* l_USize_ofNatTruncate___boxed(lean_object* v_n_275_){
_start:
{
size_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_USize_ofNatTruncate(v_n_275_);
lean_dec(v_n_275_);
v_r_277_ = lean_box_usize(v_res_276_);
return v_r_277_;
}
}
size_t l_Nat_toUSize(lean_object* v_n_278_){
_start:
{
size_t v___x_279_; 
v___x_279_ = lean_usize_of_nat(v_n_278_);
return v___x_279_;
}
}
LEAN_EXPORT void l_Nat_toUSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_278_ = stack[0].m_obj;
size_t v_res_280_;
v_res_280_ = l_Nat_toUSize(v_n_278_);
stack->m_num = v_res_280_;
}
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object* v_n_281_){
_start:
{
size_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Nat_toUSize(v_n_281_);
lean_dec(v_n_281_);
v_r_283_ = lean_box_usize(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT void l_USize_toNat_0interp(lean_interpreter_value* stack)
{
size_t v_n_284_ = stack[0].m_num;
lean_object* v_res_285_;
v_res_285_ = lean_usize_to_nat(v_n_284_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object* v_n_286_){
_start:
{
size_t v_n_boxed_287_; lean_object* v_res_288_; 
v_n_boxed_287_ = lean_unbox_usize(v_n_286_);
lean_dec(v_n_286_);
v_res_288_ = lean_usize_to_nat(v_n_boxed_287_);
return v_res_288_;
}
}
LEAN_EXPORT void l_USize_add_0interp(lean_interpreter_value* stack)
{
size_t v_a_289_ = stack[0].m_num;
size_t v_b_290_ = stack[1].m_num;
size_t v_res_291_;
v_res_291_ = lean_usize_add(v_a_289_, v_b_290_);
stack->m_num = v_res_291_;
}
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object* v_a_292_, lean_object* v_b_293_){
_start:
{
size_t v_a_boxed_294_; size_t v_b_boxed_295_; size_t v_res_296_; lean_object* v_r_297_; 
v_a_boxed_294_ = lean_unbox_usize(v_a_292_);
lean_dec(v_a_292_);
v_b_boxed_295_ = lean_unbox_usize(v_b_293_);
lean_dec(v_b_293_);
v_res_296_ = lean_usize_add(v_a_boxed_294_, v_b_boxed_295_);
v_r_297_ = lean_box_usize(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT void l_USize_sub_0interp(lean_interpreter_value* stack)
{
size_t v_a_298_ = stack[0].m_num;
size_t v_b_299_ = stack[1].m_num;
size_t v_res_300_;
v_res_300_ = lean_usize_sub(v_a_298_, v_b_299_);
stack->m_num = v_res_300_;
}
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object* v_a_301_, lean_object* v_b_302_){
_start:
{
size_t v_a_boxed_303_; size_t v_b_boxed_304_; size_t v_res_305_; lean_object* v_r_306_; 
v_a_boxed_303_ = lean_unbox_usize(v_a_301_);
lean_dec(v_a_301_);
v_b_boxed_304_ = lean_unbox_usize(v_b_302_);
lean_dec(v_b_302_);
v_res_305_ = lean_usize_sub(v_a_boxed_303_, v_b_boxed_304_);
v_r_306_ = lean_box_usize(v_res_305_);
return v_r_306_;
}
}
size_t l_USize_instOfNat(lean_object* v_n_307_){
_start:
{
size_t v___x_308_; 
v___x_308_ = lean_usize_of_nat(v_n_307_);
return v___x_308_;
}
}
LEAN_EXPORT void l_USize_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_307_ = stack[0].m_obj;
size_t v_res_309_;
v_res_309_ = l_USize_instOfNat(v_n_307_);
stack->m_num = v_res_309_;
}
LEAN_EXPORT lean_object* l_USize_instOfNat___boxed(lean_object* v_n_310_){
_start:
{
size_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_USize_instOfNat(v_n_310_);
lean_dec(v_n_310_);
v_r_312_ = lean_box_usize(v_res_311_);
return v_r_312_;
}
}
static lean_object* _init_l_instLTUSize(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_box(0);
return v___x_317_;
}
}
static lean_object* _init_l_instLEUSize(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
LEAN_EXPORT void l_USize_decLt_0interp(lean_interpreter_value* stack)
{
size_t v_a_319_ = stack[0].m_num;
size_t v_b_320_ = stack[1].m_num;
uint8_t v_res_321_;
v_res_321_ = lean_usize_dec_lt(v_a_319_, v_b_320_);
stack->m_num = v_res_321_;
}
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
size_t v_a_boxed_324_; size_t v_b_boxed_325_; uint8_t v_res_326_; lean_object* v_r_327_; 
v_a_boxed_324_ = lean_unbox_usize(v_a_322_);
lean_dec(v_a_322_);
v_b_boxed_325_ = lean_unbox_usize(v_b_323_);
lean_dec(v_b_323_);
v_res_326_ = lean_usize_dec_lt(v_a_boxed_324_, v_b_boxed_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT void l_USize_decLe_0interp(lean_interpreter_value* stack)
{
size_t v_a_328_ = stack[0].m_num;
size_t v_b_329_ = stack[1].m_num;
uint8_t v_res_330_;
v_res_330_ = lean_usize_dec_le(v_a_328_, v_b_329_);
stack->m_num = v_res_330_;
}
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object* v_a_331_, lean_object* v_b_332_){
_start:
{
size_t v_a_boxed_333_; size_t v_b_boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_a_boxed_333_ = lean_unbox_usize(v_a_331_);
lean_dec(v_a_331_);
v_b_boxed_334_ = lean_unbox_usize(v_b_332_);
lean_dec(v_b_332_);
v_res_335_ = lean_usize_dec_le(v_a_boxed_333_, v_b_boxed_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
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
