// Lean compiler output
// Module: Init.Data.String.Slice.Basic
// Imports: public import Init.Data.String.Basic public import Init.Data.String.FindPos public import Init.Data.String.Compare public import Init.Data.Ord.Basic import Init.Data.String.Pattern.Memcmp import Init.Omega
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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_memcmp_lt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp_compare(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
uint8_t lean_bool_to_uint8(uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instHAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instHAppend___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instHAppend___closed__0 = (const lean_object*)&l_String_Slice_instHAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instHAppend = (const lean_object*)&l_String_Slice_instHAppend___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instBEq___closed__0 = (const lean_object*)&l_String_Slice_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instBEq = (const lean_object*)&l_String_Slice_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toString___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instToString___closed__0 = (const lean_object*)&l_String_Slice_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instToString = (const lean_object*)&l_String_Slice_instToString___closed__0_value;
uint64_t lean_slice_hash(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_hash___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instHashable___closed__0 = (const lean_object*)&l_String_Slice_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instHashable = (const lean_object*)&l_String_Slice_instHashable___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_blt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instLT;
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instOrd___closed__0 = (const lean_object*)&l_String_Slice_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instOrd = (const lean_object*)&l_String_Slice_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instLE;
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instMin___closed__0 = (const lean_object*)&l_String_Slice_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instMin = (const lean_object*)&l_String_Slice_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instMax___closed__0 = (const lean_object*)&l_String_Slice_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instMax = (const lean_object*)&l_String_Slice_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_intercalate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_intercalate___closed__0 = (const lean_object*)&l_String_Slice_intercalate___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instToFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instToFormat___closed__0 = (const lean_object*)&l_String_Slice_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instToFormat = (const lean_object*)&l_String_Slice_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0(lean_object* v_s_1_, lean_object* v_t_2_){
_start:
{
lean_object* v_str_3_; lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_str_3_ = lean_ctor_get(v_t_2_, 0);
v_startInclusive_4_ = lean_ctor_get(v_t_2_, 1);
v_endExclusive_5_ = lean_ctor_get(v_t_2_, 2);
v___x_6_ = lean_string_utf8_extract_fast(v_str_3_, v_startInclusive_4_, v_endExclusive_5_);
v___x_7_ = lean_string_append(v_s_1_, v___x_6_);
lean_dec_ref(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0___boxed(lean_object* v_s_8_, lean_object* v_t_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_String_Slice_instHAppend___lam__0(v_s_8_, v_t_9_);
lean_dec_ref(v_t_9_);
return v_res_10_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_beq(lean_object* v_s1_13_, lean_object* v_s2_14_){
_start:
{
lean_object* v_str_15_; lean_object* v_startInclusive_16_; lean_object* v_endExclusive_17_; lean_object* v_str_18_; lean_object* v_startInclusive_19_; lean_object* v_endExclusive_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_str_15_ = lean_ctor_get(v_s1_13_, 0);
v_startInclusive_16_ = lean_ctor_get(v_s1_13_, 1);
v_endExclusive_17_ = lean_ctor_get(v_s1_13_, 2);
v_str_18_ = lean_ctor_get(v_s2_14_, 0);
v_startInclusive_19_ = lean_ctor_get(v_s2_14_, 1);
v_endExclusive_20_ = lean_ctor_get(v_s2_14_, 2);
v___x_21_ = lean_nat_sub(v_endExclusive_17_, v_startInclusive_16_);
v___x_22_ = lean_nat_sub(v_endExclusive_20_, v_startInclusive_19_);
v___x_23_ = lean_nat_dec_eq(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
if (v___x_23_ == 0)
{
lean_dec(v___x_21_);
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_string_memcmp(v_str_15_, v_str_18_, v_startInclusive_16_, v_startInclusive_19_, v___x_21_);
lean_dec(v___x_21_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_beq___boxed(lean_object* v_s1_25_, lean_object* v_s2_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_String_Slice_beq(v_s1_25_, v_s2_26_);
lean_dec_ref(v_s2_26_);
lean_dec_ref(v_s1_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString(lean_object* v_s_31_){
_start:
{
lean_object* v_str_32_; lean_object* v_startInclusive_33_; lean_object* v_endExclusive_34_; lean_object* v___x_35_; 
v_str_32_ = lean_ctor_get(v_s_31_, 0);
v_startInclusive_33_ = lean_ctor_get(v_s_31_, 1);
v_endExclusive_34_ = lean_ctor_get(v_s_31_, 2);
v___x_35_ = lean_string_utf8_extract_fast(v_str_32_, v_startInclusive_33_, v_endExclusive_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString___boxed(lean_object* v_s_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_String_Slice_toString(v_s_36_);
lean_dec_ref(v_s_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_hash___boxed(lean_object* v_s_41_){
_start:
{
uint64_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lean_slice_hash(v_s_41_);
lean_dec_ref(v_s_41_);
v_r_43_ = lean_box_uint64(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_blt(lean_object* v_s_46_, lean_object* v_t_47_){
_start:
{
lean_object* v_str_48_; lean_object* v_startInclusive_49_; lean_object* v_endExclusive_50_; lean_object* v_str_51_; lean_object* v_startInclusive_52_; lean_object* v_endExclusive_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v_str_48_ = lean_ctor_get(v_s_46_, 0);
v_startInclusive_49_ = lean_ctor_get(v_s_46_, 1);
v_endExclusive_50_ = lean_ctor_get(v_s_46_, 2);
v_str_51_ = lean_ctor_get(v_t_47_, 0);
v_startInclusive_52_ = lean_ctor_get(v_t_47_, 1);
v_endExclusive_53_ = lean_ctor_get(v_t_47_, 2);
v___x_54_ = lean_nat_sub(v_endExclusive_50_, v_startInclusive_49_);
v___x_55_ = lean_nat_sub(v_endExclusive_53_, v_startInclusive_52_);
v___x_56_ = lean_nat_dec_lt(v___x_54_, v___x_55_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
lean_dec(v___x_54_);
v___x_57_ = lean_string_memcmp_lt(v_str_48_, v_str_51_, v_startInclusive_49_, v_startInclusive_52_, v___x_55_);
lean_dec(v___x_55_);
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
lean_dec(v___x_55_);
v___x_58_ = lean_string_memcmp_lt(v_str_51_, v_str_48_, v_startInclusive_52_, v_startInclusive_49_, v___x_54_);
lean_dec(v___x_54_);
if (v___x_58_ == 0)
{
return v___x_56_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_blt___boxed(lean_object* v_s_60_, lean_object* v_t_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_String_Slice_blt(v_s_60_, v_t_61_);
lean_dec_ref(v_t_61_);
lean_dec_ref(v_s_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
static lean_object* _init_l_String_Slice_instLT(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLT(lean_object* v_x_65_, lean_object* v_y_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = l_String_Slice_blt(v_x_65_, v_y_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLT___boxed(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_String_Slice_instDecidableLT(v_x_68_, v_y_69_);
lean_dec_ref(v_y_69_);
lean_dec_ref(v_x_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_compare(lean_object* v_s_72_, lean_object* v_t_73_){
_start:
{
lean_object* v_str_74_; lean_object* v_startInclusive_75_; lean_object* v_endExclusive_76_; lean_object* v_str_77_; lean_object* v_startInclusive_78_; lean_object* v_endExclusive_79_; lean_object* v___y_81_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_str_74_ = lean_ctor_get(v_s_72_, 0);
v_startInclusive_75_ = lean_ctor_get(v_s_72_, 1);
v_endExclusive_76_ = lean_ctor_get(v_s_72_, 2);
v_str_77_ = lean_ctor_get(v_t_73_, 0);
v_startInclusive_78_ = lean_ctor_get(v_t_73_, 1);
v_endExclusive_79_ = lean_ctor_get(v_t_73_, 2);
v___x_89_ = lean_nat_sub(v_endExclusive_76_, v_startInclusive_75_);
v___x_90_ = lean_nat_sub(v_endExclusive_79_, v_startInclusive_78_);
v___x_91_ = lean_nat_dec_le(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v___x_89_);
v___y_81_ = v___x_90_;
goto v___jp_80_;
}
else
{
lean_dec(v___x_90_);
v___y_81_ = v___x_89_;
goto v___jp_80_;
}
v___jp_80_:
{
uint8_t v___x_82_; 
v___x_82_ = lean_string_memcmp_compare(v_str_74_, v_str_77_, v_startInclusive_75_, v_startInclusive_78_, v___y_81_);
lean_dec(v___y_81_);
if (v___x_82_ == 1)
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_nat_sub(v_endExclusive_76_, v_startInclusive_75_);
v___x_84_ = lean_nat_sub(v_endExclusive_79_, v_startInclusive_78_);
v___x_85_ = lean_nat_dec_lt(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = lean_nat_dec_eq(v___x_83_, v___x_84_);
lean_dec(v___x_84_);
lean_dec(v___x_83_);
if (v___x_86_ == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 2;
return v___x_87_;
}
else
{
return v___x_82_;
}
}
else
{
uint8_t v___x_88_; 
lean_dec(v___x_84_);
lean_dec(v___x_83_);
v___x_88_ = 0;
return v___x_88_;
}
}
else
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_compare___boxed(lean_object* v_s_92_, lean_object* v_t_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_String_Slice_compare(v_s_92_, v_t_93_);
lean_dec_ref(v_t_93_);
lean_dec_ref(v_s_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
static lean_object* _init_l_String_Slice_instLE(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(0);
return v___x_98_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLE(lean_object* v_x_99_, lean_object* v_y_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = l_String_Slice_blt(v_y_100_, v_x_99_);
if (v___x_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = 1;
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLE___boxed(lean_object* v_x_104_, lean_object* v_y_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_String_Slice_instDecidableLE(v_x_104_, v_y_105_);
lean_dec_ref(v_y_105_);
lean_dec_ref(v_x_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instMin___lam__0(lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = l_String_Slice_instDecidableLE(v_a_108_, v_b_109_);
if (v___x_110_ == 0)
{
lean_inc_ref(v_b_109_);
return v_b_109_;
}
else
{
lean_inc_ref(v_a_108_);
return v_a_108_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instMin___lam__0___boxed(lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_String_Slice_instMin___lam__0(v_a_111_, v_b_112_);
lean_dec_ref(v_b_112_);
lean_dec_ref(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instMax___lam__0(lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = l_String_Slice_instDecidableLE(v_b_117_, v_a_116_);
if (v___x_118_ == 0)
{
lean_inc_ref(v_b_117_);
return v_b_117_;
}
else
{
lean_inc_ref(v_a_116_);
return v_a_116_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instMax___lam__0___boxed(lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_String_Slice_instMax___lam__0(v_a_119_, v_b_120_);
lean_dec_ref(v_b_120_);
lean_dec_ref(v_a_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_124_, lean_object* v_n_125_){
_start:
{
lean_object* v_str_126_; lean_object* v_startInclusive_127_; lean_object* v_endExclusive_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_str_126_ = lean_ctor_get(v_s_124_, 0);
lean_inc_ref(v_str_126_);
v_startInclusive_127_ = lean_ctor_get(v_s_124_, 1);
lean_inc(v_startInclusive_127_);
v_endExclusive_128_ = lean_ctor_get(v_s_124_, 2);
lean_inc(v_endExclusive_128_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_String_Slice_Pos_nextn(v_s_124_, v___x_129_, v_n_125_);
v_isSharedCheck_138_ = !lean_is_exclusive(v_s_124_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_139_ = lean_ctor_get(v_s_124_, 2);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_s_124_, 1);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_s_124_, 0);
lean_dec(v_unused_141_);
v___x_132_ = v_s_124_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_dec(v_s_124_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_nat_add(v_startInclusive_127_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v_startInclusive_127_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_str_126_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_endExclusive_128_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_142_, lean_object* v_n_143_){
_start:
{
lean_object* v_str_144_; lean_object* v_startInclusive_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_str_144_ = lean_ctor_get(v_s_142_, 0);
lean_inc_ref(v_str_144_);
v_startInclusive_145_ = lean_ctor_get(v_s_142_, 1);
lean_inc(v_startInclusive_145_);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_String_Slice_Pos_nextn(v_s_142_, v___x_146_, v_n_143_);
v_isSharedCheck_155_ = !lean_is_exclusive(v_s_142_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_156_ = lean_ctor_get(v_s_142_, 2);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_s_142_, 1);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_s_142_, 0);
lean_dec(v_unused_158_);
v___x_149_ = v_s_142_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_s_142_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_nat_add(v_startInclusive_145_, v___x_147_);
lean_dec(v___x_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 2, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_str_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_startInclusive_145_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_159_, lean_object* v_n_160_){
_start:
{
lean_object* v_str_161_; lean_object* v_startInclusive_162_; lean_object* v_endExclusive_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_str_161_ = lean_ctor_get(v_s_159_, 0);
lean_inc_ref(v_str_161_);
v_startInclusive_162_ = lean_ctor_get(v_s_159_, 1);
lean_inc(v_startInclusive_162_);
v_endExclusive_163_ = lean_ctor_get(v_s_159_, 2);
v___x_164_ = lean_nat_sub(v_endExclusive_163_, v_startInclusive_162_);
v___x_165_ = l_String_Slice_Pos_prevn(v_s_159_, v___x_164_, v_n_160_);
v_isSharedCheck_173_ = !lean_is_exclusive(v_s_159_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; 
v_unused_174_ = lean_ctor_get(v_s_159_, 2);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_s_159_, 1);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_s_159_, 0);
lean_dec(v_unused_176_);
v___x_167_ = v_s_159_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_dec(v_s_159_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_nat_add(v_startInclusive_162_, v___x_165_);
lean_dec(v___x_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 2, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_str_161_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_startInclusive_162_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_177_, lean_object* v_n_178_){
_start:
{
lean_object* v_str_179_; lean_object* v_startInclusive_180_; lean_object* v_endExclusive_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_str_179_ = lean_ctor_get(v_s_177_, 0);
lean_inc_ref(v_str_179_);
v_startInclusive_180_ = lean_ctor_get(v_s_177_, 1);
lean_inc(v_startInclusive_180_);
v_endExclusive_181_ = lean_ctor_get(v_s_177_, 2);
lean_inc(v_endExclusive_181_);
v___x_182_ = lean_nat_sub(v_endExclusive_181_, v_startInclusive_180_);
v___x_183_ = l_String_Slice_Pos_prevn(v_s_177_, v___x_182_, v_n_178_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_s_177_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; 
v_unused_192_ = lean_ctor_get(v_s_177_, 2);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_s_177_, 1);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_s_177_, 0);
lean_dec(v_unused_194_);
v___x_185_ = v_s_177_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_dec(v_s_177_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_nat_add(v_startInclusive_180_, v___x_183_);
lean_dec(v___x_183_);
lean_dec(v_startInclusive_180_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_str_179_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_endExclusive_181_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_195_, lean_object* v_s1Curr_196_, lean_object* v_s2_197_, lean_object* v_s2Curr_198_){
_start:
{
lean_object* v_str_199_; lean_object* v_startInclusive_200_; lean_object* v_endExclusive_201_; lean_object* v___x_202_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_str_199_ = lean_ctor_get(v_s1_195_, 0);
v_startInclusive_200_ = lean_ctor_get(v_s1_195_, 1);
v_endExclusive_201_ = lean_ctor_get(v_s1_195_, 2);
v___x_202_ = lean_nat_sub(v_endExclusive_201_, v_startInclusive_200_);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_s1Curr_196_, v___x_209_);
v___x_211_ = lean_nat_dec_le(v___x_210_, v___x_202_);
if (v___x_211_ == 0)
{
lean_dec(v___x_210_);
goto v___jp_203_;
}
else
{
lean_object* v_str_212_; lean_object* v_startInclusive_213_; lean_object* v_endExclusive_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_str_212_ = lean_ctor_get(v_s2_197_, 0);
v_startInclusive_213_ = lean_ctor_get(v_s2_197_, 1);
v_endExclusive_214_ = lean_ctor_get(v_s2_197_, 2);
v___x_215_ = lean_nat_sub(v_endExclusive_214_, v_startInclusive_213_);
v___x_216_ = lean_nat_add(v_s2Curr_198_, v___x_209_);
v___x_217_ = lean_nat_dec_le(v___x_216_, v___x_215_);
lean_dec(v___x_215_);
if (v___x_217_ == 0)
{
lean_dec(v___x_216_);
lean_dec(v___x_210_);
goto v___jp_203_;
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; uint8_t v___x_225_; uint8_t v___x_226_; uint8_t v_c1_227_; lean_object* v___x_228_; uint8_t v___x_229_; uint8_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; uint8_t v_c2_234_; uint8_t v___x_235_; 
lean_dec(v___x_202_);
v___x_218_ = lean_nat_add(v_startInclusive_200_, v_s1Curr_196_);
lean_dec(v_s1Curr_196_);
v___x_219_ = lean_string_get_byte_fast(v_str_199_, v___x_218_);
v___x_220_ = 65;
v___x_221_ = lean_uint8_sub(v___x_219_, v___x_220_);
v___x_222_ = 26;
v___x_223_ = lean_uint8_dec_lt(v___x_221_, v___x_222_);
v___x_224_ = lean_bool_to_uint8(v___x_223_);
v___x_225_ = 5;
v___x_226_ = lean_uint8_shift_left(v___x_224_, v___x_225_);
v_c1_227_ = lean_uint8_add(v___x_219_, v___x_226_);
v___x_228_ = lean_nat_add(v_startInclusive_213_, v_s2Curr_198_);
lean_dec(v_s2Curr_198_);
v___x_229_ = lean_string_get_byte_fast(v_str_212_, v___x_228_);
v___x_230_ = lean_uint8_sub(v___x_229_, v___x_220_);
v___x_231_ = lean_uint8_dec_lt(v___x_230_, v___x_222_);
v___x_232_ = lean_bool_to_uint8(v___x_231_);
v___x_233_ = lean_uint8_shift_left(v___x_232_, v___x_225_);
v_c2_234_ = lean_uint8_add(v___x_229_, v___x_233_);
v___x_235_ = lean_uint8_dec_eq(v_c1_227_, v_c2_234_);
if (v___x_235_ == 0)
{
lean_dec(v___x_216_);
lean_dec(v___x_210_);
return v___x_235_;
}
else
{
v_s1Curr_196_ = v___x_210_;
v_s2Curr_198_ = v___x_216_;
goto _start;
}
}
}
v___jp_203_:
{
uint8_t v_decide_204_; 
v_decide_204_ = lean_nat_dec_eq(v_s1Curr_196_, v___x_202_);
lean_dec(v___x_202_);
lean_dec(v_s1Curr_196_);
if (v_decide_204_ == 0)
{
lean_dec(v_s2Curr_198_);
return v_decide_204_;
}
else
{
lean_object* v_startInclusive_205_; lean_object* v_endExclusive_206_; lean_object* v___x_207_; uint8_t v_decide_208_; 
v_startInclusive_205_ = lean_ctor_get(v_s2_197_, 1);
v_endExclusive_206_ = lean_ctor_get(v_s2_197_, 2);
v___x_207_ = lean_nat_sub(v_endExclusive_206_, v_startInclusive_205_);
v_decide_208_ = lean_nat_dec_eq(v_s2Curr_198_, v___x_207_);
lean_dec(v___x_207_);
lean_dec(v_s2Curr_198_);
return v_decide_208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_237_, lean_object* v_s1Curr_238_, lean_object* v_s2_239_, lean_object* v_s2Curr_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_237_, v_s1Curr_238_, v_s2_239_, v_s2Curr_240_);
lean_dec_ref(v_s2_239_);
lean_dec_ref(v_s1_237_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_243_, lean_object* v_s2_244_){
_start:
{
lean_object* v_startInclusive_245_; lean_object* v_endExclusive_246_; lean_object* v_startInclusive_247_; lean_object* v_endExclusive_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_startInclusive_245_ = lean_ctor_get(v_s1_243_, 1);
v_endExclusive_246_ = lean_ctor_get(v_s1_243_, 2);
v_startInclusive_247_ = lean_ctor_get(v_s2_244_, 1);
v_endExclusive_248_ = lean_ctor_get(v_s2_244_, 2);
v___x_249_ = lean_nat_sub(v_endExclusive_246_, v_startInclusive_245_);
v___x_250_ = lean_nat_sub(v_endExclusive_248_, v_startInclusive_247_);
v___x_251_ = lean_nat_dec_eq(v___x_249_, v___x_250_);
lean_dec(v___x_250_);
lean_dec(v___x_249_);
if (v___x_251_ == 0)
{
return v___x_251_;
}
else
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_243_, v___x_252_, v_s2_244_, v___x_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_254_, lean_object* v_s2_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_254_, v_s2_255_);
lean_dec_ref(v_s2_255_);
lean_dec_ref(v_s1_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = l_String_Slice_Pos_get_x3f(v_s_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_String_Slice_front_x3f(v_s_261_);
lean_dec_ref(v_s_261_);
return v_res_262_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = l_String_Slice_Pos_get_x3f(v_s_263_, v___x_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
uint32_t v___x_266_; 
v___x_266_ = 65;
return v___x_266_;
}
else
{
lean_object* v_val_267_; uint32_t v___x_268_; 
v_val_267_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v___x_265_, 1);
v___x_268_ = lean_unbox_uint32(v_val_267_);
lean_dec(v_val_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_269_){
_start:
{
uint32_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_String_Slice_front(v_s_269_);
lean_dec_ref(v_s_269_);
v_r_271_ = lean_box_uint32(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_272_){
_start:
{
lean_object* v_startInclusive_273_; lean_object* v_endExclusive_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_startInclusive_273_ = lean_ctor_get(v_s_272_, 1);
v_endExclusive_274_ = lean_ctor_get(v_s_272_, 2);
v___x_275_ = lean_nat_sub(v_endExclusive_274_, v_startInclusive_273_);
v___x_276_ = l_String_Slice_Pos_prev_x3f(v_s_272_, v___x_275_);
lean_dec(v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; 
v_val_278_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v___x_276_, 1);
v___x_279_ = l_String_Slice_Pos_get_x3f(v_s_272_, v_val_278_);
lean_dec(v_val_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_String_Slice_back_x3f(v_s_280_);
lean_dec_ref(v_s_280_);
return v_res_281_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_282_){
_start:
{
lean_object* v_startInclusive_283_; lean_object* v_endExclusive_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_startInclusive_283_ = lean_ctor_get(v_s_282_, 1);
v_endExclusive_284_ = lean_ctor_get(v_s_282_, 2);
v___x_285_ = lean_nat_sub(v_endExclusive_284_, v_startInclusive_283_);
v___x_286_ = l_String_Slice_Pos_prev_x3f(v_s_282_, v___x_285_);
lean_dec(v___x_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
uint32_t v___x_287_; 
v___x_287_ = 65;
return v___x_287_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_289_; 
v_val_288_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_288_);
lean_dec_ref_known(v___x_286_, 1);
v___x_289_ = l_String_Slice_Pos_get_x3f(v_s_282_, v_val_288_);
lean_dec(v_val_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
uint32_t v___x_290_; 
v___x_290_ = 65;
return v___x_290_;
}
else
{
lean_object* v_val_291_; uint32_t v___x_292_; 
v_val_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_289_, 1);
v___x_292_ = lean_unbox_uint32(v_val_291_);
lean_dec(v_val_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_293_){
_start:
{
uint32_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_String_Slice_back(v_s_293_);
lean_dec_ref(v_s_293_);
v_r_295_ = lean_box_uint32(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(lean_object* v_acc_296_, lean_object* v_s_297_, lean_object* v_a_298_){
_start:
{
if (lean_obj_tag(v_a_298_) == 0)
{
return v_acc_296_;
}
else
{
lean_object* v_head_299_; lean_object* v_tail_300_; lean_object* v_str_301_; lean_object* v_startInclusive_302_; lean_object* v_endExclusive_303_; lean_object* v_str_304_; lean_object* v_startInclusive_305_; lean_object* v_endExclusive_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_head_299_ = lean_ctor_get(v_a_298_, 0);
v_tail_300_ = lean_ctor_get(v_a_298_, 1);
v_str_301_ = lean_ctor_get(v_s_297_, 0);
v_startInclusive_302_ = lean_ctor_get(v_s_297_, 1);
v_endExclusive_303_ = lean_ctor_get(v_s_297_, 2);
v_str_304_ = lean_ctor_get(v_head_299_, 0);
v_startInclusive_305_ = lean_ctor_get(v_head_299_, 1);
v_endExclusive_306_ = lean_ctor_get(v_head_299_, 2);
v___x_307_ = lean_string_utf8_extract_fast(v_str_301_, v_startInclusive_302_, v_endExclusive_303_);
v___x_308_ = lean_string_append(v_acc_296_, v___x_307_);
lean_dec_ref(v___x_307_);
v___x_309_ = lean_string_utf8_extract_fast(v_str_304_, v_startInclusive_305_, v_endExclusive_306_);
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
lean_dec_ref(v___x_309_);
v_acc_296_ = v___x_310_;
v_a_298_ = v_tail_300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_312_, lean_object* v_s_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(v_acc_312_, v_s_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_s_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v___x_319_; 
v___x_319_ = ((lean_object*)(l_String_Slice_intercalate___closed__0));
return v___x_319_;
}
else
{
lean_object* v_head_320_; lean_object* v_tail_321_; lean_object* v_str_322_; lean_object* v_startInclusive_323_; lean_object* v_endExclusive_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_head_320_ = lean_ctor_get(v_x_318_, 0);
v_tail_321_ = lean_ctor_get(v_x_318_, 1);
v_str_322_ = lean_ctor_get(v_head_320_, 0);
v_startInclusive_323_ = lean_ctor_get(v_head_320_, 1);
v_endExclusive_324_ = lean_ctor_get(v_head_320_, 2);
v___x_325_ = lean_string_utf8_extract_fast(v_str_322_, v_startInclusive_323_, v_endExclusive_324_);
v___x_326_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(v___x_325_, v_s_317_, v_tail_321_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_String_Slice_intercalate(v_s_327_, v_x_328_);
lean_dec(v_x_328_);
lean_dec_ref(v_s_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
return v_x_330_;
}
else
{
lean_object* v_head_332_; lean_object* v_tail_333_; lean_object* v_str_334_; lean_object* v_startInclusive_335_; lean_object* v_endExclusive_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_head_332_ = lean_ctor_get(v_x_331_, 0);
v_tail_333_ = lean_ctor_get(v_x_331_, 1);
v_str_334_ = lean_ctor_get(v_head_332_, 0);
v_startInclusive_335_ = lean_ctor_get(v_head_332_, 1);
v_endExclusive_336_ = lean_ctor_get(v_head_332_, 2);
v___x_337_ = lean_string_utf8_extract_fast(v_str_334_, v_startInclusive_335_, v_endExclusive_336_);
v___x_338_ = lean_string_append(v_x_330_, v___x_337_);
lean_dec_ref(v___x_337_);
v_x_330_ = v___x_338_;
v_x_331_ = v_tail_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_340_, v_x_341_);
lean_dec(v_x_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object* v_l_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_String_Slice_intercalate___closed__0));
v___x_345_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_344_, v_l_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object* v_l_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_String_Slice_join(v_l_346_);
lean_dec(v_l_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = l_String_Slice_toString(v_s_348_);
v___x_350_ = l_String_toName(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_String_Slice_toName(v_s_351_);
lean_dec_ref(v_s_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_353_){
_start:
{
lean_object* v_str_354_; lean_object* v_startInclusive_355_; lean_object* v_endExclusive_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_str_354_ = lean_ctor_get(v_s_353_, 0);
v_startInclusive_355_ = lean_ctor_get(v_s_353_, 1);
v_endExclusive_356_ = lean_ctor_get(v_s_353_, 2);
v___x_357_ = lean_string_utf8_extract_fast(v_str_354_, v_startInclusive_355_, v_endExclusive_356_);
v___x_358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_String_Slice_instToFormat___lam__0(v_s_359_);
lean_dec_ref(v_s_359_);
return v_res_360_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_instLT = _init_l_String_Slice_instLT();
lean_mark_persistent(l_String_Slice_instLT);
l_String_Slice_instLE = _init_l_String_Slice_instLE();
lean_mark_persistent(l_String_Slice_instLE);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Slice_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
