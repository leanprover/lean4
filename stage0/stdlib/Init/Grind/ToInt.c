// Lean compiler output
// Module: Init.Grind.ToInt
// Imports: import Init.LawfulBEqTactics public import Init.Data.Int.DivMod.Basic public meta import Init.Grind.Tactics import Init.ByCases import Init.Data.Int.DivMod.Lemmas import Init.Omega
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_co_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_co_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ci_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ci_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_io_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_io_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ii_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ii_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqIntInterval_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqIntInterval_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instBEqIntInterval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instBEqIntInterval_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instBEqIntInterval___closed__0 = (const lean_object*)&l_Lean_Grind_instBEqIntInterval___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instBEqIntInterval = (const lean_object*)&l_Lean_Grind_instBEqIntInterval___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instDecidableEqIntInterval_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instDecidableEqIntInterval_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instDecidableEqIntInterval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instDecidableEqIntInterval___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_instInhabitedIntInterval_default___closed__0;
static lean_once_cell_t l_Lean_Grind_instInhabitedIntInterval_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_instInhabitedIntInterval_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_instInhabitedIntInterval_default;
LEAN_EXPORT lean_object* l_Lean_Grind_instInhabitedIntInterval;
static lean_once_cell_t l_Lean_Grind_IntInterval_uint___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_IntInterval_uint___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_lo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_hi_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_nonEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_nonEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_isFinite(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_isFinite___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_instMembershipInt;
static lean_once_cell_t l_Lean_Grind_IntInterval_wrap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_IntInterval_wrap___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_toIntUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__0 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__0_value;
static const lean_string_object l_Lean_Grind_toIntUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__1 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__1_value;
static const lean_string_object l_Lean_Grind_toIntUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__2 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__2_value;
static const lean_string_object l_Lean_Grind_toIntUnexpander___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__3 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__3_value;
static const lean_ctor_object l_Lean_Grind_toIntUnexpander___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_toIntUnexpander___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__4_value_aux_0),((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_toIntUnexpander___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__4_value_aux_1),((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Grind_toIntUnexpander___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__4_value_aux_2),((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__4 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__4_value;
static const lean_string_object l_Lean_Grind_toIntUnexpander___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coeNotation"};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__5 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__5_value;
static const lean_ctor_object l_Lean_Grind_toIntUnexpander___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_toIntUnexpander___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 100, 71, 170, 251, 12, 50, 58)}};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__6 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__6_value;
static const lean_string_object l_Lean_Grind_toIntUnexpander___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↑"};
static const lean_object* l_Lean_Grind_toIntUnexpander___closed__7 = (const lean_object*)&l_Lean_Grind_toIntUnexpander___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Grind_toIntUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_toIntUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Grind_IntInterval_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
switch(lean_obj_tag(v_t_8_))
{
case 0:
{
lean_object* v_lo_10_; lean_object* v_hi_11_; lean_object* v___x_12_; 
v_lo_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_lo_10_);
v_hi_11_ = lean_ctor_get(v_t_8_, 1);
lean_inc(v_hi_11_);
lean_dec_ref(v_t_8_);
v___x_12_ = lean_apply_2(v_k_9_, v_lo_10_, v_hi_11_);
return v___x_12_;
}
case 3:
{
return v_k_9_;
}
default: 
{
lean_object* v_lo_13_; lean_object* v___x_14_; 
v_lo_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_lo_13_);
lean_dec(v_t_8_);
v___x_14_ = lean_apply_1(v_k_9_, v_lo_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Grind_IntInterval_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_co_elim___redArg(lean_object* v_t_27_, lean_object* v_co_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_27_, v_co_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_co_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_co_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_31_, v_co_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ci_elim___redArg(lean_object* v_t_35_, lean_object* v_ci_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_35_, v_ci_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ci_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_ci_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_39_, v_ci_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_io_elim___redArg(lean_object* v_t_43_, lean_object* v_io_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_43_, v_io_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_io_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_io_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_47_, v_io_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ii_elim___redArg(lean_object* v_t_51_, lean_object* v_ii_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_51_, v_ii_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_ii_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_ii_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_55_, v_ii_57_);
return v___x_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqIntInterval_beq(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
switch(lean_obj_tag(v_x_59_))
{
case 0:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_lo_61_; lean_object* v_hi_62_; lean_object* v_lo_63_; lean_object* v_hi_64_; uint8_t v___x_65_; 
v_lo_61_ = lean_ctor_get(v_x_59_, 0);
v_hi_62_ = lean_ctor_get(v_x_59_, 1);
v_lo_63_ = lean_ctor_get(v_x_60_, 0);
v_hi_64_ = lean_ctor_get(v_x_60_, 1);
v___x_65_ = lean_int_dec_eq(v_lo_61_, v_lo_63_);
if (v___x_65_ == 0)
{
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = lean_int_dec_eq(v_hi_62_, v_hi_64_);
return v___x_66_;
}
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
case 1:
{
if (lean_obj_tag(v_x_60_) == 1)
{
lean_object* v_lo_68_; lean_object* v_lo_69_; uint8_t v___x_70_; 
v_lo_68_ = lean_ctor_get(v_x_59_, 0);
v_lo_69_ = lean_ctor_get(v_x_60_, 0);
v___x_70_ = lean_int_dec_eq(v_lo_68_, v_lo_69_);
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
case 2:
{
if (lean_obj_tag(v_x_60_) == 2)
{
lean_object* v_hi_72_; lean_object* v_hi_73_; uint8_t v___x_74_; 
v_hi_72_ = lean_ctor_get(v_x_59_, 0);
v_hi_73_ = lean_ctor_get(v_x_60_, 0);
v___x_74_ = lean_int_dec_eq(v_hi_72_, v_hi_73_);
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
default: 
{
if (lean_obj_tag(v_x_60_) == 3)
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqIntInterval_beq___boxed(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Grind_instBEqIntInterval_beq(v_x_78_, v_x_79_);
lean_dec(v_x_79_);
lean_dec(v_x_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter___redArg(lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_, lean_object* v_h__3_88_, lean_object* v_h__4_89_, lean_object* v_h__5_90_){
_start:
{
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
lean_dec(v_h__4_89_);
lean_dec(v_h__3_88_);
lean_dec(v_h__2_87_);
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_lo_91_; lean_object* v_hi_92_; lean_object* v_lo_93_; lean_object* v_hi_94_; lean_object* v___x_95_; 
lean_dec(v_h__5_90_);
v_lo_91_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_lo_91_);
v_hi_92_ = lean_ctor_get(v_x_84_, 1);
lean_inc(v_hi_92_);
lean_dec_ref(v_x_84_);
v_lo_93_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_lo_93_);
v_hi_94_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_hi_94_);
lean_dec_ref(v_x_85_);
v___x_95_ = lean_apply_4(v_h__1_86_, v_lo_91_, v_hi_92_, v_lo_93_, v_hi_94_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; 
lean_dec(v_h__1_86_);
v___x_96_ = lean_apply_6(v_h__5_90_, v_x_84_, v_x_85_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_96_;
}
}
case 1:
{
lean_dec(v_h__4_89_);
lean_dec(v_h__3_88_);
lean_dec(v_h__1_86_);
if (lean_obj_tag(v_x_85_) == 1)
{
lean_object* v_lo_97_; lean_object* v_lo_98_; lean_object* v___x_99_; 
lean_dec(v_h__5_90_);
v_lo_97_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_lo_97_);
lean_dec_ref(v_x_84_);
v_lo_98_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_lo_98_);
lean_dec_ref(v_x_85_);
v___x_99_ = lean_apply_2(v_h__2_87_, v_lo_97_, v_lo_98_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; 
lean_dec(v_h__2_87_);
v___x_100_ = lean_apply_6(v_h__5_90_, v_x_84_, v_x_85_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_100_;
}
}
case 2:
{
lean_dec(v_h__4_89_);
lean_dec(v_h__2_87_);
lean_dec(v_h__1_86_);
if (lean_obj_tag(v_x_85_) == 2)
{
lean_object* v_hi_101_; lean_object* v_hi_102_; lean_object* v___x_103_; 
lean_dec(v_h__5_90_);
v_hi_101_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_hi_101_);
lean_dec_ref(v_x_84_);
v_hi_102_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_hi_102_);
lean_dec_ref(v_x_85_);
v___x_103_ = lean_apply_2(v_h__3_88_, v_hi_101_, v_hi_102_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_dec(v_h__3_88_);
v___x_104_ = lean_apply_6(v_h__5_90_, v_x_84_, v_x_85_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_104_;
}
}
default: 
{
lean_dec(v_h__3_88_);
lean_dec(v_h__2_87_);
lean_dec(v_h__1_86_);
if (lean_obj_tag(v_x_85_) == 3)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__5_90_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__4_89_, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
lean_dec(v_h__4_89_);
v___x_107_ = lean_apply_6(v_h__5_90_, v_x_84_, v_x_85_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter(lean_object* v_motive_108_, lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_, lean_object* v_h__4_114_, lean_object* v_h__5_115_){
_start:
{
switch(lean_obj_tag(v_x_109_))
{
case 0:
{
lean_dec(v_h__4_114_);
lean_dec(v_h__3_113_);
lean_dec(v_h__2_112_);
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v_lo_116_; lean_object* v_hi_117_; lean_object* v_lo_118_; lean_object* v_hi_119_; lean_object* v___x_120_; 
lean_dec(v_h__5_115_);
v_lo_116_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_lo_116_);
v_hi_117_ = lean_ctor_get(v_x_109_, 1);
lean_inc(v_hi_117_);
lean_dec_ref(v_x_109_);
v_lo_118_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_lo_118_);
v_hi_119_ = lean_ctor_get(v_x_110_, 1);
lean_inc(v_hi_119_);
lean_dec_ref(v_x_110_);
v___x_120_ = lean_apply_4(v_h__1_111_, v_lo_116_, v_hi_117_, v_lo_118_, v_hi_119_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_h__1_111_);
v___x_121_ = lean_apply_6(v_h__5_115_, v_x_109_, v_x_110_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_121_;
}
}
case 1:
{
lean_dec(v_h__4_114_);
lean_dec(v_h__3_113_);
lean_dec(v_h__1_111_);
if (lean_obj_tag(v_x_110_) == 1)
{
lean_object* v_lo_122_; lean_object* v_lo_123_; lean_object* v___x_124_; 
lean_dec(v_h__5_115_);
v_lo_122_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_lo_122_);
lean_dec_ref(v_x_109_);
v_lo_123_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_lo_123_);
lean_dec_ref(v_x_110_);
v___x_124_ = lean_apply_2(v_h__2_112_, v_lo_122_, v_lo_123_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
lean_dec(v_h__2_112_);
v___x_125_ = lean_apply_6(v_h__5_115_, v_x_109_, v_x_110_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_125_;
}
}
case 2:
{
lean_dec(v_h__4_114_);
lean_dec(v_h__2_112_);
lean_dec(v_h__1_111_);
if (lean_obj_tag(v_x_110_) == 2)
{
lean_object* v_hi_126_; lean_object* v_hi_127_; lean_object* v___x_128_; 
lean_dec(v_h__5_115_);
v_hi_126_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_hi_126_);
lean_dec_ref(v_x_109_);
v_hi_127_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_hi_127_);
lean_dec_ref(v_x_110_);
v___x_128_ = lean_apply_2(v_h__3_113_, v_hi_126_, v_hi_127_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
lean_dec(v_h__3_113_);
v___x_129_ = lean_apply_6(v_h__5_115_, v_x_109_, v_x_110_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_129_;
}
}
default: 
{
lean_dec(v_h__3_113_);
lean_dec(v_h__2_112_);
lean_dec(v_h__1_111_);
if (lean_obj_tag(v_x_110_) == 3)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__5_115_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__4_114_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
lean_dec(v_h__4_114_);
v___x_132_ = lean_apply_6(v_h__5_115_, v_x_109_, v_x_110_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_132_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instDecidableEqIntInterval_decEq(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
switch(lean_obj_tag(v_x_133_))
{
case 0:
{
lean_object* v_lo_135_; lean_object* v_hi_136_; uint8_t v___x_137_; 
v_lo_135_ = lean_ctor_get(v_x_133_, 0);
v_hi_136_ = lean_ctor_get(v_x_133_, 1);
v___x_137_ = 0;
switch(lean_obj_tag(v_x_134_))
{
case 0:
{
lean_object* v_lo_138_; lean_object* v_hi_139_; uint8_t v___x_140_; 
v_lo_138_ = lean_ctor_get(v_x_134_, 0);
v_hi_139_ = lean_ctor_get(v_x_134_, 1);
v___x_140_ = lean_int_dec_eq(v_lo_135_, v_lo_138_);
if (v___x_140_ == 0)
{
return v___x_137_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = lean_int_dec_eq(v_hi_136_, v_hi_139_);
if (v___x_141_ == 0)
{
return v___x_137_;
}
else
{
return v___x_141_;
}
}
}
case 3:
{
return v___x_137_;
}
default: 
{
return v___x_137_;
}
}
}
case 1:
{
lean_object* v_lo_142_; uint8_t v___x_143_; 
v_lo_142_ = lean_ctor_get(v_x_133_, 0);
v___x_143_ = 0;
switch(lean_obj_tag(v_x_134_))
{
case 1:
{
lean_object* v_lo_144_; uint8_t v___x_145_; 
v_lo_144_ = lean_ctor_get(v_x_134_, 0);
v___x_145_ = lean_int_dec_eq(v_lo_142_, v_lo_144_);
if (v___x_145_ == 0)
{
return v___x_143_;
}
else
{
return v___x_145_;
}
}
case 3:
{
return v___x_143_;
}
default: 
{
return v___x_143_;
}
}
}
case 2:
{
lean_object* v_hi_146_; uint8_t v___x_147_; 
v_hi_146_ = lean_ctor_get(v_x_133_, 0);
v___x_147_ = 0;
switch(lean_obj_tag(v_x_134_))
{
case 2:
{
lean_object* v_hi_148_; uint8_t v___x_149_; 
v_hi_148_ = lean_ctor_get(v_x_134_, 0);
v___x_149_ = lean_int_dec_eq(v_hi_146_, v_hi_148_);
if (v___x_149_ == 0)
{
return v___x_147_;
}
else
{
return v___x_149_;
}
}
case 3:
{
return v___x_147_;
}
default: 
{
return v___x_147_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_134_) == 3)
{
uint8_t v___x_150_; 
v___x_150_ = 1;
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instDecidableEqIntInterval_decEq___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lean_Grind_instDecidableEqIntInterval_decEq(v_x_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec(v_x_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instDecidableEqIntInterval(lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = l_Lean_Grind_instDecidableEqIntInterval_decEq(v_x_156_, v_x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instDecidableEqIntInterval___boxed(lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Grind_instDecidableEqIntInterval(v_x_159_, v_x_160_);
lean_dec(v_x_160_);
lean_dec(v_x_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
static lean_object* _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_nat_to_int(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__1(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_Lean_Grind_instInhabitedIntInterval_default___closed__0, &l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once, _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Grind_instInhabitedIntInterval_default(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Lean_Grind_instInhabitedIntInterval_default___closed__1, &l_Lean_Grind_instInhabitedIntInterval_default___closed__1_once, _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__1);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Grind_instInhabitedIntInterval(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Grind_instInhabitedIntInterval_default;
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Grind_IntInterval_uint___closed__0(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(2u);
v___x_170_ = lean_nat_to_int(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint(lean_object* v_n_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_obj_once(&l_Lean_Grind_instInhabitedIntInterval_default___closed__0, &l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once, _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0);
v___x_173_ = lean_obj_once(&l_Lean_Grind_IntInterval_uint___closed__0, &l_Lean_Grind_IntInterval_uint___closed__0_once, _init_l_Lean_Grind_IntInterval_uint___closed__0);
v___x_174_ = l_Int_pow(v___x_173_, v_n_171_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_172_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint___boxed(lean_object* v_n_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Grind_IntInterval_uint(v_n_176_);
lean_dec(v_n_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint(lean_object* v_n_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_179_ = lean_obj_once(&l_Lean_Grind_IntInterval_uint___closed__0, &l_Lean_Grind_IntInterval_uint___closed__0_once, _init_l_Lean_Grind_IntInterval_uint___closed__0);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_sub(v_n_178_, v___x_180_);
v___x_182_ = l_Int_pow(v___x_179_, v___x_181_);
lean_dec(v___x_181_);
v___x_183_ = lean_int_neg(v___x_182_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint___boxed(lean_object* v_n_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Grind_IntInterval_sint(v_n_185_);
lean_dec(v_n_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_lo_x3f(lean_object* v_i_187_){
_start:
{
switch(lean_obj_tag(v_i_187_))
{
case 0:
{
lean_object* v_lo_188_; lean_object* v___x_189_; 
v_lo_188_ = lean_ctor_get(v_i_187_, 0);
lean_inc(v_lo_188_);
lean_dec_ref(v_i_187_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_lo_188_);
return v___x_189_;
}
case 1:
{
lean_object* v_lo_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_lo_190_ = lean_ctor_get(v_i_187_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_i_187_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v_i_187_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_lo_190_);
lean_dec(v_i_187_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_lo_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
default: 
{
lean_object* v___x_198_; 
lean_dec(v_i_187_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_hi_x3f(lean_object* v_i_199_){
_start:
{
switch(lean_obj_tag(v_i_199_))
{
case 0:
{
lean_object* v_hi_200_; lean_object* v___x_201_; 
v_hi_200_ = lean_ctor_get(v_i_199_, 1);
lean_inc(v_hi_200_);
lean_dec_ref(v_i_199_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v_hi_200_);
return v___x_201_;
}
case 2:
{
lean_object* v_hi_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_hi_202_ = lean_ctor_get(v_i_199_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_i_199_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v_i_199_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_hi_202_);
lean_dec(v_i_199_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_hi_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
default: 
{
lean_object* v___x_210_; 
lean_dec(v_i_199_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_nonEmpty(lean_object* v_i_211_){
_start:
{
switch(lean_obj_tag(v_i_211_))
{
case 0:
{
lean_object* v_lo_212_; lean_object* v_hi_213_; uint8_t v___x_214_; 
v_lo_212_ = lean_ctor_get(v_i_211_, 0);
v_hi_213_ = lean_ctor_get(v_i_211_, 1);
v___x_214_ = lean_int_dec_lt(v_lo_212_, v_hi_213_);
return v___x_214_;
}
case 3:
{
uint8_t v___x_215_; 
v___x_215_ = 1;
return v___x_215_;
}
default: 
{
uint8_t v___x_216_; 
v___x_216_ = 1;
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_nonEmpty___boxed(lean_object* v_i_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Grind_IntInterval_nonEmpty(v_i_217_);
lean_dec(v_i_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(lean_object* v_i_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_, lean_object* v_h__3_223_, lean_object* v_h__4_224_){
_start:
{
switch(lean_obj_tag(v_i_220_))
{
case 0:
{
lean_object* v_lo_225_; lean_object* v_hi_226_; lean_object* v___x_227_; 
lean_dec(v_h__4_224_);
lean_dec(v_h__3_223_);
lean_dec(v_h__2_222_);
v_lo_225_ = lean_ctor_get(v_i_220_, 0);
lean_inc(v_lo_225_);
v_hi_226_ = lean_ctor_get(v_i_220_, 1);
lean_inc(v_hi_226_);
lean_dec_ref(v_i_220_);
v___x_227_ = lean_apply_2(v_h__1_221_, v_lo_225_, v_hi_226_);
return v___x_227_;
}
case 1:
{
lean_object* v_lo_228_; lean_object* v___x_229_; 
lean_dec(v_h__4_224_);
lean_dec(v_h__3_223_);
lean_dec(v_h__1_221_);
v_lo_228_ = lean_ctor_get(v_i_220_, 0);
lean_inc(v_lo_228_);
lean_dec_ref(v_i_220_);
v___x_229_ = lean_apply_1(v_h__2_222_, v_lo_228_);
return v___x_229_;
}
case 2:
{
lean_object* v_hi_230_; lean_object* v___x_231_; 
lean_dec(v_h__4_224_);
lean_dec(v_h__2_222_);
lean_dec(v_h__1_221_);
v_hi_230_ = lean_ctor_get(v_i_220_, 0);
lean_inc(v_hi_230_);
lean_dec_ref(v_i_220_);
v___x_231_ = lean_apply_1(v_h__3_223_, v_hi_230_);
return v___x_231_;
}
default: 
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_h__3_223_);
lean_dec(v_h__2_222_);
lean_dec(v_h__1_221_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_h__4_224_, v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(lean_object* v_motive_234_, lean_object* v_i_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_, lean_object* v_h__3_238_, lean_object* v_h__4_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(v_i_235_, v_h__1_236_, v_h__2_237_, v_h__3_238_, v_h__4_239_);
return v___x_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_isFinite(lean_object* v_i_241_){
_start:
{
switch(lean_obj_tag(v_i_241_))
{
case 0:
{
uint8_t v___x_242_; 
v___x_242_ = 1;
return v___x_242_;
}
case 3:
{
uint8_t v___x_243_; 
v___x_243_ = 0;
return v___x_243_;
}
default: 
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_isFinite___boxed(lean_object* v_i_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Lean_Grind_IntInterval_isFinite(v_i_245_);
lean_dec(v_i_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
static lean_object* _init_l_Lean_Grind_IntInterval_instMembershipInt(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_box(0);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Grind_IntInterval_wrap___closed__0(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_to_int(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap(lean_object* v_i_251_, lean_object* v_x_252_){
_start:
{
switch(lean_obj_tag(v_i_251_))
{
case 0:
{
lean_object* v_lo_253_; lean_object* v_hi_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_lo_253_ = lean_ctor_get(v_i_251_, 0);
v_hi_254_ = lean_ctor_get(v_i_251_, 1);
v___x_255_ = lean_int_sub(v_x_252_, v_lo_253_);
v___x_256_ = lean_int_sub(v_hi_254_, v_lo_253_);
v___x_257_ = lean_int_emod(v___x_255_, v___x_256_);
lean_dec(v___x_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_int_add(v___x_257_, v_lo_253_);
lean_dec(v___x_257_);
return v___x_258_;
}
case 1:
{
lean_object* v_lo_259_; uint8_t v___x_260_; 
v_lo_259_ = lean_ctor_get(v_i_251_, 0);
v___x_260_ = lean_int_dec_le(v_x_252_, v_lo_259_);
if (v___x_260_ == 0)
{
lean_inc(v_x_252_);
return v_x_252_;
}
else
{
lean_inc(v_lo_259_);
return v_lo_259_;
}
}
case 2:
{
lean_object* v_hi_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_hi_261_ = lean_ctor_get(v_i_251_, 0);
v___x_262_ = lean_obj_once(&l_Lean_Grind_IntInterval_wrap___closed__0, &l_Lean_Grind_IntInterval_wrap___closed__0_once, _init_l_Lean_Grind_IntInterval_wrap___closed__0);
v___x_263_ = lean_int_sub(v_hi_261_, v___x_262_);
v___x_264_ = lean_int_dec_le(v_x_252_, v___x_263_);
if (v___x_264_ == 0)
{
return v___x_263_;
}
else
{
lean_dec(v___x_263_);
lean_inc(v_x_252_);
return v_x_252_;
}
}
default: 
{
lean_inc(v_x_252_);
return v_x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap___boxed(lean_object* v_i_265_, lean_object* v_x_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Grind_IntInterval_wrap(v_i_265_, v_x_266_);
lean_dec(v_x_266_);
lean_dec(v_i_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_toIntUnexpander(lean_object* v_stx_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_Grind_toIntUnexpander___closed__4));
lean_inc(v_stx_281_);
v___x_285_ = l_Lean_Syntax_isOfKind(v_stx_281_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_stx_281_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_a_283_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = l_Lean_Syntax_getArg(v_stx_281_, v___x_288_);
lean_dec(v_stx_281_);
lean_inc(v___x_289_);
v___x_290_ = l_Lean_Syntax_matchesNull(v___x_289_, v___x_288_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v___x_289_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_a_283_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l_Lean_Syntax_getArg(v___x_289_, v___x_293_);
lean_dec(v___x_289_);
v___x_295_ = 0;
v___x_296_ = l_Lean_SourceInfo_fromRef(v_a_282_, v___x_295_);
v___x_297_ = ((lean_object*)(l_Lean_Grind_toIntUnexpander___closed__6));
v___x_298_ = ((lean_object*)(l_Lean_Grind_toIntUnexpander___closed__7));
lean_inc(v___x_296_);
v___x_299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_296_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = l_Lean_Syntax_node2(v___x_296_, v___x_297_, v___x_299_, v___x_294_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_a_283_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_toIntUnexpander___boxed(lean_object* v_stx_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Grind_toIntUnexpander(v_stx_302_, v_a_303_, v_a_304_);
lean_dec(v_a_303_);
return v_res_305_;
}
}
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instInhabitedIntInterval_default = _init_l_Lean_Grind_instInhabitedIntInterval_default();
lean_mark_persistent(l_Lean_Grind_instInhabitedIntInterval_default);
l_Lean_Grind_instInhabitedIntInterval = _init_l_Lean_Grind_instInhabitedIntInterval();
lean_mark_persistent(l_Lean_Grind_instInhabitedIntInterval);
l_Lean_Grind_IntInterval_instMembershipInt = _init_l_Lean_Grind_IntInterval_instMembershipInt();
lean_mark_persistent(l_Lean_Grind_IntInterval_instMembershipInt);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_ToInt(builtin);
}
#ifdef __cplusplus
}
#endif
