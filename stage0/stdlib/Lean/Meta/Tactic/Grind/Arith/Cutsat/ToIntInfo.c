// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ToIntInfo
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Util import Lean.Meta.LitValues
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_co_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_co_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ci_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ci_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_io_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_io_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ii_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ii_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_lo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_hi_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "`grind` internal error, `.ci` interval support has not been implemented yet"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "`grind` internal error, `.io` interval support has not been implemented yet"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1));
v___x_10_ = l_Lean_Expr_const___override(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_box(0);
v___x_12_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default;
return v___x_15_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(lean_object* v_b_16_){
_start:
{
lean_object* v_ival_x3f_17_; 
v_ival_x3f_17_ = lean_ctor_get(v_b_16_, 1);
if (lean_obj_tag(v_ival_x3f_17_) == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 0;
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = 1;
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral___boxed(lean_object* v_b_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(v_b_20_);
lean_dec_ref(v_b_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx(lean_object* v_x_23_){
_start:
{
switch(lean_obj_tag(v_x_23_))
{
case 0:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(0u);
return v___x_24_;
}
case 1:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(1u);
return v___x_25_;
}
case 2:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(2u);
return v___x_26_;
}
default: 
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(3u);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(lean_object* v_t_30_, lean_object* v_k_31_){
_start:
{
switch(lean_obj_tag(v_t_30_))
{
case 0:
{
lean_object* v_lo_32_; lean_object* v_hi_33_; lean_object* v___x_34_; 
v_lo_32_ = lean_ctor_get(v_t_30_, 0);
lean_inc_ref(v_lo_32_);
v_hi_33_ = lean_ctor_get(v_t_30_, 1);
lean_inc_ref(v_hi_33_);
lean_dec_ref(v_t_30_);
v___x_34_ = lean_apply_2(v_k_31_, v_lo_32_, v_hi_33_);
return v___x_34_;
}
case 3:
{
return v_k_31_;
}
default: 
{
lean_object* v_lo_35_; lean_object* v___x_36_; 
v_lo_35_ = lean_ctor_get(v_t_30_, 0);
lean_inc_ref(v_lo_35_);
lean_dec(v_t_30_);
v___x_36_ = lean_apply_1(v_k_31_, v_lo_35_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim(lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_k_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_39_, v_k_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___boxed(lean_object* v_motive_43_, lean_object* v_ctorIdx_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_k_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim(v_motive_43_, v_ctorIdx_44_, v_t_45_, v_h_46_, v_k_47_);
lean_dec(v_ctorIdx_44_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_co_elim___redArg(lean_object* v_t_49_, lean_object* v_co_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_49_, v_co_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_co_elim(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_co_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_53_, v_co_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ci_elim___redArg(lean_object* v_t_57_, lean_object* v_ci_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_57_, v_ci_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ci_elim(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_ci_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_61_, v_ci_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_io_elim___redArg(lean_object* v_t_65_, lean_object* v_io_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_65_, v_io_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_io_elim(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_io_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_69_, v_io_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ii_elim___redArg(lean_object* v_t_73_, lean_object* v_ii_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_73_, v_ii_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ii_elim(lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_ii_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_77_, v_ii_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default;
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default;
return v___x_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite(lean_object* v_i_85_){
_start:
{
switch(lean_obj_tag(v_i_85_))
{
case 0:
{
uint8_t v___x_86_; 
v___x_86_ = 1;
return v___x_86_;
}
case 3:
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
default: 
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite___boxed(lean_object* v_i_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite(v_i_89_);
lean_dec(v_i_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_lo_x3f(lean_object* v_i_92_){
_start:
{
switch(lean_obj_tag(v_i_92_))
{
case 0:
{
lean_object* v_lo_93_; lean_object* v___x_94_; 
v_lo_93_ = lean_ctor_get(v_i_92_, 0);
lean_inc_ref(v_lo_93_);
lean_dec_ref(v_i_92_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_lo_93_);
return v___x_94_;
}
case 1:
{
lean_object* v_lo_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_lo_95_ = lean_ctor_get(v_i_92_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_i_92_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v_i_92_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_lo_95_);
lean_dec(v_i_92_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_lo_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
default: 
{
lean_object* v___x_103_; 
lean_dec(v_i_92_);
v___x_103_ = lean_box(0);
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_hi_x3f(lean_object* v_i_104_){
_start:
{
switch(lean_obj_tag(v_i_104_))
{
case 0:
{
lean_object* v_hi_105_; lean_object* v___x_106_; 
v_hi_105_ = lean_ctor_get(v_i_104_, 1);
lean_inc_ref(v_hi_105_);
lean_dec_ref(v_i_104_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v_hi_105_);
return v___x_106_;
}
case 2:
{
lean_object* v_hi_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_hi_107_ = lean_ctor_get(v_i_104_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v_i_104_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v_i_104_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_hi_107_);
lean_dec(v_i_104_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 1);
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_hi_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
default: 
{
lean_object* v___x_115_; 
lean_dec(v_i_104_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0(lean_object* v_msgData_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; lean_object* v_env_123_; lean_object* v___x_124_; lean_object* v_mctx_125_; lean_object* v_lctx_126_; lean_object* v_options_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_122_ = lean_st_ref_get(v___y_120_);
v_env_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc_ref(v_env_123_);
lean_dec(v___x_122_);
v___x_124_ = lean_st_ref_get(v___y_118_);
v_mctx_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc_ref(v_mctx_125_);
lean_dec(v___x_124_);
v_lctx_126_ = lean_ctor_get(v___y_117_, 2);
v_options_127_ = lean_ctor_get(v___y_119_, 2);
lean_inc_ref(v_options_127_);
lean_inc_ref(v_lctx_126_);
v___x_128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_128_, 0, v_env_123_);
lean_ctor_set(v___x_128_, 1, v_mctx_125_);
lean_ctor_set(v___x_128_, 2, v_lctx_126_);
lean_ctor_set(v___x_128_, 3, v_options_127_);
v___x_129_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_msgData_116_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0___boxed(lean_object* v_msgData_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0(v_msgData_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(lean_object* v_msg_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_ref_144_; lean_object* v___x_145_; lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_ref_144_ = lean_ctor_get(v___y_141_, 5);
v___x_145_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0(v_msg_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_154_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
lean_inc(v_ref_144_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v_ref_144_);
lean_ctor_set(v___x_150_, 1, v_a_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set_tag(v___x_148_, 1);
lean_ctor_set(v___x_148_, 0, v___x_150_);
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg___boxed(lean_object* v_msg_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v_msg_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_161_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1));
v___x_166_ = l_Lean_stringToMessageData(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3));
v___x_169_ = l_Lean_stringToMessageData(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(lean_object* v_i_170_, lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
switch(lean_obj_tag(v_i_170_))
{
case 0:
{
lean_object* v_lo_177_; lean_object* v_hi_178_; lean_object* v_val_179_; lean_object* v_ival_x3f_180_; 
v_lo_177_ = lean_ctor_get(v_i_170_, 0);
lean_inc_ref(v_lo_177_);
v_hi_178_ = lean_ctor_get(v_i_170_, 1);
lean_inc_ref(v_hi_178_);
lean_dec_ref(v_i_170_);
v_val_179_ = lean_ctor_get(v_lo_177_, 0);
lean_inc_ref(v_val_179_);
v_ival_x3f_180_ = lean_ctor_get(v_lo_177_, 1);
lean_inc(v_ival_x3f_180_);
lean_dec_ref(v_lo_177_);
if (lean_obj_tag(v_ival_x3f_180_) == 1)
{
lean_object* v_ival_x3f_188_; 
v_ival_x3f_188_ = lean_ctor_get(v_hi_178_, 1);
if (lean_obj_tag(v_ival_x3f_188_) == 1)
{
lean_object* v_val_189_; lean_object* v_val_190_; lean_object* v_val_191_; lean_object* v___x_192_; 
lean_inc_ref(v_ival_x3f_188_);
lean_dec_ref(v_val_179_);
v_val_189_ = lean_ctor_get(v_ival_x3f_180_, 0);
lean_inc(v_val_189_);
lean_dec_ref(v_ival_x3f_180_);
v_val_190_ = lean_ctor_get(v_hi_178_, 0);
lean_inc_ref(v_val_190_);
lean_dec_ref(v_hi_178_);
v_val_191_ = lean_ctor_get(v_ival_x3f_188_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v_ival_x3f_188_);
lean_inc_ref(v_x_171_);
v___x_192_ = l_Lean_Meta_getIntValue_x3f(v_x_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_221_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_221_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_221_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_221_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
if (lean_obj_tag(v_a_193_) == 1)
{
lean_object* v_val_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec_ref(v_val_190_);
lean_dec_ref(v_x_171_);
v_val_197_ = lean_ctor_get(v_a_193_, 0);
lean_inc(v_val_197_);
lean_dec_ref(v_a_193_);
v___x_198_ = lean_int_sub(v_val_197_, v_val_189_);
lean_dec(v_val_197_);
v___x_199_ = lean_int_sub(v_val_191_, v_val_189_);
lean_dec(v_val_191_);
v___x_200_ = lean_int_emod(v___x_198_, v___x_199_);
lean_dec(v___x_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_int_add(v___x_200_, v_val_189_);
lean_dec(v_val_189_);
lean_dec(v___x_200_);
v___x_202_ = l_Lean_mkIntLit(v___x_201_);
lean_dec(v___x_201_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_202_);
v___x_204_ = v___x_195_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
else
{
lean_object* v___x_206_; uint8_t v___x_207_; 
lean_dec(v_a_193_);
v___x_206_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0);
v___x_207_ = lean_int_dec_eq(v_val_189_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec_ref(v_val_190_);
v___x_208_ = l_Lean_mkIntLit(v_val_189_);
lean_inc_ref(v___x_208_);
v___x_209_ = l_Lean_mkIntSub(v_x_171_, v___x_208_);
v___x_210_ = lean_int_sub(v_val_191_, v_val_189_);
lean_dec(v_val_189_);
lean_dec(v_val_191_);
v___x_211_ = l_Lean_mkIntLit(v___x_210_);
lean_dec(v___x_210_);
v___x_212_ = l_Lean_mkIntMod(v___x_209_, v___x_211_);
v___x_213_ = l_Lean_mkIntAdd(v___x_212_, v___x_208_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_213_);
v___x_215_ = v___x_195_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_219_; 
lean_dec(v_val_191_);
lean_dec(v_val_189_);
v___x_217_ = l_Lean_mkIntMod(v_x_171_, v_val_190_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_217_);
v___x_219_ = v___x_195_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v_val_191_);
lean_dec_ref(v_val_190_);
lean_dec(v_val_189_);
lean_dec_ref(v_x_171_);
v_a_222_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_192_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_192_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_val_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_241_; 
v_val_230_ = lean_ctor_get(v_ival_x3f_180_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_ival_x3f_180_);
if (v_isSharedCheck_241_ == 0)
{
v___x_232_ = v_ival_x3f_180_;
v_isShared_233_ = v_isSharedCheck_241_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_val_230_);
lean_dec(v_ival_x3f_180_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_241_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_val_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_val_234_ = lean_ctor_get(v_hi_178_, 0);
v___x_235_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0);
v___x_236_ = lean_int_dec_eq(v_val_230_, v___x_235_);
lean_dec(v_val_230_);
if (v___x_236_ == 0)
{
lean_del_object(v___x_232_);
goto v___jp_181_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_inc_ref(v_val_234_);
lean_dec_ref(v_val_179_);
lean_dec_ref(v_hi_178_);
v___x_237_ = l_Lean_mkIntMod(v_x_171_, v_val_234_);
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 0);
lean_ctor_set(v___x_232_, 0, v___x_237_);
v___x_239_ = v___x_232_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
else
{
lean_dec(v_ival_x3f_180_);
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v_val_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_val_182_ = lean_ctor_get(v_hi_178_, 0);
lean_inc_ref(v_val_182_);
lean_dec_ref(v_hi_178_);
lean_inc_ref(v_val_179_);
v___x_183_ = l_Lean_mkIntSub(v_x_171_, v_val_179_);
lean_inc_ref(v_val_179_);
v___x_184_ = l_Lean_mkIntSub(v_val_182_, v_val_179_);
v___x_185_ = l_Lean_mkIntMod(v___x_183_, v___x_184_);
v___x_186_ = l_Lean_mkIntAdd(v___x_185_, v_val_179_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
case 1:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v_i_170_);
lean_dec_ref(v_x_171_);
v___x_242_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2);
v___x_243_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v___x_242_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_243_;
}
case 2:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_i_170_);
lean_dec_ref(v_x_171_);
v___x_244_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4);
v___x_245_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v___x_244_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_245_;
}
default: 
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_x_171_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___boxed(lean_object* v_i_247_, lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(v_i_247_, v_x_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0(lean_object* v_00_u03b1_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___boxed(lean_object* v_00_u03b1_263_, lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0(v_00_u03b1_263_, v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_271_ = lean_box(0);
v___x_272_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default;
v___x_273_ = lean_box(0);
v___x_274_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
lean_ctor_set(v___x_276_, 3, v___x_274_);
lean_ctor_set(v___x_276_, 4, v___x_274_);
lean_ctor_set(v___x_276_, 5, v___x_272_);
lean_ctor_set(v___x_276_, 6, v___x_274_);
lean_ctor_set(v___x_276_, 7, v___x_274_);
lean_ctor_set(v___x_276_, 8, v___x_271_);
lean_ctor_set(v___x_276_, 9, v___x_274_);
lean_ctor_set(v___x_276_, 10, v___x_274_);
lean_ctor_set(v___x_276_, 11, v___x_271_);
lean_ctor_set(v___x_276_, 12, v___x_271_);
lean_ctor_set(v___x_276_, 13, v___x_271_);
lean_ctor_set(v___x_276_, 14, v___x_271_);
lean_ctor_set(v___x_276_, 15, v___x_271_);
lean_ctor_set(v___x_276_, 16, v___x_271_);
lean_ctor_set(v___x_276_, 17, v___x_271_);
lean_ctor_set(v___x_276_, 18, v___x_271_);
lean_ctor_set(v___x_276_, 19, v___x_271_);
lean_ctor_set(v___x_276_, 20, v___x_271_);
lean_ctor_set(v___x_276_, 21, v___x_271_);
lean_ctor_set(v___x_276_, 22, v___x_271_);
lean_ctor_set(v___x_276_, 23, v___x_271_);
lean_ctor_set(v___x_276_, 24, v___x_271_);
lean_ctor_set(v___x_276_, 25, v___x_271_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
return v___x_278_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
}
#ifdef __cplusplus
}
#endif
