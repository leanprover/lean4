// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Sign
// Imports: public import Init.Data.Int.Basic public import Init.Data.BitVec.Basic public import Init.Data.Repr public import Init.Data.Ord.Basic
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Float_Model_UnpackedFloat_instReprSign_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Float.Model.UnpackedFloat.Sign.negative"};
static const lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_instReprSign_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__0_value)}};
static const lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__1_value;
static const lean_string_object l_Float_Model_UnpackedFloat_instReprSign_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Float.Model.UnpackedFloat.Sign.positive"};
static const lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___closed__2 = (const lean_object*)&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__2_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_instReprSign_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__2_value)}};
static const lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___closed__3 = (const lean_object*)&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__3_value;
static lean_once_cell_t l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4;
static lean_once_cell_t l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_UnpackedFloat_instReprSign___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_UnpackedFloat_instReprSign_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_UnpackedFloat_instReprSign___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_instReprSign___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_UnpackedFloat_instReprSign = (const lean_object*)&l_Float_Model_UnpackedFloat_instReprSign___closed__0_value;
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_instDecidableEqSign(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instDecidableEqSign___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instMul___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_UnpackedFloat_Sign_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_UnpackedFloat_Sign_instMul___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_UnpackedFloat_Sign_instMul___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_Sign_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_UnpackedFloat_Sign_instMul = (const lean_object*)&l_Float_Model_UnpackedFloat_Sign_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_UnpackedFloat_Sign_instDiv = (const lean_object*)&l_Float_Model_UnpackedFloat_Sign_instMul___closed__0_value;
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Float_Model_UnpackedFloat_Sign_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_UnpackedFloat_Sign_instNeg___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_Sign_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_UnpackedFloat_Sign_instNeg = (const lean_object*)&l_Float_Model_UnpackedFloat_Sign_instNeg___closed__0_value;
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_UnpackedFloat_Sign_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_UnpackedFloat_Sign_instOrd___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_Sign_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_UnpackedFloat_Sign_instOrd = (const lean_object*)&l_Float_Model_UnpackedFloat_Sign_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec(uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_ofBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofBitVec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Float_Model_UnpackedFloat_Sign_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Float_Model_UnpackedFloat_Sign_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg(lean_object* v_negative_27_){
_start:
{
lean_inc(v_negative_27_);
return v_negative_27_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg___boxed(lean_object* v_negative_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg(v_negative_28_);
lean_dec(v_negative_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_negative_33_){
_start:
{
lean_inc(v_negative_33_);
return v_negative_33_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_negative_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Float_Model_UnpackedFloat_Sign_negative_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_negative_37_);
lean_dec(v_negative_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg(lean_object* v_positive_40_){
_start:
{
lean_inc(v_positive_40_);
return v_positive_40_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg___boxed(lean_object* v_positive_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg(v_positive_41_);
lean_dec(v_positive_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_positive_46_){
_start:
{
lean_inc(v_positive_46_);
return v_positive_46_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_positive_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Float_Model_UnpackedFloat_Sign_positive_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_positive_50_);
lean_dec(v_positive_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr(uint8_t v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___y_66_; lean_object* v___y_73_; 
if (v_x_63_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_64_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4);
v___y_66_ = v___x_81_;
goto v___jp_65_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5);
v___y_66_ = v___x_82_;
goto v___jp_65_;
}
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1024u);
v___x_84_ = lean_nat_dec_le(v___x_83_, v_prec_64_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4);
v___y_73_ = v___x_85_;
goto v___jp_72_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5);
v___y_73_ = v___x_86_;
goto v___jp_72_;
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = ((lean_object*)(l_Float_Model_UnpackedFloat_instReprSign_repr___closed__1));
lean_inc(v___y_66_);
v___x_68_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = 0;
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___x_69_);
v___x_71_ = l_Repr_addAppParen(v___x_70_, v_prec_64_);
return v___x_71_;
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = ((lean_object*)(l_Float_Model_UnpackedFloat_instReprSign_repr___closed__3));
lean_inc(v___y_73_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___y_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = 0;
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_64_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_121__boxed_89_; lean_object* v_res_90_; 
v_x_121__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_x_121__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_ofNat(lean_object* v_n_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_le(v_n_93_, v___x_94_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofNat___boxed(lean_object* v_n_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Float_Model_UnpackedFloat_Sign_ofNat(v_n_98_);
lean_dec(v_n_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_instDecidableEqSign(uint8_t v_x_101_, uint8_t v_y_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_x_101_);
v___x_104_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_y_102_);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
lean_dec(v___x_104_);
lean_dec(v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instDecidableEqSign___boxed(lean_object* v_x_106_, lean_object* v_y_107_){
_start:
{
uint8_t v_x_13__boxed_108_; uint8_t v_y_14__boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_x_13__boxed_108_ = lean_unbox(v_x_106_);
v_y_14__boxed_109_ = lean_unbox(v_y_107_);
v_res_110_ = l_Float_Model_UnpackedFloat_instDecidableEqSign(v_x_13__boxed_108_, v_y_14__boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(uint8_t v_x_112_, uint8_t v_x_113_){
_start:
{
if (v_x_112_ == 0)
{
if (v_x_113_ == 0)
{
uint8_t v___x_114_; 
v___x_114_ = 1;
return v___x_114_;
}
else
{
return v_x_112_;
}
}
else
{
return v_x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instMul___lam__0___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_x_35__boxed_117_; uint8_t v_x_36__boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_x_35__boxed_117_ = lean_unbox(v_x_115_);
v_x_36__boxed_118_ = lean_unbox(v_x_116_);
v_res_119_ = l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(v_x_35__boxed_117_, v_x_36__boxed_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(uint8_t v_x_124_){
_start:
{
if (v_x_124_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 1;
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0___boxed(lean_object* v_x_127_){
_start:
{
uint8_t v_x_22__boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_x_22__boxed_128_ = lean_unbox(v_x_127_);
v_res_129_ = l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(v_x_22__boxed_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(uint8_t v_x_133_, uint8_t v_x_134_){
_start:
{
if (v_x_133_ == 0)
{
if (v_x_134_ == 0)
{
uint8_t v___x_135_; 
v___x_135_ = 1;
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
else
{
if (v_x_134_ == 0)
{
uint8_t v___x_137_; 
v___x_137_ = 2;
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = 1;
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0___boxed(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
uint8_t v_x_40__boxed_141_; uint8_t v_x_41__boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_x_40__boxed_141_ = lean_unbox(v_x_139_);
v_x_41__boxed_142_ = lean_unbox(v_x_140_);
v_res_143_ = l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(v_x_40__boxed_141_, v_x_41__boxed_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t v_s_147_, lean_object* v_n_148_){
_start:
{
if (v_s_147_ == 0)
{
lean_object* v___x_149_; 
v___x_149_ = lean_int_neg(v_n_148_);
return v___x_149_;
}
else
{
lean_inc(v_n_148_);
return v_n_148_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply___boxed(lean_object* v_s_150_, lean_object* v_n_151_){
_start:
{
uint8_t v_s_boxed_152_; lean_object* v_res_153_; 
v_s_boxed_152_ = lean_unbox(v_s_150_);
v_res_153_ = l_Float_Model_UnpackedFloat_Sign_apply(v_s_boxed_152_, v_n_151_);
lean_dec(v_n_151_);
return v_res_153_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = l_BitVec_ofNat(v___x_154_, v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = l_BitVec_ofNat(v___x_157_, v___x_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec(uint8_t v_x_159_){
_start:
{
if (v_x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0);
return v___x_160_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec___boxed(lean_object* v_x_162_){
_start:
{
uint8_t v_x_45__boxed_163_; lean_object* v_res_164_; 
v_x_45__boxed_163_ = lean_unbox(v_x_162_);
v_res_164_ = l_Float_Model_UnpackedFloat_Sign_toBitVec(v_x_45__boxed_163_);
return v_res_164_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_ofBitVec(lean_object* v_b_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
v___x_167_ = lean_nat_dec_eq(v_b_165_, v___x_166_);
if (v___x_167_ == 0)
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
else
{
uint8_t v___x_169_; 
v___x_169_ = 1;
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofBitVec___boxed(lean_object* v_b_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Float_Model_UnpackedFloat_Sign_ofBitVec(v_b_170_);
lean_dec(v_b_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Sign(builtin);
}
#ifdef __cplusplus
}
#endif
