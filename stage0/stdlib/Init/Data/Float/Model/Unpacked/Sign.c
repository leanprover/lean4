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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_instBEqSign_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instBEqSign_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_UnpackedFloat_instBEqSign___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_UnpackedFloat_instBEqSign_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_UnpackedFloat_instBEqSign___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_instBEqSign___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_UnpackedFloat_instBEqSign = (const lean_object*)&l_Float_Model_UnpackedFloat_instBEqSign___closed__0_value;
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
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_instBEqSign_beq(uint8_t v_x_93_, uint8_t v_y_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_x_93_);
v___x_96_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_y_94_);
v___x_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
lean_dec(v___x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instBEqSign_beq___boxed(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v_x_17__boxed_100_; uint8_t v_y_18__boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_x_17__boxed_100_ = lean_unbox(v_x_98_);
v_y_18__boxed_101_ = lean_unbox(v_y_99_);
v_res_102_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_x_17__boxed_100_, v_y_18__boxed_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(uint8_t v_x_106_, uint8_t v_x_107_){
_start:
{
if (v_x_106_ == 0)
{
if (v_x_107_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 1;
return v___x_108_;
}
else
{
return v_x_106_;
}
}
else
{
return v_x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instMul___lam__0___boxed(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_x_35__boxed_111_; uint8_t v_x_36__boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_x_35__boxed_111_ = lean_unbox(v_x_109_);
v_x_36__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(v_x_35__boxed_111_, v_x_36__boxed_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(uint8_t v_x_118_){
_start:
{
if (v_x_118_ == 0)
{
uint8_t v___x_119_; 
v___x_119_ = 1;
return v___x_119_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0___boxed(lean_object* v_x_121_){
_start:
{
uint8_t v_x_22__boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_x_22__boxed_122_ = lean_unbox(v_x_121_);
v_res_123_ = l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(v_x_22__boxed_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(uint8_t v_x_127_, uint8_t v_x_128_){
_start:
{
if (v_x_127_ == 0)
{
if (v_x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
else
{
if (v_x_128_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 2;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 1;
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_x_40__boxed_135_; uint8_t v_x_41__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_x_40__boxed_135_ = lean_unbox(v_x_133_);
v_x_41__boxed_136_ = lean_unbox(v_x_134_);
v_res_137_ = l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(v_x_40__boxed_135_, v_x_41__boxed_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t v_s_141_, lean_object* v_n_142_){
_start:
{
if (v_s_141_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_int_neg(v_n_142_);
return v___x_143_;
}
else
{
lean_inc(v_n_142_);
return v_n_142_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply___boxed(lean_object* v_s_144_, lean_object* v_n_145_){
_start:
{
uint8_t v_s_boxed_146_; lean_object* v_res_147_; 
v_s_boxed_146_ = lean_unbox(v_s_144_);
v_res_147_ = l_Float_Model_UnpackedFloat_Sign_apply(v_s_boxed_146_, v_n_145_);
lean_dec(v_n_145_);
return v_res_147_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = l_BitVec_ofNat(v___x_148_, v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = l_BitVec_ofNat(v___x_151_, v___x_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec(uint8_t v_x_153_){
_start:
{
if (v_x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0);
return v___x_154_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec___boxed(lean_object* v_x_156_){
_start:
{
uint8_t v_x_45__boxed_157_; lean_object* v_res_158_; 
v_x_45__boxed_157_ = lean_unbox(v_x_156_);
v_res_158_ = l_Float_Model_UnpackedFloat_Sign_toBitVec(v_x_45__boxed_157_);
return v_res_158_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_ofBitVec(lean_object* v_b_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
v___x_161_ = lean_nat_dec_eq(v_b_159_, v___x_160_);
if (v___x_161_ == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 1;
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofBitVec___boxed(lean_object* v_b_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Float_Model_UnpackedFloat_Sign_ofBitVec(v_b_164_);
lean_dec(v_b_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
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
