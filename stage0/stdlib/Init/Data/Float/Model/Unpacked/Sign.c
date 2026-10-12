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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Float_Model_UnpackedFloat_Sign_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Float_Model_UnpackedFloat_Sign_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg(lean_object* v_negative_24_){
_start:
{
lean_inc(v_negative_24_);
return v_negative_24_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg___boxed(lean_object* v_negative_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg(v_negative_25_);
lean_dec(v_negative_25_);
return v_res_26_;
}
}
lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_negative_30_){
_start:
{
lean_inc(v_negative_30_);
return v_negative_30_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_negative_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_negative_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Float_Model_UnpackedFloat_Sign_negative_elim(lean_box(0), v_t_28_, lean_box(0), v_negative_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_negative_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Float_Model_UnpackedFloat_Sign_negative_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_negative_35_);
lean_dec(v_negative_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg(lean_object* v_positive_38_){
_start:
{
lean_inc(v_positive_38_);
return v_positive_38_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg___boxed(lean_object* v_positive_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg(v_positive_39_);
lean_dec(v_positive_39_);
return v_res_40_;
}
}
lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_positive_44_){
_start:
{
lean_inc(v_positive_44_);
return v_positive_44_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_positive_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_positive_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Float_Model_UnpackedFloat_Sign_positive_elim(lean_box(0), v_t_42_, lean_box(0), v_positive_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_positive_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Float_Model_UnpackedFloat_Sign_positive_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_positive_49_);
lean_dec(v_positive_49_);
return v_res_51_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(2u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr(uint8_t v_x_62_, lean_object* v_prec_63_){
_start:
{
lean_object* v___y_65_; lean_object* v___y_72_; 
if (v_x_62_ == 0)
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_63_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4);
v___y_65_ = v___x_80_;
goto v___jp_64_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5);
v___y_65_ = v___x_81_;
goto v___jp_64_;
}
}
else
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1024u);
v___x_83_ = lean_nat_dec_le(v___x_82_, v_prec_63_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4);
v___y_72_ = v___x_84_;
goto v___jp_71_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5);
v___y_72_ = v___x_85_;
goto v___jp_71_;
}
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = ((lean_object*)(l_Float_Model_UnpackedFloat_instReprSign_repr___closed__1));
lean_inc(v___y_65_);
v___x_67_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_67_, 0, v___y_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
v___x_70_ = l_Repr_addAppParen(v___x_69_, v_prec_63_);
return v___x_70_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l_Float_Model_UnpackedFloat_instReprSign_repr___closed__3));
lean_inc(v___y_72_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_63_);
return v___x_77_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_instReprSign_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_62_ = stack[0].m_num;
lean_object* v_prec_63_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_x_62_, v_prec_63_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_117__boxed_89_; lean_object* v_res_90_; 
v_x_117__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_x_117__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
uint8_t l_Float_Model_UnpackedFloat_Sign_ofNat(lean_object* v_n_93_){
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
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_93_ = stack[0].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_Float_Model_UnpackedFloat_Sign_ofNat(v_n_93_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofNat___boxed(lean_object* v_n_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Float_Model_UnpackedFloat_Sign_ofNat(v_n_99_);
lean_dec(v_n_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
uint8_t l_Float_Model_UnpackedFloat_instDecidableEqSign(uint8_t v_x_102_, uint8_t v_y_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_104_ = lean_box(v_x_102_);
v___x_105_ = lean_obj_tag_nat(v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_box(v_y_103_);
v___x_107_ = lean_obj_tag_nat(v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = lean_nat_dec_eq(v___x_105_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_instDecidableEqSign_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_102_ = stack[0].m_num;
uint8_t v_y_103_ = stack[1].m_num;
uint8_t v_res_109_;
v_res_109_ = l_Float_Model_UnpackedFloat_instDecidableEqSign(v_x_102_, v_y_103_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instDecidableEqSign___boxed(lean_object* v_x_110_, lean_object* v_y_111_){
_start:
{
uint8_t v_x_23__boxed_112_; uint8_t v_y_24__boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_23__boxed_112_ = lean_unbox(v_x_110_);
v_y_24__boxed_113_ = lean_unbox(v_y_111_);
v_res_114_ = l_Float_Model_UnpackedFloat_instDecidableEqSign(v_x_23__boxed_112_, v_y_24__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
uint8_t l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(uint8_t v_x_116_, uint8_t v_x_117_){
_start:
{
if (v_x_116_ == 0)
{
if (v_x_117_ == 0)
{
uint8_t v___x_118_; 
v___x_118_ = 1;
return v___x_118_;
}
else
{
return v_x_116_;
}
}
else
{
return v_x_117_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_instMul___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_116_ = stack[0].m_num;
uint8_t v_x_117_ = stack[1].m_num;
uint8_t v_res_119_;
v_res_119_ = l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(v_x_116_, v_x_117_);
stack->m_num = v_res_119_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instMul___lam__0___boxed(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_x_35__boxed_122_; uint8_t v_x_36__boxed_123_; uint8_t v_res_124_; lean_object* v_r_125_; 
v_x_35__boxed_122_ = lean_unbox(v_x_120_);
v_x_36__boxed_123_ = lean_unbox(v_x_121_);
v_res_124_ = l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(v_x_35__boxed_122_, v_x_36__boxed_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
uint8_t l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(uint8_t v_x_129_){
_start:
{
if (v_x_129_ == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 1;
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_129_ = stack[0].m_num;
uint8_t v_res_132_;
v_res_132_ = l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(v_x_129_);
stack->m_num = v_res_132_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0___boxed(lean_object* v_x_133_){
_start:
{
uint8_t v_x_22__boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_x_22__boxed_134_ = lean_unbox(v_x_133_);
v_res_135_ = l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(v_x_22__boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
uint8_t l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(uint8_t v_x_139_, uint8_t v_x_140_){
_start:
{
if (v_x_139_ == 0)
{
if (v_x_140_ == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
else
{
if (v_x_140_ == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 2;
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_139_ = stack[0].m_num;
uint8_t v_x_140_ = stack[1].m_num;
uint8_t v_res_145_;
v_res_145_ = l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(v_x_139_, v_x_140_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0___boxed(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_x_40__boxed_148_; uint8_t v_x_41__boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_x_40__boxed_148_ = lean_unbox(v_x_146_);
v_x_41__boxed_149_ = lean_unbox(v_x_147_);
v_res_150_ = l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(v_x_40__boxed_148_, v_x_41__boxed_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t v_s_154_, lean_object* v_n_155_){
_start:
{
if (v_s_154_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_int_neg(v_n_155_);
return v___x_156_;
}
else
{
lean_inc(v_n_155_);
return v_n_155_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_apply_0interp(lean_interpreter_value* stack)
{
uint8_t v_s_154_ = stack[0].m_num;
lean_object* v_n_155_ = stack[1].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Float_Model_UnpackedFloat_Sign_apply(v_s_154_, v_n_155_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply___boxed(lean_object* v_s_158_, lean_object* v_n_159_){
_start:
{
uint8_t v_s_boxed_160_; lean_object* v_res_161_; 
v_s_boxed_160_ = lean_unbox(v_s_158_);
v_res_161_ = l_Float_Model_UnpackedFloat_Sign_apply(v_s_boxed_160_, v_n_159_);
lean_dec(v_n_159_);
return v_res_161_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = l_BitVec_ofNat(v___x_162_, v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = l_BitVec_ofNat(v___x_165_, v___x_164_);
return v___x_166_;
}
}
lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec(uint8_t v_x_167_){
_start:
{
if (v_x_167_ == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0);
return v___x_168_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
return v___x_169_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_toBitVec_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_167_ = stack[0].m_num;
lean_object* v_res_170_;
v_res_170_ = l_Float_Model_UnpackedFloat_Sign_toBitVec(v_x_167_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec___boxed(lean_object* v_x_171_){
_start:
{
uint8_t v_x_45__boxed_172_; lean_object* v_res_173_; 
v_x_45__boxed_172_ = lean_unbox(v_x_171_);
v_res_173_ = l_Float_Model_UnpackedFloat_Sign_toBitVec(v_x_45__boxed_172_);
return v_res_173_;
}
}
uint8_t l_Float_Model_UnpackedFloat_Sign_ofBitVec(lean_object* v_b_174_){
_start:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
v___x_176_ = lean_nat_dec_eq(v_b_174_, v___x_175_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = 0;
return v___x_177_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 1;
return v___x_178_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_Sign_ofBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_174_ = stack[0].m_obj;
uint8_t v_res_179_;
v_res_179_ = l_Float_Model_UnpackedFloat_Sign_ofBitVec(v_b_174_);
stack->m_num = v_res_179_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofBitVec___boxed(lean_object* v_b_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Float_Model_UnpackedFloat_Sign_ofBitVec(v_b_180_);
lean_dec(v_b_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
