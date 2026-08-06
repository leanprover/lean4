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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Float_Model_UnpackedFloat_Sign_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Float_Model_UnpackedFloat_Sign_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg(lean_object* v_negative_22_){
_start:
{
lean_inc(v_negative_22_);
return v_negative_22_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg___boxed(lean_object* v_negative_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Float_Model_UnpackedFloat_Sign_negative_elim___redArg(v_negative_23_);
lean_dec(v_negative_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_negative_28_){
_start:
{
lean_inc(v_negative_28_);
return v_negative_28_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_negative_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_negative_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Float_Model_UnpackedFloat_Sign_negative_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_negative_32_);
lean_dec(v_negative_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg(lean_object* v_positive_35_){
_start:
{
lean_inc(v_positive_35_);
return v_positive_35_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg___boxed(lean_object* v_positive_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Float_Model_UnpackedFloat_Sign_positive_elim___redArg(v_positive_36_);
lean_dec(v_positive_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_positive_41_){
_start:
{
lean_inc(v_positive_41_);
return v_positive_41_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_positive_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_positive_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Float_Model_UnpackedFloat_Sign_positive_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_positive_45_);
lean_dec(v_positive_45_);
return v_res_47_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(2u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr(uint8_t v_x_58_, lean_object* v_prec_59_){
_start:
{
lean_object* v___y_61_; lean_object* v___y_68_; 
if (v_x_58_ == 0)
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1024u);
v___x_75_ = lean_nat_dec_le(v___x_74_, v_prec_59_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4);
v___y_61_ = v___x_76_;
goto v___jp_60_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5);
v___y_61_ = v___x_77_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_59_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5, &l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5_once, _init_l_Float_Model_UnpackedFloat_instReprSign_repr___closed__5);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_62_ = ((lean_object*)(l_Float_Model_UnpackedFloat_instReprSign_repr___closed__1));
lean_inc(v___y_61_);
v___x_63_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_63_, 0, v___y_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = 0;
v___x_65_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*1, v___x_64_);
v___x_66_ = l_Repr_addAppParen(v___x_65_, v_prec_59_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_69_ = ((lean_object*)(l_Float_Model_UnpackedFloat_instReprSign_repr___closed__3));
lean_inc(v___y_68_);
v___x_70_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_70_, 0, v___y_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = 0;
v___x_72_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*1, v___x_71_);
v___x_73_ = l_Repr_addAppParen(v___x_72_, v_prec_59_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr___boxed(lean_object* v_x_82_, lean_object* v_prec_83_){
_start:
{
uint8_t v_x_121__boxed_84_; lean_object* v_res_85_; 
v_x_121__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_x_121__boxed_84_, v_prec_83_);
lean_dec(v_prec_83_);
return v_res_85_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_ofNat(lean_object* v_n_88_){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_nat_dec_le(v_n_88_, v___x_89_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofNat___boxed(lean_object* v_n_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Float_Model_UnpackedFloat_Sign_ofNat(v_n_93_);
lean_dec(v_n_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_instDecidableEqSign(uint8_t v_x_96_, uint8_t v_y_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_x_96_);
v___x_99_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_y_97_);
v___x_100_ = lean_nat_dec_eq(v___x_98_, v___x_99_);
lean_dec(v___x_99_);
lean_dec(v___x_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_instDecidableEqSign___boxed(lean_object* v_x_101_, lean_object* v_y_102_){
_start:
{
uint8_t v_x_13__boxed_103_; uint8_t v_y_14__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_x_13__boxed_103_ = lean_unbox(v_x_101_);
v_y_14__boxed_104_ = lean_unbox(v_y_102_);
v_res_105_ = l_Float_Model_UnpackedFloat_instDecidableEqSign(v_x_13__boxed_103_, v_y_14__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(uint8_t v_x_107_, uint8_t v_x_108_){
_start:
{
if (v_x_107_ == 0)
{
if (v_x_108_ == 0)
{
uint8_t v___x_109_; 
v___x_109_ = 1;
return v___x_109_;
}
else
{
return v_x_107_;
}
}
else
{
return v_x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instMul___lam__0___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_x_35__boxed_112_; uint8_t v_x_36__boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_35__boxed_112_ = lean_unbox(v_x_110_);
v_x_36__boxed_113_ = lean_unbox(v_x_111_);
v_res_114_ = l_Float_Model_UnpackedFloat_Sign_instMul___lam__0(v_x_35__boxed_112_, v_x_36__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(uint8_t v_x_119_){
_start:
{
if (v_x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 1;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0___boxed(lean_object* v_x_122_){
_start:
{
uint8_t v_x_22__boxed_123_; uint8_t v_res_124_; lean_object* v_r_125_; 
v_x_22__boxed_123_ = lean_unbox(v_x_122_);
v_res_124_ = l_Float_Model_UnpackedFloat_Sign_instNeg___lam__0(v_x_22__boxed_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(uint8_t v_x_128_, uint8_t v_x_129_){
_start:
{
if (v_x_128_ == 0)
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
else
{
if (v_x_129_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = 2;
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 1;
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0___boxed(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_x_40__boxed_136_; uint8_t v_x_41__boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_x_40__boxed_136_ = lean_unbox(v_x_134_);
v_x_41__boxed_137_ = lean_unbox(v_x_135_);
v_res_138_ = l_Float_Model_UnpackedFloat_Sign_instOrd___lam__0(v_x_40__boxed_136_, v_x_41__boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t v_s_142_, lean_object* v_n_143_){
_start:
{
if (v_s_142_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_int_neg(v_n_143_);
return v___x_144_;
}
else
{
lean_inc(v_n_143_);
return v_n_143_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_apply___boxed(lean_object* v_s_145_, lean_object* v_n_146_){
_start:
{
uint8_t v_s_boxed_147_; lean_object* v_res_148_; 
v_s_boxed_147_ = lean_unbox(v_s_145_);
v_res_148_ = l_Float_Model_UnpackedFloat_Sign_apply(v_s_boxed_147_, v_n_146_);
lean_dec(v_n_146_);
return v_res_148_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = l_BitVec_ofNat(v___x_149_, v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = l_BitVec_ofNat(v___x_152_, v___x_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec(uint8_t v_x_154_){
_start:
{
if (v_x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__0);
return v___x_155_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec___boxed(lean_object* v_x_157_){
_start:
{
uint8_t v_x_45__boxed_158_; lean_object* v_res_159_; 
v_x_45__boxed_158_ = lean_unbox(v_x_157_);
v_res_159_ = l_Float_Model_UnpackedFloat_Sign_toBitVec(v_x_45__boxed_158_);
return v_res_159_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_Sign_ofBitVec(lean_object* v_b_160_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_obj_once(&l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1, &l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1_once, _init_l_Float_Model_UnpackedFloat_Sign_toBitVec___closed__1);
v___x_162_ = lean_nat_dec_eq(v_b_160_, v___x_161_);
if (v___x_162_ == 0)
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
else
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Sign_ofBitVec___boxed(lean_object* v_b_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Float_Model_UnpackedFloat_Sign_ofBitVec(v_b_165_);
lean_dec(v_b_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
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
