// Lean compiler output
// Module: Lake.Config.Lang
// Imports: public import Init.Data.ToString.Basic
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprConfigLang_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ConfigLang.lean"};
static const lean_object* l_Lake_instReprConfigLang_repr___closed__0 = (const lean_object*)&l_Lake_instReprConfigLang_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprConfigLang_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprConfigLang_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprConfigLang_repr___closed__1 = (const lean_object*)&l_Lake_instReprConfigLang_repr___closed__1_value;
static const lean_string_object l_Lake_instReprConfigLang_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ConfigLang.toml"};
static const lean_object* l_Lake_instReprConfigLang_repr___closed__2 = (const lean_object*)&l_Lake_instReprConfigLang_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprConfigLang_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprConfigLang_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprConfigLang_repr___closed__3 = (const lean_object*)&l_Lake_instReprConfigLang_repr___closed__3_value;
static lean_once_cell_t l_Lake_instReprConfigLang_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprConfigLang_repr___closed__4;
static lean_once_cell_t l_Lake_instReprConfigLang_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprConfigLang_repr___closed__5;
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprConfigLang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprConfigLang_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprConfigLang___closed__0 = (const lean_object*)&l_Lake_instReprConfigLang___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprConfigLang = (const lean_object*)&l_Lake_instReprConfigLang___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_ConfigLang_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqConfigLang(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqConfigLang___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_ConfigLang_default;
LEAN_EXPORT uint8_t l_Lake_instInhabitedConfigLang;
static const lean_string_object l_Lake_ConfigLang_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_ConfigLang_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_ConfigLang_ofString_x3f___closed__0_value;
static const lean_string_object l_Lake_ConfigLang_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l_Lake_ConfigLang_ofString_x3f___closed__1 = (const lean_object*)&l_Lake_ConfigLang_ofString_x3f___closed__1_value;
static const lean_ctor_object l_Lake_ConfigLang_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_ConfigLang_ofString_x3f___closed__2 = (const lean_object*)&l_Lake_ConfigLang_ofString_x3f___closed__2_value;
static const lean_ctor_object l_Lake_ConfigLang_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_ConfigLang_ofString_x3f___closed__3 = (const lean_object*)&l_Lake_ConfigLang_ofString_x3f___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension___boxed(lean_object*);
static const lean_closure_object l_Lake_instToStringConfigLang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ConfigLang_fileExtension___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToStringConfigLang___closed__0 = (const lean_object*)&l_Lake_instToStringConfigLang___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringConfigLang = (const lean_object*)&l_Lake_instToStringConfigLang___closed__0_value;
lean_object* l_Lake_ConfigLang_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lake_ConfigLang_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lake_ConfigLang_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_ConfigLang_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_ConfigLang_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lake_ConfigLang_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lake_ConfigLang_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lake_ConfigLang_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lake_ConfigLang_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg(lean_object* v_lean_24_){
_start:
{
lean_inc(v_lean_24_);
return v_lean_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg___boxed(lean_object* v_lean_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_ConfigLang_lean_elim___redArg(v_lean_25_);
lean_dec(v_lean_25_);
return v_res_26_;
}
}
lean_object* l_Lake_ConfigLang_lean_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_lean_30_){
_start:
{
lean_inc(v_lean_30_);
return v_lean_30_;
}
}
LEAN_EXPORT void l_Lake_ConfigLang_lean_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_lean_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_ConfigLang_lean_elim(lean_box(0), v_t_28_, lean_box(0), v_lean_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_lean_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lake_ConfigLang_lean_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_lean_35_);
lean_dec(v_lean_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg(lean_object* v_toml_38_){
_start:
{
lean_inc(v_toml_38_);
return v_toml_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg___boxed(lean_object* v_toml_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_ConfigLang_toml_elim___redArg(v_toml_39_);
lean_dec(v_toml_39_);
return v_res_40_;
}
}
lean_object* l_Lake_ConfigLang_toml_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_toml_44_){
_start:
{
lean_inc(v_toml_44_);
return v_toml_44_;
}
}
LEAN_EXPORT void l_Lake_ConfigLang_toml_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_toml_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lake_ConfigLang_toml_elim(lean_box(0), v_t_42_, lean_box(0), v_toml_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_toml_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lake_ConfigLang_toml_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_toml_49_);
lean_dec(v_toml_49_);
return v_res_51_;
}
}
static lean_object* _init_l_Lake_instReprConfigLang_repr___closed__4(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(2u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lake_instReprConfigLang_repr___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
lean_object* l_Lake_instReprConfigLang_repr(uint8_t v_x_62_, lean_object* v_prec_63_){
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
v___x_80_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__4, &l_Lake_instReprConfigLang_repr___closed__4_once, _init_l_Lake_instReprConfigLang_repr___closed__4);
v___y_65_ = v___x_80_;
goto v___jp_64_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__5, &l_Lake_instReprConfigLang_repr___closed__5_once, _init_l_Lake_instReprConfigLang_repr___closed__5);
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
v___x_84_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__4, &l_Lake_instReprConfigLang_repr___closed__4_once, _init_l_Lake_instReprConfigLang_repr___closed__4);
v___y_72_ = v___x_84_;
goto v___jp_71_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__5, &l_Lake_instReprConfigLang_repr___closed__5_once, _init_l_Lake_instReprConfigLang_repr___closed__5);
v___y_72_ = v___x_85_;
goto v___jp_71_;
}
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = ((lean_object*)(l_Lake_instReprConfigLang_repr___closed__1));
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
v___x_73_ = ((lean_object*)(l_Lake_instReprConfigLang_repr___closed__3));
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
LEAN_EXPORT void l_Lake_instReprConfigLang_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_62_ = stack[0].m_num;
lean_object* v_prec_63_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lake_instReprConfigLang_repr(v_x_62_, v_prec_63_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_117__boxed_89_; lean_object* v_res_90_; 
v_x_117__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Lake_instReprConfigLang_repr(v_x_117__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
uint8_t l_Lake_ConfigLang_ofNat(lean_object* v_n_93_){
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
LEAN_EXPORT void l_Lake_ConfigLang_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_93_ = stack[0].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_Lake_ConfigLang_ofNat(v_n_93_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofNat___boxed(lean_object* v_n_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Lake_ConfigLang_ofNat(v_n_99_);
lean_dec(v_n_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
uint8_t l_Lake_instDecidableEqConfigLang(uint8_t v_x_102_, uint8_t v_y_103_){
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
LEAN_EXPORT void l_Lake_instDecidableEqConfigLang_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_102_ = stack[0].m_num;
uint8_t v_y_103_ = stack[1].m_num;
uint8_t v_res_109_;
v_res_109_ = l_Lake_instDecidableEqConfigLang(v_x_102_, v_y_103_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqConfigLang___boxed(lean_object* v_x_110_, lean_object* v_y_111_){
_start:
{
uint8_t v_x_23__boxed_112_; uint8_t v_y_24__boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_23__boxed_112_ = lean_unbox(v_x_110_);
v_y_24__boxed_113_ = lean_unbox(v_y_111_);
v_res_114_ = l_Lake_instDecidableEqConfigLang(v_x_23__boxed_112_, v_y_24__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
static uint8_t _init_l_Lake_ConfigLang_default(void){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
}
static uint8_t _init_l_Lake_instInhabitedConfigLang(void){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = 1;
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f(lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__0));
v___x_128_ = lean_string_dec_eq(v_x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__1));
v___x_130_ = lean_string_dec_eq(v_x_126_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__2));
return v___x_132_;
}
}
else
{
lean_object* v___x_133_; 
v___x_133_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__3));
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f___boxed(lean_object* v_x_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lake_ConfigLang_ofString_x3f(v_x_134_);
lean_dec_ref(v_x_134_);
return v_res_135_;
}
}
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t v_x_136_){
_start:
{
if (v_x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__0));
return v___x_137_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__1));
return v___x_138_;
}
}
}
LEAN_EXPORT void l_Lake_ConfigLang_fileExtension_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_136_ = stack[0].m_num;
lean_object* v_res_139_;
v_res_139_ = l_Lake_ConfigLang_fileExtension(v_x_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension___boxed(lean_object* v_x_140_){
_start:
{
uint8_t v_x_20__boxed_141_; lean_object* v_res_142_; 
v_x_20__boxed_141_ = lean_unbox(v_x_140_);
v_res_142_ = l_Lake_ConfigLang_fileExtension(v_x_20__boxed_141_);
return v_res_142_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_ConfigLang_default = _init_l_Lake_ConfigLang_default();
l_Lake_instInhabitedConfigLang = _init_l_Lake_instInhabitedConfigLang();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Lang(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Lang(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Lang(builtin);
}
#ifdef __cplusplus
}
#endif
