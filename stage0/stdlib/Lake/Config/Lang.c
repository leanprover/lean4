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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lake_ConfigLang_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lake_ConfigLang_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Lake_ConfigLang_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lake_ConfigLang_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Lake_ConfigLang_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg(lean_object* v_lean_27_){
_start:
{
lean_inc(v_lean_27_);
return v_lean_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg___boxed(lean_object* v_lean_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_ConfigLang_lean_elim___redArg(v_lean_28_);
lean_dec(v_lean_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_lean_33_){
_start:
{
lean_inc(v_lean_33_);
return v_lean_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_lean_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Lake_ConfigLang_lean_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_lean_37_);
lean_dec(v_lean_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg(lean_object* v_toml_40_){
_start:
{
lean_inc(v_toml_40_);
return v_toml_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg___boxed(lean_object* v_toml_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lake_ConfigLang_toml_elim___redArg(v_toml_41_);
lean_dec(v_toml_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_toml_46_){
_start:
{
lean_inc(v_toml_46_);
return v_toml_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_toml_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Lake_ConfigLang_toml_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_toml_50_);
lean_dec(v_toml_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Lake_instReprConfigLang_repr___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lake_instReprConfigLang_repr___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang_repr(uint8_t v_x_63_, lean_object* v_prec_64_){
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
v___x_81_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__4, &l_Lake_instReprConfigLang_repr___closed__4_once, _init_l_Lake_instReprConfigLang_repr___closed__4);
v___y_66_ = v___x_81_;
goto v___jp_65_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__5, &l_Lake_instReprConfigLang_repr___closed__5_once, _init_l_Lake_instReprConfigLang_repr___closed__5);
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
v___x_85_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__4, &l_Lake_instReprConfigLang_repr___closed__4_once, _init_l_Lake_instReprConfigLang_repr___closed__4);
v___y_73_ = v___x_85_;
goto v___jp_72_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__5, &l_Lake_instReprConfigLang_repr___closed__5_once, _init_l_Lake_instReprConfigLang_repr___closed__5);
v___y_73_ = v___x_86_;
goto v___jp_72_;
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = ((lean_object*)(l_Lake_instReprConfigLang_repr___closed__1));
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
v___x_74_ = ((lean_object*)(l_Lake_instReprConfigLang_repr___closed__3));
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
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_121__boxed_89_; lean_object* v_res_90_; 
v_x_121__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Lake_instReprConfigLang_repr(v_x_121__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Lake_ConfigLang_ofNat(lean_object* v_n_93_){
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
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofNat___boxed(lean_object* v_n_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Lake_ConfigLang_ofNat(v_n_98_);
lean_dec(v_n_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqConfigLang(uint8_t v_x_101_, uint8_t v_y_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = l_Lake_ConfigLang_ctorIdx(v_x_101_);
v___x_104_ = l_Lake_ConfigLang_ctorIdx(v_y_102_);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
lean_dec(v___x_104_);
lean_dec(v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqConfigLang___boxed(lean_object* v_x_106_, lean_object* v_y_107_){
_start:
{
uint8_t v_x_13__boxed_108_; uint8_t v_y_14__boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_x_13__boxed_108_ = lean_unbox(v_x_106_);
v_y_14__boxed_109_ = lean_unbox(v_y_107_);
v_res_110_ = l_Lake_instDecidableEqConfigLang(v_x_13__boxed_108_, v_y_14__boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
static uint8_t _init_l_Lake_ConfigLang_default(void){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = 1;
return v___x_112_;
}
}
static uint8_t _init_l_Lake_instInhabitedConfigLang(void){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = 1;
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f(lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__0));
v___x_124_ = lean_string_dec_eq(v_x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__1));
v___x_126_ = lean_string_dec_eq(v_x_122_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__2));
return v___x_128_;
}
}
else
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__3));
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f___boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lake_ConfigLang_ofString_x3f(v_x_130_);
lean_dec_ref(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension(uint8_t v_x_132_){
_start:
{
if (v_x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__0));
return v___x_133_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__1));
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension___boxed(lean_object* v_x_135_){
_start:
{
uint8_t v_x_20__boxed_136_; lean_object* v_res_137_; 
v_x_20__boxed_136_ = lean_unbox(v_x_135_);
v_res_137_ = l_Lake_ConfigLang_fileExtension(v_x_20__boxed_136_);
return v_res_137_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
