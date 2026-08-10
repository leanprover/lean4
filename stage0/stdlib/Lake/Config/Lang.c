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
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_ConfigLang_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lake_ConfigLang_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg(lean_object* v_lean_22_){
_start:
{
lean_inc(v_lean_22_);
return v_lean_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___redArg___boxed(lean_object* v_lean_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_ConfigLang_lean_elim___redArg(v_lean_23_);
lean_dec(v_lean_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_lean_28_){
_start:
{
lean_inc(v_lean_28_);
return v_lean_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_lean_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_lean_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lake_ConfigLang_lean_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_lean_32_);
lean_dec(v_lean_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg(lean_object* v_toml_35_){
_start:
{
lean_inc(v_toml_35_);
return v_toml_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___redArg___boxed(lean_object* v_toml_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_ConfigLang_toml_elim___redArg(v_toml_36_);
lean_dec(v_toml_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_toml_41_){
_start:
{
lean_inc(v_toml_41_);
return v_toml_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toml_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_toml_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lake_ConfigLang_toml_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_toml_45_);
lean_dec(v_toml_45_);
return v_res_47_;
}
}
static lean_object* _init_l_Lake_instReprConfigLang_repr___closed__4(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(2u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lake_instReprConfigLang_repr___closed__5(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang_repr(uint8_t v_x_58_, lean_object* v_prec_59_){
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
v___x_76_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__4, &l_Lake_instReprConfigLang_repr___closed__4_once, _init_l_Lake_instReprConfigLang_repr___closed__4);
v___y_61_ = v___x_76_;
goto v___jp_60_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__5, &l_Lake_instReprConfigLang_repr___closed__5_once, _init_l_Lake_instReprConfigLang_repr___closed__5);
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
v___x_80_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__4, &l_Lake_instReprConfigLang_repr___closed__4_once, _init_l_Lake_instReprConfigLang_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lake_instReprConfigLang_repr___closed__5, &l_Lake_instReprConfigLang_repr___closed__5_once, _init_l_Lake_instReprConfigLang_repr___closed__5);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_62_ = ((lean_object*)(l_Lake_instReprConfigLang_repr___closed__1));
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
v___x_69_ = ((lean_object*)(l_Lake_instReprConfigLang_repr___closed__3));
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
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang_repr___boxed(lean_object* v_x_82_, lean_object* v_prec_83_){
_start:
{
uint8_t v_x_121__boxed_84_; lean_object* v_res_85_; 
v_x_121__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Lake_instReprConfigLang_repr(v_x_121__boxed_84_, v_prec_83_);
lean_dec(v_prec_83_);
return v_res_85_;
}
}
LEAN_EXPORT uint8_t l_Lake_ConfigLang_ofNat(lean_object* v_n_88_){
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
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofNat___boxed(lean_object* v_n_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Lake_ConfigLang_ofNat(v_n_93_);
lean_dec(v_n_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqConfigLang(uint8_t v_x_96_, uint8_t v_y_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = l_Lake_ConfigLang_ctorIdx(v_x_96_);
v___x_99_ = l_Lake_ConfigLang_ctorIdx(v_y_97_);
v___x_100_ = lean_nat_dec_eq(v___x_98_, v___x_99_);
lean_dec(v___x_99_);
lean_dec(v___x_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqConfigLang___boxed(lean_object* v_x_101_, lean_object* v_y_102_){
_start:
{
uint8_t v_x_13__boxed_103_; uint8_t v_y_14__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_x_13__boxed_103_ = lean_unbox(v_x_101_);
v_y_14__boxed_104_ = lean_unbox(v_y_102_);
v_res_105_ = l_Lake_instDecidableEqConfigLang(v_x_13__boxed_103_, v_y_14__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
static uint8_t _init_l_Lake_ConfigLang_default(void){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
}
static uint8_t _init_l_Lake_instInhabitedConfigLang(void){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = 1;
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f(lean_object* v_x_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__0));
v___x_119_ = lean_string_dec_eq(v_x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__1));
v___x_121_ = lean_string_dec_eq(v_x_117_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__2));
return v___x_123_;
}
}
else
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__3));
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f___boxed(lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lake_ConfigLang_ofString_x3f(v_x_125_);
lean_dec_ref(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension(uint8_t v_x_127_){
_start:
{
if (v_x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__0));
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Lake_ConfigLang_ofString_x3f___closed__1));
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension___boxed(lean_object* v_x_130_){
_start:
{
uint8_t v_x_20__boxed_131_; lean_object* v_res_132_; 
v_x_20__boxed_131_ = lean_unbox(v_x_130_);
v_res_132_ = l_Lake_ConfigLang_fileExtension(v_x_20__boxed_131_);
return v_res_132_;
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
