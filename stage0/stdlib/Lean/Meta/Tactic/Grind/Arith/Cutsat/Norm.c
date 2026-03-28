// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.IntInstTesters
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object* v_e_26_, lean_object* v_generation_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_e_40_; lean_object* v___y_41_; lean_object* v___y_42_; lean_object* v___y_43_; lean_object* v___y_44_; lean_object* v___y_45_; lean_object* v___y_46_; lean_object* v___y_47_; lean_object* v___y_48_; lean_object* v___y_49_; lean_object* v___y_50_; lean_object* v___x_118_; 
lean_inc_ref(v_e_26_);
v___x_118_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_26_, v_a_35_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v___x_118_);
v___x_120_ = l_Lean_Expr_cleanupAnnotations(v_a_119_);
v___x_121_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_121_ == 0)
{
lean_dec_ref(v___x_120_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v_arg_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_arg_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_arg_122_);
v___x_123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
v___x_124_ = l_Lean_Expr_isApp(v___x_123_);
if (v___x_124_ == 0)
{
lean_dec_ref(v___x_123_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v_arg_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_arg_125_);
v___x_126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_123_);
v___x_127_ = l_Lean_Expr_isApp(v___x_126_);
if (v___x_127_ == 0)
{
lean_dec_ref(v___x_126_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v_arg_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_arg_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc_ref(v_arg_128_);
v___x_129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_126_);
v___x_130_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2));
v___x_131_ = l_Lean_Expr_isConstOf(v___x_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5));
v___x_133_ = l_Lean_Expr_isConstOf(v___x_129_, v___x_132_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = l_Lean_Expr_isApp(v___x_129_);
if (v___x_134_ == 0)
{
lean_dec_ref(v___x_129_);
lean_dec_ref(v_arg_128_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_129_);
v___x_136_ = l_Lean_Expr_isApp(v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v___x_135_);
lean_dec_ref(v_arg_128_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_135_);
v___x_138_ = l_Lean_Expr_isApp(v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_128_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_137_);
v___x_140_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8));
v___x_141_ = l_Lean_Expr_isConstOf(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11));
v___x_143_ = l_Lean_Expr_isConstOf(v___x_139_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14));
v___x_145_ = l_Lean_Expr_isConstOf(v___x_139_, v___x_144_);
lean_dec_ref(v___x_139_);
if (v___x_145_ == 0)
{
lean_dec_ref(v_arg_128_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_128_, v_a_35_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; uint8_t v___x_148_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
lean_dec_ref(v___x_146_);
v___x_148_ = lean_unbox(v_a_147_);
lean_dec(v_a_147_);
if (v___x_148_ == 0)
{
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_125_, v___x_149_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v___x_150_);
v___x_152_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_122_, v___x_149_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_157_, 0, v_a_151_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_dec(v_a_151_);
return v___x_152_;
}
}
else
{
lean_dec_ref(v_arg_122_);
return v___x_150_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_162_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_146_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_146_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
else
{
lean_object* v___x_170_; 
lean_dec_ref(v___x_139_);
v___x_170_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_128_, v_a_35_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; uint8_t v___x_172_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = lean_unbox(v_a_171_);
lean_dec(v_a_171_);
if (v___x_172_ == 0)
{
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_125_, v___x_173_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref(v___x_174_);
v___x_176_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_122_, v___x_173_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_181_, 0, v_a_175_);
lean_ctor_set(v___x_181_, 1, v_a_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
lean_dec(v_a_175_);
return v___x_176_;
}
}
else
{
lean_dec_ref(v_arg_122_);
return v___x_174_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_186_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_170_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_170_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
else
{
lean_object* v___x_194_; 
lean_dec_ref(v___x_139_);
v___x_194_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_128_, v_a_35_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; uint8_t v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref(v___x_194_);
v___x_196_ = lean_unbox(v_a_195_);
lean_dec(v_a_195_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_197_; 
lean_inc_ref(v_arg_125_);
v___x_197_ = l_Lean_Meta_getIntValue_x3f(v_arg_125_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_197_);
if (lean_obj_tag(v_a_198_) == 0)
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_getIntValue_x3f(v_arg_122_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref(v___x_199_);
if (lean_obj_tag(v_a_200_) == 0)
{
lean_dec_ref(v_arg_125_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_val_201_ = lean_ctor_get(v_a_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref(v_a_200_);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_125_, v___x_202_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_208_, 0, v_a_204_);
lean_ctor_set(v___x_208_, 1, v_val_201_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_dec(v_val_201_);
return v___x_203_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_arg_125_);
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_213_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_199_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_199_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v_val_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref(v_arg_125_);
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_val_221_ = lean_ctor_get(v_a_198_, 0);
lean_inc(v_val_221_);
lean_dec_ref(v_a_198_);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_122_, v___x_222_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v_val_221_);
lean_ctor_set(v___x_228_, 1, v_a_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_dec(v_val_221_);
return v___x_223_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_233_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_197_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_197_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_241_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_194_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_194_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_249_; 
lean_dec_ref(v___x_129_);
lean_dec_ref(v_arg_128_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
lean_inc_ref(v_e_26_);
v___x_249_ = l_Lean_Meta_getIntValue_x3f(v_e_26_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_265_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_265_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
if (lean_obj_tag(v_a_250_) == 1)
{
lean_object* v_val_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_264_; 
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_val_254_ = lean_ctor_get(v_a_250_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_264_ == 0)
{
v___x_256_ = v_a_250_;
v_isShared_257_ = v_isSharedCheck_264_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_val_254_);
lean_dec(v_a_250_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_264_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 0);
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_val_254_);
v___x_259_ = v_reuseFailAlloc_263_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_261_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_259_);
v___x_261_ = v___x_252_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_del_object(v___x_252_);
lean_dec(v_a_250_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_266_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_249_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_249_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
else
{
lean_object* v___x_274_; 
lean_dec_ref(v___x_129_);
lean_dec_ref(v_arg_128_);
v___x_274_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_125_, v_a_35_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; uint8_t v___x_276_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref(v___x_274_);
v___x_276_ = lean_unbox(v_a_275_);
lean_dec(v_a_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_arg_122_);
v_e_40_ = v_e_26_;
v___y_41_ = v_a_28_;
v___y_42_ = v_a_29_;
v___y_43_ = v_a_30_;
v___y_44_ = v_a_31_;
v___y_45_ = v_a_32_;
v___y_46_ = v_a_33_;
v___y_47_ = v_a_34_;
v___y_48_ = v_a_35_;
v___y_49_ = v_a_36_;
v___y_50_ = v_a_37_;
goto v___jp_39_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_122_, v___x_277_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_283_, 0, v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
return v___x_278_;
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref(v_arg_122_);
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_288_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_274_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_274_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v_generation_27_);
lean_dec_ref(v_e_26_);
v_a_296_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_118_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_118_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
v___jp_39_:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_40_, v___y_46_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref(v___x_51_);
v___x_53_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_52_, v___y_41_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; uint8_t v___x_55_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref(v___x_53_);
v___x_55_ = lean_unbox(v_a_54_);
lean_dec(v_a_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_box(0);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
lean_inc(v___y_48_);
lean_inc_ref(v___y_47_);
lean_inc(v___y_46_);
lean_inc_ref(v___y_45_);
lean_inc(v___y_44_);
lean_inc_ref(v___y_43_);
lean_inc(v___y_42_);
lean_inc(v___y_41_);
lean_inc(v_a_52_);
v___x_57_ = lean_grind_internalize(v_a_52_, v_generation_27_, v___x_56_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v___x_58_; 
lean_dec_ref(v___x_57_);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
lean_inc(v___y_48_);
lean_inc_ref(v___y_47_);
lean_inc(v___y_46_);
lean_inc_ref(v___y_45_);
lean_inc(v___y_44_);
lean_inc_ref(v___y_43_);
lean_inc(v___y_42_);
lean_inc(v___y_41_);
v___x_58_ = lean_grind_cutsat_mk_var(v_a_52_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_67_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_67_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v_a_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_65_ = v___x_61_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
else
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
v_a_68_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_75_ == 0)
{
v___x_70_ = v___x_58_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_58_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_68_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec(v_a_52_);
v_a_76_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_57_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_57_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
else
{
lean_object* v___x_84_; 
lean_dec(v_generation_27_);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
lean_inc(v___y_48_);
lean_inc_ref(v___y_47_);
lean_inc(v___y_46_);
lean_inc_ref(v___y_45_);
lean_inc(v___y_44_);
lean_inc_ref(v___y_43_);
lean_inc(v___y_42_);
lean_inc(v___y_41_);
v___x_84_ = lean_grind_cutsat_mk_var(v_a_52_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_93_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_93_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_a_85_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_89_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
v_a_94_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_84_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_84_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_a_52_);
lean_dec(v_generation_27_);
v_a_102_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_53_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_53_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec(v_generation_27_);
v_a_110_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_51_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_51_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object* v_e_304_, lean_object* v_generation_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_e_304_, v_generation_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec(v_a_306_);
return v_res_317_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
}
#ifdef __cplusplus
}
#endif
