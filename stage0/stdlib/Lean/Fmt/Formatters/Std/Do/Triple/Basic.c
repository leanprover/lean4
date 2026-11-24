// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Do.Triple.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Do.Triple.Basic import Init.Data
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_tuple(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_hoareTriple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Fmt_hoareTriple___closed__0 = (const lean_object*)&l_Lean_Fmt_hoareTriple___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_hoareTriple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_hoareTriple___closed__1 = (const lean_object*)&l_Lean_Fmt_hoareTriple___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_hoareTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_hoareTriple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTriple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtTriple___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTriple___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTriple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Fmt_fmtTriple___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTriple___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTriple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "triple"};
static const lean_object* l_Lean_Fmt_fmtTriple___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTriple___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtTriple___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTriple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtTriple___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTriple___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTriple___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtTriple___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTriple___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTriple___closed__2_value),LEAN_SCALAR_PTR_LITERAL(98, 3, 229, 14, 94, 184, 116, 193)}};
static const lean_object* l_Lean_Fmt_fmtTriple___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTriple___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTriple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTriple___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtTriple"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 226, 46, 190, 3, 96, 25, 164)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_hoareTriple(lean_object* v_preLbTk_5_, lean_object* v_pre_6_, lean_object* v_preRbTk_7_, lean_object* v_namedArg_8_, lean_object* v_prog_9_, lean_object* v_postLbTk_10_, lean_object* v_post_11_, lean_object* v_postRbTk_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_pre_17_; lean_object* v_post_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_hoareTriple___closed__0));
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_mk_empty_array_with_capacity(v___x_14_);
v___x_16_ = lean_array_push(v___x_15_, v_pre_6_);
v_pre_17_ = l_Lean_Fmt_Layouts_tuple(v___x_13_, v_preLbTk_5_, v___x_16_, v_preRbTk_7_);
lean_dec_ref(v___x_16_);
v_post_18_ = l_Lean_Fmt_Layouts_tuple(v___x_13_, v_postLbTk_10_, v_post_11_, v_postRbTk_12_);
v___x_19_ = lean_unsigned_to_nat(2u);
v___x_20_ = lean_mk_empty_array_with_capacity(v___x_19_);
v___x_21_ = lean_array_push(v___x_20_, v_pre_17_);
v___x_22_ = lean_array_push(v___x_21_, v_namedArg_8_);
v___x_23_ = 1;
v___x_24_ = ((lean_object*)(l_Lean_Fmt_hoareTriple___closed__1));
v___x_25_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_22_, v___x_24_);
v___x_26_ = lean_unsigned_to_nat(3u);
v___x_27_ = lean_mk_empty_array_with_capacity(v___x_26_);
v___x_28_ = lean_array_push(v___x_27_, v___x_25_);
v___x_29_ = lean_array_push(v___x_28_, v_prog_9_);
v___x_30_ = lean_array_push(v___x_29_, v_post_18_);
v___x_31_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_30_, v___x_23_);
lean_dec_ref(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_hoareTriple___boxed(lean_object* v_preLbTk_32_, lean_object* v_pre_33_, lean_object* v_preRbTk_34_, lean_object* v_namedArg_35_, lean_object* v_prog_36_, lean_object* v_postLbTk_37_, lean_object* v_post_38_, lean_object* v_postRbTk_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Fmt_hoareTriple(v_preLbTk_32_, v_pre_33_, v_preRbTk_34_, v_namedArg_35_, v_prog_36_, v_postLbTk_37_, v_post_38_, v_postRbTk_39_);
lean_dec_ref(v_post_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTriple(lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Fmt_fmtTriple___closed__3));
lean_inc(v_x_48_);
v___x_52_ = l_Lean_Syntax_isOfKind(v_x_48_, v___x_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_x_48_);
v___x_53_ = l_Lean_Fmt_Error_partialFormatter;
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_a_50_);
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v_preLbTk_56_; lean_object* v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v_preLbTk_56_ = l_Lean_Syntax_getArg(v_x_48_, v___x_55_);
v___x_57_ = l_Lean_Fmt_fmt(v_preLbTk_56_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v_a_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
v_a_59_ = lean_ctor_get(v___x_57_, 1);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_57_, 2);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = l_Lean_Syntax_getArg(v_x_48_, v___x_60_);
v___x_62_ = l_Lean_Fmt_fmt(v___x_61_, v_a_49_, v_a_59_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v_preRbTk_66_; lean_object* v___x_67_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
v_a_64_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_62_, 2);
v___x_65_ = lean_unsigned_to_nat(2u);
v_preRbTk_66_ = l_Lean_Syntax_getArg(v_x_48_, v___x_65_);
v___x_67_ = l_Lean_Fmt_fmt(v_preRbTk_66_, v_a_49_, v_a_64_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_67_, 2);
v___x_70_ = lean_unsigned_to_nat(3u);
v___x_71_ = l_Lean_Syntax_getArg(v_x_48_, v___x_70_);
v___x_72_ = l_Lean_Fmt_fmt(v___x_71_, v_a_49_, v_a_69_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_75_; lean_object* v_postLbTk_76_; lean_object* v___x_77_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
v_a_74_ = lean_ctor_get(v___x_72_, 1);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_72_, 2);
v___x_75_ = lean_unsigned_to_nat(4u);
v_postLbTk_76_ = l_Lean_Syntax_getArg(v_x_48_, v___x_75_);
v___x_77_ = l_Lean_Fmt_fmt(v_postLbTk_76_, v_a_49_, v_a_74_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
v_a_79_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_77_, 2);
v___x_80_ = lean_unsigned_to_nat(5u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_48_, v___x_80_);
v___x_82_ = l_Lean_Fmt_fmt(v___x_81_, v_a_49_, v_a_79_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v_a_84_; lean_object* v___x_85_; lean_object* v_postRbTk_86_; lean_object* v___x_87_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
v_a_84_ = lean_ctor_get(v___x_82_, 1);
lean_inc(v_a_84_);
lean_dec_ref_known(v___x_82_, 2);
v___x_85_ = lean_unsigned_to_nat(6u);
v_postRbTk_86_ = l_Lean_Syntax_getArg(v_x_48_, v___x_85_);
lean_dec(v_x_48_);
v___x_87_ = l_Lean_Fmt_fmt(v_postRbTk_86_, v_a_49_, v_a_84_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_100_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_a_89_ = lean_ctor_get(v___x_87_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_100_ == 0)
{
v___x_91_ = v___x_87_;
v_isShared_92_ = v_isSharedCheck_100_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_100_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_93_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_60_);
v___x_95_ = lean_array_push(v___x_94_, v_a_83_);
v___x_96_ = l_Lean_Fmt_hoareTriple(v_a_58_, v_a_63_, v_a_68_, v___x_93_, v_a_73_, v_a_78_, v___x_95_, v_a_88_);
lean_dec_ref(v___x_95_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_96_);
v___x_98_ = v___x_91_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_a_89_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_dec(v_a_83_);
lean_dec(v_a_78_);
lean_dec(v_a_73_);
lean_dec(v_a_68_);
lean_dec(v_a_63_);
lean_dec(v_a_58_);
return v___x_87_;
}
}
else
{
lean_dec(v_a_78_);
lean_dec(v_a_73_);
lean_dec(v_a_68_);
lean_dec(v_a_63_);
lean_dec(v_a_58_);
lean_dec(v_x_48_);
return v___x_82_;
}
}
else
{
lean_dec(v_a_73_);
lean_dec(v_a_68_);
lean_dec(v_a_63_);
lean_dec(v_a_58_);
lean_dec(v_x_48_);
return v___x_77_;
}
}
else
{
lean_dec(v_a_68_);
lean_dec(v_a_63_);
lean_dec(v_a_58_);
lean_dec(v_x_48_);
return v___x_72_;
}
}
else
{
lean_dec(v_a_63_);
lean_dec(v_a_58_);
lean_dec(v_x_48_);
return v___x_67_;
}
}
else
{
lean_dec(v_a_58_);
lean_dec(v_x_48_);
return v___x_62_;
}
}
else
{
lean_dec(v_x_48_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTriple___boxed(lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Fmt_fmtTriple(v_x_101_, v_a_102_, v_a_103_);
lean_dec_ref(v_a_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1(){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_113_ = l_Lean_Fmt_fmtAttribute;
v___x_114_ = ((lean_object*)(l_Lean_Fmt_fmtTriple___closed__3));
v___x_115_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___closed__3));
v___x_116_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTriple___boxed), 3, 0);
v___x_117_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_113_, v___x_114_, v___x_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1___boxed(lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1();
return v_res_119_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Do_Triple_Basic_0__Lean_Fmt_fmtTriple___regBuiltin_Lean_Fmt_fmtTriple__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Do_Triple_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_Triple_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
