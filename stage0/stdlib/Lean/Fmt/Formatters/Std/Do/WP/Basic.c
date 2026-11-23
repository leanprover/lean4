// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Do.WP.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Do.WP.Basic import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtWP___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWP___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtWP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Fmt_fmtWP___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWP___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtWP___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 11, .m_data = "termWp⟦_:_⟧"};
static const lean_object* l_Lean_Fmt_fmtWP___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtWP___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtWP___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWP___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtWP___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWP___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWP___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtWP___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWP___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtWP___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 96, 4, 176, 128, 111, 85, 188)}};
static const lean_object* l_Lean_Fmt_fmtWP___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtWP___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWP___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fmtWP"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(104, 128, 57, 195, 60, 82, 52, 16)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWP(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_16_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_20_; 
v___x_11_ = ((lean_object*)(l_Lean_Fmt_fmtWP___closed__3));
lean_inc(v_x_8_);
v___x_12_ = l_Lean_Syntax_isOfKind(v_x_8_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_x_8_);
v___x_38_ = l_Lean_Fmt_Error_partialFormatter;
v___x_39_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v_a_10_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v_lbTk_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_typeAscriptionTk_x3f_45_; lean_object* v_type_x3f_46_; lean_object* v___y_47_; lean_object* v___y_48_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_40_ = lean_unsigned_to_nat(0u);
v_lbTk_41_ = l_Lean_Syntax_getArg(v_x_8_, v___x_40_);
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = l_Lean_Syntax_getArg(v_x_8_, v___x_42_);
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = l_Lean_Syntax_getArg(v_x_8_, v___x_69_);
v___x_71_ = l_Lean_Syntax_isNone(v___x_70_);
if (v___x_71_ == 0)
{
uint8_t v___x_72_; 
lean_inc(v___x_70_);
v___x_72_ = l_Lean_Syntax_matchesNull(v___x_70_, v___x_69_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v___x_70_);
lean_dec(v___x_43_);
lean_dec(v_lbTk_41_);
lean_dec(v_x_8_);
v___x_73_ = l_Lean_Fmt_Error_partialFormatter;
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_a_10_);
return v___x_74_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_75_; lean_object* v_type_x3f_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_typeAscriptionTk_x3f_75_ = l_Lean_Syntax_getArg(v___x_70_, v___x_40_);
v_type_x3f_76_ = l_Lean_Syntax_getArg(v___x_70_, v___x_42_);
lean_dec(v___x_70_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v_typeAscriptionTk_x3f_75_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_type_x3f_76_);
v_typeAscriptionTk_x3f_45_ = v___x_77_;
v_type_x3f_46_ = v___x_78_;
v___y_47_ = v_a_9_;
v___y_48_ = v_a_10_;
goto v___jp_44_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec(v___x_70_);
v___x_79_ = lean_box(0);
v_typeAscriptionTk_x3f_45_ = v___x_79_;
v_type_x3f_46_ = v___x_79_;
v___y_47_ = v_a_9_;
v___y_48_ = v_a_10_;
goto v___jp_44_;
}
v___jp_44_:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Fmt_fmt(v_lbTk_41_, v___y_47_, v___y_48_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v___x_52_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
v_a_51_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_49_, 2);
v___x_52_ = l_Lean_Fmt_fmt(v___x_43_, v___y_47_, v_a_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_55_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
v_a_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_52_, 2);
v___x_55_ = l_Lean_Fmt_fmt_x3f(v_typeAscriptionTk_x3f_45_, v___y_47_, v_a_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v_a_57_; lean_object* v___x_58_; lean_object* v_rbTk_59_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_56_);
v_a_57_ = lean_ctor_get(v___x_55_, 1);
lean_inc(v_a_57_);
lean_dec_ref_known(v___x_55_, 2);
v___x_58_ = lean_unsigned_to_nat(3u);
v_rbTk_59_ = l_Lean_Syntax_getArg(v_x_8_, v___x_58_);
lean_dec(v_x_8_);
if (lean_obj_tag(v_type_x3f_46_) == 0)
{
lean_object* v___x_60_; 
v___x_60_ = lean_box(0);
v___y_14_ = v_a_56_;
v___y_15_ = v_a_53_;
v___y_16_ = v_a_50_;
v___y_17_ = v_rbTk_59_;
v___y_18_ = v_a_57_;
v___y_19_ = v___y_47_;
v___y_20_ = v___x_60_;
goto v___jp_13_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v_val_61_ = lean_ctor_get(v_type_x3f_46_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_type_x3f_46_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v_type_x3f_46_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_val_61_);
lean_dec(v_type_x3f_46_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_val_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
v___y_14_ = v_a_56_;
v___y_15_ = v_a_53_;
v___y_16_ = v_a_50_;
v___y_17_ = v_rbTk_59_;
v___y_18_ = v_a_57_;
v___y_19_ = v___y_47_;
v___y_20_ = v___x_66_;
goto v___jp_13_;
}
}
}
}
else
{
lean_dec(v_a_53_);
lean_dec(v_a_50_);
lean_dec(v_type_x3f_46_);
lean_dec(v_x_8_);
return v___x_55_;
}
}
else
{
lean_dec(v_a_50_);
lean_dec(v_type_x3f_46_);
lean_dec(v_typeAscriptionTk_x3f_45_);
lean_dec(v_x_8_);
return v___x_52_;
}
}
else
{
lean_dec(v_type_x3f_46_);
lean_dec(v_typeAscriptionTk_x3f_45_);
lean_dec(v___x_43_);
lean_dec(v_x_8_);
return v___x_49_;
}
}
}
v___jp_13_:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Fmt_fmt_x3f(v___y_20_, v___y_19_, v___y_18_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v_a_23_; lean_object* v___x_24_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_a_22_);
v_a_23_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_a_23_);
lean_dec_ref_known(v___x_21_, 2);
v___x_24_ = l_Lean_Fmt_fmt(v___y_17_, v___y_19_, v_a_23_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_37_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_a_26_ = lean_ctor_get(v___x_24_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_37_ == 0)
{
v___x_28_ = v___x_24_;
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_37_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_30_ = 0;
v___x_31_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_31_, 0, v___x_12_);
lean_ctor_set_uint8(v___x_31_, 1, v___x_30_);
lean_ctor_set_uint8(v___x_31_, 2, v___x_12_);
lean_ctor_set_uint8(v___x_31_, 3, v___x_12_);
v___x_32_ = l_Lean_Fmt_Layouts_typeAscription(v___y_15_, v___y_14_, v_a_22_, v___x_31_);
lean_dec_ref_known(v___x_31_, 0);
v___x_33_ = l_Lean_Fmt_Layouts_parens(v___y_16_, v___x_32_, v_a_25_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_33_);
v___x_35_ = v___x_28_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_a_26_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_dec(v_a_22_);
lean_dec_ref(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec_ref(v___y_14_);
return v___x_24_;
}
}
else
{
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec_ref(v___y_14_);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWP___boxed(lean_object* v_x_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Fmt_fmtWP(v_x_80_, v_a_81_, v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1(){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = l_Lean_Fmt_fmtAttribute;
v___x_93_ = ((lean_object*)(l_Lean_Fmt_fmtWP___closed__3));
v___x_94_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___closed__3));
v___x_95_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWP___boxed), 3, 0);
v___x_96_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_92_, v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1___boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1();
return v_res_98_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_WP_Basic(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Do_WP_Basic_0__Lean_Fmt_fmtWP___regBuiltin_Lean_Fmt_fmtWP__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Do_WP_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_WP_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Do_WP_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
