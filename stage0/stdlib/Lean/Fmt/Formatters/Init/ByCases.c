// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.ByCases
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.ByCases import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtByCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticBy_cases_:_"};
static const lean_object* l_Lean_Fmt_fmtByCases___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtByCases___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtByCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtByCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 65, 31, 128, 134, 243, 21, 139)}};
static const lean_object* l_Lean_Fmt_fmtByCases___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtByCases___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtByCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtByCases___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtByCases___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtByCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtByCases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtByCases___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtByCases___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByCases___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtByCases"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(253, 131, 129, 144, 248, 233, 213, 34)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByCases(lean_object* v_x_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___y_13_; lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_16_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; 
v___x_10_ = ((lean_object*)(l_Lean_Fmt_fmtByCases___closed__1));
lean_inc(v_x_7_);
v___x_11_ = l_Lean_Syntax_isOfKind(v_x_7_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_x_7_);
v___x_44_ = l_Lean_Fmt_Error_partialFormatter;
v___x_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v_a_9_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v_byCasesTk_47_; lean_object* v_h_x3f_49_; lean_object* v_colonTk_x3f_50_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v_byCasesTk_47_ = l_Lean_Syntax_getArg(v_x_7_, v___x_46_);
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = l_Lean_Syntax_getArg(v_x_7_, v___x_67_);
v___x_69_ = l_Lean_Syntax_isNone(v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_68_);
v___x_71_ = l_Lean_Syntax_matchesNull(v___x_68_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v___x_68_);
lean_dec(v_byCasesTk_47_);
lean_dec(v_x_7_);
v___x_72_ = l_Lean_Fmt_Error_partialFormatter;
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_a_9_);
return v___x_73_;
}
else
{
lean_object* v_h_x3f_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_h_x3f_74_ = l_Lean_Syntax_getArg(v___x_68_, v___x_46_);
v___x_75_ = ((lean_object*)(l_Lean_Fmt_fmtByCases___closed__3));
lean_inc(v_h_x3f_74_);
v___x_76_ = l_Lean_Syntax_isOfKind(v_h_x3f_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_h_x3f_74_);
lean_dec(v___x_68_);
lean_dec(v_byCasesTk_47_);
lean_dec(v_x_7_);
v___x_77_ = l_Lean_Fmt_Error_partialFormatter;
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v_a_9_);
return v___x_78_;
}
else
{
lean_object* v_colonTk_x3f_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_colonTk_x3f_79_ = l_Lean_Syntax_getArg(v___x_68_, v___x_67_);
lean_dec(v___x_68_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v_h_x3f_74_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v_colonTk_x3f_79_);
v_h_x3f_49_ = v___x_80_;
v_colonTk_x3f_50_ = v___x_81_;
v___y_51_ = v_a_8_;
v___y_52_ = v_a_9_;
goto v___jp_48_;
}
}
}
else
{
lean_object* v___x_82_; 
lean_dec(v___x_68_);
v___x_82_ = lean_box(0);
v_h_x3f_49_ = v___x_82_;
v_colonTk_x3f_50_ = v___x_82_;
v___y_51_ = v_a_8_;
v___y_52_ = v_a_9_;
goto v___jp_48_;
}
v___jp_48_:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Fmt_fmt(v_byCasesTk_47_, v___y_51_, v___y_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
v_a_55_ = lean_ctor_get(v___x_53_, 1);
lean_inc(v_a_55_);
lean_dec_ref_known(v___x_53_, 2);
v___x_56_ = lean_unsigned_to_nat(2u);
v___x_57_ = l_Lean_Syntax_getArg(v_x_7_, v___x_56_);
lean_dec(v_x_7_);
if (lean_obj_tag(v_h_x3f_49_) == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(0);
v___y_13_ = v___x_57_;
v___y_14_ = v_colonTk_x3f_50_;
v___y_15_ = v_a_55_;
v___y_16_ = v_a_54_;
v___y_17_ = v___x_56_;
v___y_18_ = v___y_51_;
v___y_19_ = v___x_58_;
goto v___jp_12_;
}
else
{
lean_object* v_val_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_val_59_ = lean_ctor_get(v_h_x3f_49_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v_h_x3f_49_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v_h_x3f_49_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_val_59_);
lean_dec(v_h_x3f_49_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_val_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
v___y_13_ = v___x_57_;
v___y_14_ = v_colonTk_x3f_50_;
v___y_15_ = v_a_55_;
v___y_16_ = v_a_54_;
v___y_17_ = v___x_56_;
v___y_18_ = v___y_51_;
v___y_19_ = v___x_64_;
goto v___jp_12_;
}
}
}
}
else
{
lean_dec(v_colonTk_x3f_50_);
lean_dec(v_h_x3f_49_);
lean_dec(v_x_7_);
return v___x_53_;
}
}
}
v___jp_12_:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Fmt_fmt_x3f(v___y_19_, v___y_18_, v___y_15_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
v_a_22_ = lean_ctor_get(v___x_20_, 1);
lean_inc(v_a_22_);
lean_dec_ref_known(v___x_20_, 2);
v___x_23_ = l_Lean_Fmt_fmt_x3f(v___y_14_, v___y_18_, v_a_22_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_26_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
v_a_25_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_23_, 2);
v___x_26_ = l_Lean_Fmt_fmt(v___y_13_, v___y_18_, v_a_25_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_43_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
v_a_28_ = lean_ctor_get(v___x_26_, 1);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_43_ == 0)
{
v___x_30_ = v___x_26_;
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_inc(v_a_27_);
lean_dec(v___x_26_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_32_ = 0;
v___x_33_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_33_, 0, v___x_11_);
lean_ctor_set_uint8(v___x_33_, 1, v___x_32_);
lean_ctor_set_uint8(v___x_33_, 2, v___x_11_);
lean_ctor_set_uint8(v___x_33_, 3, v___x_11_);
v___x_34_ = l_Lean_Fmt_Layouts_typeAscription(v_a_21_, v_a_24_, v_a_27_, v___x_33_);
lean_dec_ref_known(v___x_33_, 0);
v___x_35_ = lean_mk_empty_array_with_capacity(v___y_17_);
v___x_36_ = lean_array_push(v___x_35_, v___y_16_);
v___x_37_ = lean_array_push(v___x_36_, v___x_34_);
v___x_38_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_38_, 0, v___x_11_);
lean_ctor_set_uint8(v___x_38_, 1, v___x_32_);
lean_ctor_set_uint8(v___x_38_, 2, v___x_32_);
lean_ctor_set_uint8(v___x_38_, 3, v___x_32_);
v___x_39_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_37_, v___x_38_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_39_);
v___x_41_ = v___x_30_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_a_28_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
else
{
lean_dec(v_a_24_);
lean_dec(v_a_21_);
lean_dec_ref(v___y_16_);
return v___x_26_;
}
}
else
{
lean_dec(v_a_21_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_13_);
return v___x_23_;
}
}
else
{
lean_dec_ref(v___y_16_);
lean_dec(v___y_14_);
lean_dec(v___y_13_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByCases___boxed(lean_object* v_x_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Fmt_fmtByCases(v_x_83_, v_a_84_, v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1(){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = l_Lean_Fmt_fmtAttribute;
v___x_96_ = ((lean_object*)(l_Lean_Fmt_fmtByCases___closed__1));
v___x_97_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___closed__3));
v___x_98_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtByCases___boxed), 3, 0);
v___x_99_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_95_, v___x_96_, v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1___boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1();
return v_res_101_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_ByCases(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_ByCases_0__Lean_Fmt_fmtByCases___regBuiltin_Lean_Fmt_fmtByCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_ByCases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_ByCases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_ByCases(builtin);
}
#ifdef __cplusplus
}
#endif
