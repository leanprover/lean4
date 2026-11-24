// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.WP.EStack
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.WP.EStack import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEStackType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtEStackType___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEStackType___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtEStackType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Fmt_fmtEStackType___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEStackType___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtEStackType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "termEStack⟨_⟩"};
static const lean_object* l_Lean_Fmt_fmtEStackType___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtEStackType___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtEStackType___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEStackType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtEStackType___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEStackType___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEStackType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Fmt_fmtEStackType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEStackType___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEStackType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 119, 75, 119, 76, 63, 185, 180)}};
static const lean_object* l_Lean_Fmt_fmtEStackType___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtEStackType___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackType___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtEStackType"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(229, 8, 255, 39, 67, 52, 182, 123)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEStackValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "termEstack⟨_⟩"};
static const lean_object* l_Lean_Fmt_fmtEStackValue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEStackValue___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtEStackValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEStackType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtEStackValue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEStackValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEStackType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Fmt_fmtEStackValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEStackValue___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEStackValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 219, 130, 170, 85, 204, 141, 199)}};
static const lean_object* l_Lean_Fmt_fmtEStackValue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEStackValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackValue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtEStackValue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 76, 36, 213, 93, 194, 220, 199)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackType(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Fmt_fmtEStackType___closed__3));
lean_inc(v_x_8_);
v___x_12_ = l_Lean_Syntax_isOfKind(v_x_8_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_x_8_);
v___x_13_ = l_Lean_Fmt_Error_partialFormatter;
v___x_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_a_10_);
return v___x_14_;
}
else
{
lean_object* v___x_15_; lean_object* v_lbTk_16_; lean_object* v___x_17_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v_lbTk_16_ = l_Lean_Syntax_getArg(v_x_8_, v___x_15_);
v___x_17_ = l_Lean_Fmt_fmt(v_lbTk_16_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_exceptConds_22_; lean_object* v___x_23_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_17_, 2);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_8_, v___x_20_);
v_exceptConds_22_ = l_Lean_Syntax_getArgs(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = l_Lean_Fmt_fmtTSepArray___redArg(v_exceptConds_22_, v_a_9_, v_a_19_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_26_; lean_object* v_rbTk_27_; lean_object* v___x_28_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
v_a_25_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_23_, 2);
v___x_26_ = lean_unsigned_to_nat(2u);
v_rbTk_27_ = l_Lean_Syntax_getArg(v_x_8_, v___x_26_);
lean_dec(v_x_8_);
v___x_28_ = l_Lean_Fmt_fmt(v_rbTk_27_, v_a_9_, v_a_25_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_39_ == 0)
{
v___x_32_ = v___x_28_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_34_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_a_24_);
v___x_35_ = l_Lean_Fmt_Layouts_metaApplication(v_a_18_, v___x_34_, v_a_29_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_35_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_a_30_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_dec(v_a_24_);
lean_dec(v_a_18_);
return v___x_28_;
}
}
else
{
lean_object* v_a_40_; lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_18_);
lean_dec(v_x_8_);
v_a_40_ = lean_ctor_get(v___x_23_, 0);
v_a_41_ = lean_ctor_get(v___x_23_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_23_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_inc(v_a_40_);
lean_dec(v___x_23_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_40_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
else
{
lean_dec(v_x_8_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackType___boxed(lean_object* v_x_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Fmt_fmtEStackType(v_x_49_, v_a_50_, v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Fmt_fmtAttribute;
v___x_62_ = ((lean_object*)(l_Lean_Fmt_fmtEStackType___closed__3));
v___x_63_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___closed__3));
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEStackType___boxed), 3, 0);
v___x_65_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_61_, v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackValue(lean_object* v_x_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtEStackValue___closed__1));
lean_inc(v_x_73_);
v___x_77_ = l_Lean_Syntax_isOfKind(v_x_73_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_x_73_);
v___x_78_ = l_Lean_Fmt_Error_partialFormatter;
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_a_75_);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v_lbTk_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v_lbTk_81_ = l_Lean_Syntax_getArg(v_x_73_, v___x_80_);
v___x_82_ = l_Lean_Fmt_fmt(v_lbTk_81_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v_a_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_handlers_87_; lean_object* v___x_88_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
v_a_84_ = lean_ctor_get(v___x_82_, 1);
lean_inc(v_a_84_);
lean_dec_ref_known(v___x_82_, 2);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = l_Lean_Syntax_getArg(v_x_73_, v___x_85_);
v_handlers_87_ = l_Lean_Syntax_getArgs(v___x_86_);
lean_dec(v___x_86_);
v___x_88_ = l_Lean_Fmt_fmtTSepArray___redArg(v_handlers_87_, v_a_74_, v_a_84_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_91_; lean_object* v_rbTk_92_; lean_object* v___x_93_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
v_a_90_ = lean_ctor_get(v___x_88_, 1);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_88_, 2);
v___x_91_ = lean_unsigned_to_nat(2u);
v_rbTk_92_ = l_Lean_Syntax_getArg(v_x_73_, v___x_91_);
lean_dec(v_x_73_);
v___x_93_ = l_Lean_Fmt_fmt(v_rbTk_92_, v_a_74_, v_a_90_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_104_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_a_95_ = lean_ctor_get(v___x_93_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_104_ == 0)
{
v___x_97_ = v___x_93_;
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_99_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_a_89_);
v___x_100_ = l_Lean_Fmt_Layouts_metaApplication(v_a_83_, v___x_99_, v_a_94_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_102_ = v___x_97_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_a_95_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_dec(v_a_89_);
lean_dec(v_a_83_);
return v___x_93_;
}
}
else
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_a_83_);
lean_dec(v_x_73_);
v_a_105_ = lean_ctor_get(v___x_88_, 0);
v_a_106_ = lean_ctor_get(v___x_88_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_88_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_inc(v_a_105_);
lean_dec(v___x_88_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_105_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
else
{
lean_dec(v_x_73_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEStackValue___boxed(lean_object* v_x_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Fmt_fmtEStackValue(v_x_114_, v_a_115_, v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1(){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_Fmt_fmtAttribute;
v___x_125_ = ((lean_object*)(l_Lean_Fmt_fmtEStackValue___closed__1));
v___x_126_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___closed__1));
v___x_127_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEStackValue___boxed), 3, 0);
v___x_128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_124_, v___x_125_, v___x_126_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1___boxed(lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1();
return v_res_130_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_WP_EStack(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackType___regBuiltin_Lean_Fmt_fmtEStackType__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_EStack_0__Lean_Fmt_fmtEStackValue___regBuiltin_Lean_Fmt_fmtEStackValue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_WP_EStack(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_WP_EStack(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_WP_EStack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_WP_EStack(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_WP_EStack(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_EStack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_WP_EStack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_WP_EStack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_WP_EStack(builtin);
}
#ifdef __cplusplus
}
#endif
