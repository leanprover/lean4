// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Do.SPred.Notation.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Do.SPred.Notation.Basic import Init.Data
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
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtSPred___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSPred___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Fmt_fmtSPred___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSPred___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termSpred(_)"};
static const lean_object* l_Lean_Fmt_fmtSPred___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSPred___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSPred___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPred___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPred___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPred___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPred___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 240, 91, 148, 237, 191, 255, 193)}};
static const lean_object* l_Lean_Fmt_fmtSPred___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSPred___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPred(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPred___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtSPred"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 105, 41, 196, 86, 154, 75, 97)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSPredTermEscape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "termTerm(_)"};
static const lean_object* l_Lean_Fmt_fmtSPredTermEscape___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSPredTermEscape___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSPredTermEscape___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPredTermEscape___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPredTermEscape___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPredTermEscape___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPredTermEscape___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSPredTermEscape___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 176, 69, 25, 99, 246, 131, 165)}};
static const lean_object* l_Lean_Fmt_fmtSPredTermEscape___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSPredTermEscape___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTermEscape(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTermEscape___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtSPredTermEscape"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 75, 215, 184, 160, 201, 227, 197)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPred(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Fmt_fmtSPred___closed__3));
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
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_17_, 2);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_8_, v___x_20_);
v___x_22_ = l_Lean_Fmt_fmt(v___x_21_, v_a_9_, v_a_19_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_25_; lean_object* v_rbTk_26_; lean_object* v___x_27_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_a_23_);
v_a_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_22_, 2);
v___x_25_ = lean_unsigned_to_nat(2u);
v_rbTk_26_ = l_Lean_Syntax_getArg(v_x_8_, v___x_25_);
lean_dec(v_x_8_);
v___x_27_ = l_Lean_Fmt_fmt(v_rbTk_26_, v_a_9_, v_a_24_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_41_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_a_29_ = lean_ctor_get(v___x_27_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_41_ == 0)
{
v___x_31_ = v___x_27_;
v_isShared_32_ = v_isSharedCheck_41_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_41_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_20_);
lean_inc_ref(v___x_33_);
v___x_34_ = lean_array_push(v___x_33_, v_a_23_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
v___x_36_ = lean_array_push(v___x_33_, v___x_35_);
v___x_37_ = l_Lean_Fmt_Layouts_metaApplication(v_a_18_, v___x_36_, v_a_28_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_37_);
v___x_39_ = v___x_31_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_a_29_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_dec(v_a_23_);
lean_dec(v_a_18_);
return v___x_27_;
}
}
else
{
lean_dec(v_a_18_);
lean_dec(v_x_8_);
return v___x_22_;
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
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPred___boxed(lean_object* v_x_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Fmt_fmtSPred(v_x_42_, v_a_43_, v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = l_Lean_Fmt_fmtAttribute;
v___x_55_ = ((lean_object*)(l_Lean_Fmt_fmtSPred___closed__3));
v___x_56_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___closed__3));
v___x_57_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSPred___boxed), 3, 0);
v___x_58_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_54_, v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1___boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTermEscape(lean_object* v_x_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_Fmt_fmtSPredTermEscape___closed__1));
lean_inc(v_x_66_);
v___x_70_ = l_Lean_Syntax_isOfKind(v_x_66_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_x_66_);
v___x_71_ = l_Lean_Fmt_Error_partialFormatter;
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_a_68_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v_lbTk_74_; lean_object* v___x_75_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v_lbTk_74_ = l_Lean_Syntax_getArg(v_x_66_, v___x_73_);
v___x_75_ = l_Lean_Fmt_fmt(v_lbTk_74_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v_a_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
v_a_77_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_75_, 2);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = l_Lean_Syntax_getArg(v_x_66_, v___x_78_);
v___x_80_ = l_Lean_Fmt_fmt(v___x_79_, v_a_67_, v_a_77_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v_rbTk_84_; lean_object* v___x_85_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_81_);
v_a_82_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_80_, 2);
v___x_83_ = lean_unsigned_to_nat(2u);
v_rbTk_84_ = l_Lean_Syntax_getArg(v_x_66_, v___x_83_);
lean_dec(v_x_66_);
v___x_85_ = l_Lean_Fmt_fmt(v_rbTk_84_, v_a_67_, v_a_82_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_99_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_a_87_ = lean_ctor_get(v___x_85_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_99_ == 0)
{
v___x_89_ = v___x_85_;
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_78_);
lean_inc_ref(v___x_91_);
v___x_92_ = lean_array_push(v___x_91_, v_a_81_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
v___x_94_ = lean_array_push(v___x_91_, v___x_93_);
v___x_95_ = l_Lean_Fmt_Layouts_metaApplication(v_a_76_, v___x_94_, v_a_86_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_95_);
v___x_97_ = v___x_89_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_a_87_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
else
{
lean_dec(v_a_81_);
lean_dec(v_a_76_);
return v___x_85_;
}
}
else
{
lean_dec(v_a_76_);
lean_dec(v_x_66_);
return v___x_80_;
}
}
else
{
lean_dec(v_x_66_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTermEscape___boxed(lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Fmt_fmtSPredTermEscape(v_x_100_, v_a_101_, v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1(){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = l_Lean_Fmt_fmtAttribute;
v___x_111_ = ((lean_object*)(l_Lean_Fmt_fmtSPredTermEscape___closed__1));
v___x_112_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___closed__1));
v___x_113_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSPredTermEscape___boxed), 3, 0);
v___x_114_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_110_, v___x_111_, v___x_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1___boxed(lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1();
return v_res_116_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPred___regBuiltin_Lean_Fmt_fmtSPred__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic_0__Lean_Fmt_fmtSPredTermEscape___regBuiltin_Lean_Fmt_fmtSPredTermEscape__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
