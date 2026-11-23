// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Util.Reprove
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Util.Reprove import Init.Data
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtReprove___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtReprove___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtReprove___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtReprove___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reprove"};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReprove___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReprove___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReprove___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 205, 199, 204, 102, 230, 156, 30)}};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtReprove___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtReprove___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtReprove___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReprove___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReprove___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__6_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtReprove___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReprove___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtReprove___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtReprove___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReprove(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReprove___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtReprove"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtReprove___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 17, 110, 26, 153, 189, 178, 52)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReprove(lean_object* v_x_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = ((lean_object*)(l_Lean_Fmt_fmtReprove___closed__4));
lean_inc(v_x_18_);
v___x_22_ = l_Lean_Syntax_isOfKind(v_x_18_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_x_18_);
v___x_23_ = l_Lean_Fmt_Error_partialFormatter;
v___x_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v_a_20_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_25_ = lean_unsigned_to_nat(3u);
v___x_26_ = l_Lean_Syntax_getArg(v_x_18_, v___x_25_);
v___x_27_ = ((lean_object*)(l_Lean_Fmt_fmtReprove___closed__8));
lean_inc(v___x_26_);
v___x_28_ = l_Lean_Syntax_isOfKind(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v___x_26_);
lean_dec(v_x_18_);
v___x_29_ = l_Lean_Fmt_Error_partialFormatter;
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_a_20_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v_reproveTk_32_; lean_object* v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v_reproveTk_32_ = l_Lean_Syntax_getArg(v_x_18_, v___x_31_);
v___x_33_ = l_Lean_Fmt_fmt(v_reproveTk_32_, v_a_19_, v_a_20_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v_ids_38_; lean_object* v___x_39_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
v_a_35_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_33_, 2);
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = l_Lean_Syntax_getArg(v_x_18_, v___x_36_);
v_ids_38_ = l_Lean_Syntax_getArgs(v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = l_Lean_Fmt_fmtArray___redArg(v_ids_38_, v_a_19_, v_a_35_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v_a_41_; lean_object* v___x_42_; lean_object* v_byTk_43_; lean_object* v___x_44_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
v_a_41_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_a_41_);
lean_dec_ref_known(v___x_39_, 2);
v___x_42_ = lean_unsigned_to_nat(2u);
v_byTk_43_ = l_Lean_Syntax_getArg(v_x_18_, v___x_42_);
lean_dec(v_x_18_);
v___x_44_ = l_Lean_Fmt_fmt(v_byTk_43_, v_a_19_, v_a_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v_a_46_; lean_object* v___x_47_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
v_a_46_ = lean_ctor_get(v___x_44_, 1);
lean_inc(v_a_46_);
lean_dec_ref_known(v___x_44_, 2);
v___x_47_ = l_Lean_Fmt_fmt(v___x_26_, v_a_19_, v_a_46_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_65_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_a_49_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_65_ == 0)
{
v___x_51_ = v___x_47_;
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_53_ = l_Lean_Fmt_Layouts_fill(v_a_40_);
lean_dec(v_a_40_);
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_42_);
v___x_55_ = lean_array_push(v___x_54_, v_a_34_);
v___x_56_ = lean_array_push(v___x_55_, v___x_53_);
v___x_57_ = 0;
v___x_58_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_58_, 0, v___x_28_);
lean_ctor_set_uint8(v___x_58_, 1, v___x_57_);
lean_ctor_set_uint8(v___x_58_, 2, v___x_57_);
lean_ctor_set_uint8(v___x_58_, 3, v___x_57_);
v___x_59_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_56_, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_60_, 0, v___x_28_);
lean_ctor_set_uint8(v___x_60_, 1, v___x_28_);
v___x_61_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_59_, v_a_45_, v_a_48_, v___x_60_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_61_);
v___x_63_ = v___x_51_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_a_49_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
else
{
lean_dec(v_a_45_);
lean_dec(v_a_40_);
lean_dec(v_a_34_);
return v___x_47_;
}
}
else
{
lean_dec(v_a_40_);
lean_dec(v_a_34_);
lean_dec(v___x_26_);
return v___x_44_;
}
}
else
{
lean_object* v_a_66_; lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_a_34_);
lean_dec(v___x_26_);
lean_dec(v_x_18_);
v_a_66_ = lean_ctor_get(v___x_39_, 0);
v_a_67_ = lean_ctor_get(v___x_39_, 1);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_39_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_inc(v_a_66_);
lean_dec(v___x_39_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_66_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_dec(v___x_26_);
lean_dec(v_x_18_);
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReprove___boxed(lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Fmt_fmtReprove(v_x_75_, v_a_76_, v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1(){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = l_Lean_Fmt_fmtAttribute;
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtReprove___closed__4));
v___x_88_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___closed__2));
v___x_89_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtReprove___boxed), 3, 0);
v___x_90_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_86_, v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1___boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1();
return v_res_92_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Reprove(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Util_Reprove_0__Lean_Fmt_fmtReprove___regBuiltin_Lean_Fmt_fmtReprove__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Util_Reprove(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Util_Reprove(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Util_Reprove(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_Reprove(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Util_Reprove(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Reprove(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Reprove(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Util_Reprove(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Util_Reprove(builtin);
}
#ifdef __cplusplus
}
#endif
