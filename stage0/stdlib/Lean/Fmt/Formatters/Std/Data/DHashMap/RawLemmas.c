// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Data.DHashMap.RawLemmas
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Data.DHashMap.RawLemmas import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpToRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtSimpToRaw___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSimpToRaw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DHashMap"};
static const lean_object* l_Lean_Fmt_fmtSimpToRaw___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSimpToRaw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Fmt_fmtSimpToRaw___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtSimpToRaw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Lean_Fmt_fmtSimpToRaw___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtSimpToRaw___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "tacticSimp_to_rawUsing_"};
static const lean_object* l_Lean_Fmt_fmtSimpToRaw___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 125, 75, 48, 212, 67, 75, 250)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 104, 179, 169, 145, 232, 38, 237)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__3_value),LEAN_SCALAR_PTR_LITERAL(21, 211, 193, 39, 213, 47, 180, 148)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpToRaw___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 100, 190, 90, 247, 156, 180, 26)}};
static const lean_object* l_Lean_Fmt_fmtSimpToRaw___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtSimpToRaw___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToRaw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToRaw___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtSimpToRaw"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 183, 182, 25, 175, 193, 126, 187)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToRaw(lean_object* v_x_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_20_; lean_object* v___y_21_; lean_object* v___y_22_; 
v___x_15_ = ((lean_object*)(l_Lean_Fmt_fmtSimpToRaw___closed__5));
lean_inc(v_x_12_);
v___x_16_ = l_Lean_Syntax_isOfKind(v_x_12_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_x_12_);
v___x_42_ = l_Lean_Fmt_Error_partialFormatter;
v___x_43_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v_a_14_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; lean_object* v_simpToRawTk_45_; lean_object* v_usingTk_x3f_47_; lean_object* v_usingArg_x3f_48_; lean_object* v___y_49_; lean_object* v___y_50_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v_simpToRawTk_45_ = l_Lean_Syntax_getArg(v_x_12_, v___x_44_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = l_Lean_Syntax_getArg(v_x_12_, v___x_68_);
lean_dec(v_x_12_);
v___x_70_ = l_Lean_Syntax_isNone(v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_69_);
v___x_72_ = l_Lean_Syntax_matchesNull(v___x_69_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v___x_69_);
lean_dec(v_simpToRawTk_45_);
v___x_73_ = l_Lean_Fmt_Error_partialFormatter;
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_a_14_);
return v___x_74_;
}
else
{
lean_object* v_usingTk_x3f_75_; lean_object* v_usingArg_x3f_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_usingTk_x3f_75_ = l_Lean_Syntax_getArg(v___x_69_, v___x_44_);
v_usingArg_x3f_76_ = l_Lean_Syntax_getArg(v___x_69_, v___x_68_);
lean_dec(v___x_69_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v_usingTk_x3f_75_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_usingArg_x3f_76_);
v_usingTk_x3f_47_ = v___x_77_;
v_usingArg_x3f_48_ = v___x_78_;
v___y_49_ = v_a_13_;
v___y_50_ = v_a_14_;
goto v___jp_46_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec(v___x_69_);
v___x_79_ = lean_box(0);
v_usingTk_x3f_47_ = v___x_79_;
v_usingArg_x3f_48_ = v___x_79_;
v___y_49_ = v_a_13_;
v___y_50_ = v_a_14_;
goto v___jp_46_;
}
v___jp_46_:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Fmt_fmt(v_simpToRawTk_45_, v___y_49_, v___y_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v_a_53_; lean_object* v___x_54_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
v_a_53_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_51_, 2);
v___x_54_ = l_Lean_Fmt_fmt_x3f(v_usingTk_x3f_47_, v___y_49_, v_a_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
if (lean_obj_tag(v_usingArg_x3f_48_) == 0)
{
lean_object* v_a_55_; lean_object* v_a_56_; lean_object* v___x_57_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_55_);
v_a_56_ = lean_ctor_get(v___x_54_, 1);
lean_inc(v_a_56_);
lean_dec_ref_known(v___x_54_, 2);
v___x_57_ = lean_box(0);
v___y_18_ = v_a_55_;
v___y_19_ = v___y_49_;
v___y_20_ = v_a_56_;
v___y_21_ = v_a_52_;
v___y_22_ = v___x_57_;
goto v___jp_17_;
}
else
{
lean_object* v_a_58_; lean_object* v_a_59_; lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_58_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_58_);
v_a_59_ = lean_ctor_get(v___x_54_, 1);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_54_, 2);
v_val_60_ = lean_ctor_get(v_usingArg_x3f_48_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_usingArg_x3f_48_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v_usingArg_x3f_48_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v_usingArg_x3f_48_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_val_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
v___y_18_ = v_a_58_;
v___y_19_ = v___y_49_;
v___y_20_ = v_a_59_;
v___y_21_ = v_a_52_;
v___y_22_ = v___x_65_;
goto v___jp_17_;
}
}
}
}
else
{
lean_dec(v_a_52_);
lean_dec(v_usingArg_x3f_48_);
return v___x_54_;
}
}
else
{
lean_dec(v_usingArg_x3f_48_);
lean_dec(v_usingTk_x3f_47_);
return v___x_51_;
}
}
}
v___jp_17_:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Fmt_fmt_x3f(v___y_22_, v___y_19_, v___y_20_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_41_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_a_25_ = lean_ctor_get(v___x_23_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_41_ == 0)
{
v___x_27_ = v___x_23_;
v_isShared_28_ = v_isSharedCheck_41_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_41_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_29_ = 0;
v___x_30_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_18_, v_a_24_, v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_31_, 0, v___y_21_);
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*1, v___x_16_);
v___x_32_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set_uint8(v___x_32_, sizeof(void*)*1, v___x_16_);
v___x_33_ = lean_unsigned_to_nat(2u);
v___x_34_ = lean_mk_empty_array_with_capacity(v___x_33_);
v___x_35_ = lean_array_push(v___x_34_, v___x_31_);
v___x_36_ = lean_array_push(v___x_35_, v___x_32_);
v___x_37_ = l_Lean_Fmt_Layouts_blocks(v___x_36_, v___x_16_);
lean_dec_ref(v___x_36_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_37_);
v___x_39_ = v___x_27_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_a_25_);
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
lean_dec_ref(v___y_21_);
lean_dec_ref(v___y_18_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToRaw___boxed(lean_object* v_x_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Fmt_fmtSimpToRaw(v_x_80_, v_a_81_, v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1(){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = l_Lean_Fmt_fmtAttribute;
v___x_93_ = ((lean_object*)(l_Lean_Fmt_fmtSimpToRaw___closed__5));
v___x_94_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___closed__3));
v___x_95_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpToRaw___boxed), 3, 0);
v___x_96_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_92_, v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1___boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1();
return v_res_98_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas_0__Lean_Fmt_fmtSimpToRaw___regBuiltin_Lean_Fmt_fmtSimpToRaw__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Data_DHashMap_RawLemmas(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawLemmas(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_RawLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
