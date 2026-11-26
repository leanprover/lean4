// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Data.DHashMap.Internal.RawLemmas
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Data.DHashMap.Internal.RawLemmas import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpToModelLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtSimpToModelLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpToModelLike___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpToModelLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtSimpToModelLike___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpToModelLike___closed__1_value;
static const lean_closure_object l_Lean_Fmt_fmtSimpToModelLike___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtSimpToModelLike___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimpToModelLike___closed__2_value;
static const lean_array_object l_Lean_Fmt_fmtSimpToModelLike___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtSimpToModelLike___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSimpToModelLike___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToModelLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToModelLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DHashMap"};
static const lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = "Raw₀"};
static const lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "tacticSimp_to_model[_]Using_"};
static const lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 125, 75, 48, 212, 67, 75, 250)}};
static const lean_ctor_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 104, 179, 169, 145, 232, 38, 237)}};
static const lean_ctor_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(127, 175, 181, 7, 217, 228, 5, 230)}};
static const lean_ctor_object l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 179, 159, 53, 206, 161, 166, 129)}};
static const lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtHashMapSimpToModel___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHashMapSimpToModel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtHashMapSimpToModel"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(173, 177, 122, 123, 246, 42, 26, 116)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToModelLike(lean_object* v_simpToModelTk_8_, lean_object* v_lbTk_x3f_9_, lean_object* v_names_x3f_10_, lean_object* v_rbTk_x3f_11_, lean_object* v_usingTk_x3f_12_, lean_object* v_usingArg_x3f_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Fmt_fmt(v_simpToModelTk_8_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_a_17_);
v_a_18_ = lean_ctor_get(v___x_16_, 1);
lean_inc(v_a_18_);
lean_dec_ref_known(v___x_16_, 2);
v___x_19_ = l_Lean_Fmt_fmt_x3f(v_lbTk_x3f_9_, v_a_14_, v_a_18_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___y_28_; lean_object* v___y_57_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_19_, 2);
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtSimpToModelLike___closed__0));
if (lean_obj_tag(v_names_x3f_10_) == 0)
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtSimpToModelLike___closed__3));
v___y_57_ = v___x_87_;
goto v___jp_56_;
}
else
{
lean_object* v_val_88_; 
v_val_88_ = lean_ctor_get(v_names_x3f_10_, 0);
lean_inc(v_val_88_);
lean_dec_ref_known(v_names_x3f_10_, 1);
v___y_57_ = v_val_88_;
goto v___jp_56_;
}
v___jp_23_:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Fmt_fmt_x3f(v___y_28_, v_a_14_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_55_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_55_ == 0)
{
v___x_33_ = v___x_29_;
v_isShared_34_ = v_isSharedCheck_55_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_55_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_35_ = 1;
v___x_36_ = ((lean_object*)(l_Lean_Fmt_fmtSimpToModelLike___closed__1));
v___x_37_ = l_Lean_Fmt_Layouts_collection(v___x_22_, v_a_20_, v___y_27_, v___y_25_, v___x_36_);
lean_dec_ref(v___y_27_);
v___x_38_ = ((lean_object*)(l_Lean_Fmt_fmtSimpToModelLike___closed__2));
v___x_39_ = lean_box(0);
v___x_40_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v___x_37_, v___x_38_, v___x_39_);
v___x_41_ = 0;
v___x_42_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_24_, v_a_30_, v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_43_, 0, v_a_17_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*1, v___x_35_);
v___x_44_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_40_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_35_);
v___x_45_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_45_, 0, v___x_42_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*1, v___x_35_);
v___x_46_ = lean_unsigned_to_nat(3u);
v___x_47_ = lean_mk_empty_array_with_capacity(v___x_46_);
v___x_48_ = lean_array_push(v___x_47_, v___x_43_);
v___x_49_ = lean_array_push(v___x_48_, v___x_44_);
v___x_50_ = lean_array_push(v___x_49_, v___x_45_);
v___x_51_ = l_Lean_Fmt_Layouts_blocks(v___x_50_, v___x_35_);
lean_dec_ref(v___x_50_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_51_);
v___x_53_ = v___x_33_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_a_31_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
else
{
lean_dec_ref(v___y_27_);
lean_dec_ref(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v_a_20_);
lean_dec(v_a_17_);
return v___x_29_;
}
}
v___jp_56_:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_57_, v_a_14_, v_a_21_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v_a_60_; lean_object* v___x_61_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
v_a_60_ = lean_ctor_get(v___x_58_, 1);
lean_inc(v_a_60_);
lean_dec_ref_known(v___x_58_, 2);
v___x_61_ = l_Lean_Fmt_fmt_x3f(v_rbTk_x3f_11_, v_a_14_, v_a_60_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v_a_63_; lean_object* v___x_64_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
v_a_63_ = lean_ctor_get(v___x_61_, 1);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_61_, 2);
v___x_64_ = l_Lean_Fmt_fmt_x3f(v_usingTk_x3f_12_, v_a_14_, v_a_63_);
if (lean_obj_tag(v___x_64_) == 0)
{
if (lean_obj_tag(v_usingArg_x3f_13_) == 0)
{
lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v___x_67_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
v_a_66_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_64_, 2);
v___x_67_ = lean_box(0);
v___y_24_ = v_a_65_;
v___y_25_ = v_a_62_;
v___y_26_ = v_a_66_;
v___y_27_ = v_a_59_;
v___y_28_ = v___x_67_;
goto v___jp_23_;
}
else
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v_val_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
v_a_68_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_64_, 2);
v_val_70_ = lean_ctor_get(v_usingArg_x3f_13_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v_usingArg_x3f_13_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v_usingArg_x3f_13_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_val_70_);
lean_dec(v_usingArg_x3f_13_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_val_70_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
v___y_24_ = v_a_68_;
v___y_25_ = v_a_62_;
v___y_26_ = v_a_69_;
v___y_27_ = v_a_59_;
v___y_28_ = v___x_75_;
goto v___jp_23_;
}
}
}
}
else
{
lean_dec(v_a_62_);
lean_dec(v_a_59_);
lean_dec(v_a_20_);
lean_dec(v_a_17_);
lean_dec(v_usingArg_x3f_13_);
return v___x_64_;
}
}
else
{
lean_dec(v_a_59_);
lean_dec(v_a_20_);
lean_dec(v_a_17_);
lean_dec(v_usingArg_x3f_13_);
lean_dec(v_usingTk_x3f_12_);
return v___x_61_;
}
}
else
{
lean_object* v_a_78_; lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
lean_dec(v_a_20_);
lean_dec(v_a_17_);
lean_dec(v_usingArg_x3f_13_);
lean_dec(v_usingTk_x3f_12_);
lean_dec(v_rbTk_x3f_11_);
v_a_78_ = lean_ctor_get(v___x_58_, 0);
v_a_79_ = lean_ctor_get(v___x_58_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_58_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_inc(v_a_78_);
lean_dec(v___x_58_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_78_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
else
{
lean_dec(v_a_17_);
lean_dec(v_usingArg_x3f_13_);
lean_dec(v_usingTk_x3f_12_);
lean_dec(v_rbTk_x3f_11_);
lean_dec(v_names_x3f_10_);
return v___x_19_;
}
}
else
{
lean_dec(v_usingArg_x3f_13_);
lean_dec(v_usingTk_x3f_12_);
lean_dec(v_rbTk_x3f_11_);
lean_dec(v_names_x3f_10_);
lean_dec(v_lbTk_x3f_9_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpToModelLike___boxed(lean_object* v_simpToModelTk_89_, lean_object* v_lbTk_x3f_90_, lean_object* v_names_x3f_91_, lean_object* v_rbTk_x3f_92_, lean_object* v_usingTk_x3f_93_, lean_object* v_usingArg_x3f_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Fmt_fmtSimpToModelLike(v_simpToModelTk_89_, v_lbTk_x3f_90_, v_names_x3f_91_, v_rbTk_x3f_92_, v_usingTk_x3f_93_, v_usingArg_x3f_94_, v_a_95_, v_a_96_);
lean_dec_ref(v_a_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHashMapSimpToModel(lean_object* v_x_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_Fmt_fmtHashMapSimpToModel___closed__5));
lean_inc(v_x_109_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_x_109_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_x_109_);
v___x_114_ = l_Lean_Fmt_Error_partialFormatter;
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_a_111_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v_simpToModelTk_117_; lean_object* v___x_118_; lean_object* v_lbTk_x3f_120_; lean_object* v_names_x3f_121_; lean_object* v_rbTk_x3f_122_; lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v_simpToModelTk_117_ = l_Lean_Syntax_getArg(v_x_109_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_138_ = l_Lean_Syntax_getArg(v_x_109_, v___x_118_);
v___x_139_ = l_Lean_Syntax_isNone(v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_138_);
v___x_141_ = l_Lean_Syntax_matchesNull(v___x_138_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v___x_138_);
lean_dec(v_simpToModelTk_117_);
lean_dec(v_x_109_);
v___x_142_ = l_Lean_Fmt_Error_partialFormatter;
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_111_);
return v___x_143_;
}
else
{
lean_object* v_lbTk_x3f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_rbTk_x3f_147_; lean_object* v_names_x3f_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_lbTk_x3f_144_ = l_Lean_Syntax_getArg(v___x_138_, v___x_116_);
v___x_145_ = l_Lean_Syntax_getArg(v___x_138_, v___x_118_);
v___x_146_ = lean_unsigned_to_nat(2u);
v_rbTk_x3f_147_ = l_Lean_Syntax_getArg(v___x_138_, v___x_146_);
lean_dec(v___x_138_);
v_names_x3f_148_ = l_Lean_Syntax_getArgs(v___x_145_);
lean_dec(v___x_145_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v_lbTk_x3f_144_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v_names_x3f_148_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v_rbTk_x3f_147_);
v_lbTk_x3f_120_ = v___x_149_;
v_names_x3f_121_ = v___x_150_;
v_rbTk_x3f_122_ = v___x_151_;
v___y_123_ = v_a_110_;
v___y_124_ = v_a_111_;
goto v___jp_119_;
}
}
else
{
lean_object* v___x_152_; 
lean_dec(v___x_138_);
v___x_152_ = lean_box(0);
v_lbTk_x3f_120_ = v___x_152_;
v_names_x3f_121_ = v___x_152_;
v_rbTk_x3f_122_ = v___x_152_;
v___y_123_ = v_a_110_;
v___y_124_ = v_a_111_;
goto v___jp_119_;
}
v___jp_119_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = lean_unsigned_to_nat(2u);
v___x_126_ = l_Lean_Syntax_getArg(v_x_109_, v___x_125_);
lean_dec(v_x_109_);
v___x_127_ = l_Lean_Syntax_isNone(v___x_126_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
lean_inc(v___x_126_);
v___x_128_ = l_Lean_Syntax_matchesNull(v___x_126_, v___x_125_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v___x_126_);
lean_dec(v_rbTk_x3f_122_);
lean_dec(v_names_x3f_121_);
lean_dec(v_lbTk_x3f_120_);
lean_dec(v_simpToModelTk_117_);
v___x_129_ = l_Lean_Fmt_Error_partialFormatter;
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___y_124_);
return v___x_130_;
}
else
{
lean_object* v_usingTk_x3f_131_; lean_object* v_usingArg_x3f_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_usingTk_x3f_131_ = l_Lean_Syntax_getArg(v___x_126_, v___x_116_);
v_usingArg_x3f_132_ = l_Lean_Syntax_getArg(v___x_126_, v___x_118_);
lean_dec(v___x_126_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v_usingTk_x3f_131_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_usingArg_x3f_132_);
v___x_135_ = l_Lean_Fmt_fmtSimpToModelLike(v_simpToModelTk_117_, v_lbTk_x3f_120_, v_names_x3f_121_, v_rbTk_x3f_122_, v___x_133_, v___x_134_, v___y_123_, v___y_124_);
return v___x_135_;
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v___x_126_);
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_Fmt_fmtSimpToModelLike(v_simpToModelTk_117_, v_lbTk_x3f_120_, v_names_x3f_121_, v_rbTk_x3f_122_, v___x_136_, v___x_136_, v___y_123_, v___y_124_);
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHashMapSimpToModel___boxed(lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Fmt_fmtHashMapSimpToModel(v_x_153_, v_a_154_, v_a_155_);
lean_dec_ref(v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1(){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = l_Lean_Fmt_fmtAttribute;
v___x_166_ = ((lean_object*)(l_Lean_Fmt_fmtHashMapSimpToModel___closed__5));
v___x_167_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___closed__3));
v___x_168_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtHashMapSimpToModel___boxed), 3, 0);
v___x_169_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_165_, v___x_166_, v___x_167_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1___boxed(lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1();
return v_res_171_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas_0__Lean_Fmt_fmtHashMapSimpToModel___regBuiltin_Lean_Fmt_fmtHashMapSimpToModel__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
