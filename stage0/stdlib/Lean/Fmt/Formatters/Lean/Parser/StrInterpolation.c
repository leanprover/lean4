// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.StrInterpolation
// Imports: public import Lean.Fmt.FmtM.Basic import Lean.Fmt.Formatters.Lean.Parser.Term meta import Lean.Parser.StrInterpolation import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Fmt_fmtStr_lex(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtStr_build(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_strLit(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "interpolatedStrLitKind"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 181, 130, 246, 88, 58, 26, 43)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtInterpolatedStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtInterpolatedStr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInterpolatedStr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtInterpolatedStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtInterpolatedStr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtInterpolatedStr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInterpolatedStr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInterpolatedStr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInterpolatedStr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtInterpolatedStr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(198, 35, 59, 82, 181, 253, 146, 162)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg(lean_object* v_upperBound_7_, lean_object* v_stx_8_, lean_object* v_args_9_, lean_object* v___x_10_, lean_object* v_a_11_, lean_object* v_b_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
lean_object* v_a_16_; lean_object* v_a_17_; uint8_t v___x_21_; 
v___x_21_ = lean_nat_dec_lt(v_a_11_, v_upperBound_7_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_dec(v_a_11_);
lean_dec(v_stx_8_);
v___x_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_22_, 0, v_b_12_);
lean_ctor_set(v___x_22_, 1, v___y_14_);
return v___x_22_;
}
else
{
lean_object* v_snd_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_139_; 
v_snd_23_ = lean_ctor_get(v_b_12_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_b_12_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v_b_12_, 0);
lean_dec(v_unused_140_);
v___x_25_ = v_b_12_;
v_isShared_26_ = v_isSharedCheck_139_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_snd_23_);
lean_dec(v_b_12_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_139_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_51_; lean_object* v___y_53_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_51_ = lean_box(0);
v___x_81_ = lean_array_fget_borrowed(v_args_9_, v_a_11_);
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = lean_nat_mod(v_a_11_, v___x_82_);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_dec_eq(v___x_83_, v___x_84_);
lean_dec(v___x_83_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__1));
v___x_87_ = l_Lean_Syntax_isLit_x3f(v___x_86_, v___x_81_);
if (lean_obj_tag(v___x_87_) == 1)
{
lean_object* v_val_88_; lean_object* v___x_89_; lean_object* v___y_91_; lean_object* v___y_92_; lean_object* v___y_106_; uint8_t v___x_111_; 
v_val_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_val_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_nat_dec_eq(v_a_11_, v___x_89_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__4));
v___y_106_ = v___x_112_;
goto v___jp_105_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__3));
v___y_106_ = v___x_113_;
goto v___jp_105_;
}
v___jp_90_:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_string_length(v_val_88_);
v___x_94_ = lean_nat_dec_le(v___x_82_, v___x_93_);
if (v___x_94_ == 0)
{
lean_dec(v_val_88_);
lean_dec(v_a_11_);
goto v___jp_27_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = lean_string_utf8_byte_size(v_val_88_);
v___x_96_ = lean_string_utf8_byte_size(v___y_91_);
v___x_97_ = lean_nat_dec_le(v___x_96_, v___x_95_);
if (v___x_97_ == 0)
{
lean_dec(v_val_88_);
lean_dec(v_a_11_);
goto v___jp_27_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = lean_string_memcmp(v_val_88_, v___y_91_, v___x_89_, v___x_89_, v___x_96_);
if (v___x_98_ == 0)
{
lean_dec(v_val_88_);
lean_dec(v_a_11_);
goto v___jp_27_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_string_utf8_byte_size(v___y_92_);
v___x_100_ = lean_nat_dec_le(v___x_99_, v___x_95_);
if (v___x_100_ == 0)
{
lean_dec(v_val_88_);
lean_dec(v_a_11_);
goto v___jp_27_;
}
else
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_nat_sub(v___x_95_, v___x_99_);
v___x_102_ = lean_string_memcmp(v_val_88_, v___y_92_, v___x_101_, v___x_89_, v___x_99_);
lean_dec(v___x_101_);
if (v___x_102_ == 0)
{
lean_dec(v_val_88_);
lean_dec(v_a_11_);
goto v___jp_27_;
}
else
{
lean_object* v___x_103_; 
lean_del_object(v___x_25_);
v___x_103_ = l_String_toListImpl(v_val_88_);
if (lean_obj_tag(v___x_103_) == 0)
{
v___y_53_ = v___x_103_;
goto v___jp_52_;
}
else
{
lean_object* v_tail_104_; 
v_tail_104_ = lean_ctor_get(v___x_103_, 1);
lean_inc(v_tail_104_);
lean_dec_ref_known(v___x_103_, 2);
v___y_53_ = v_tail_104_;
goto v___jp_52_;
}
}
}
}
}
}
}
v___jp_105_:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_nat_sub(v___x_10_, v___x_84_);
v___x_108_ = lean_nat_dec_eq(v_a_11_, v___x_107_);
lean_dec(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__2));
v___y_91_ = v___y_106_;
v___y_92_ = v___x_109_;
goto v___jp_90_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___closed__3));
v___y_91_ = v___y_106_;
v___y_92_ = v___x_110_;
goto v___jp_90_;
}
}
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v___x_87_);
lean_del_object(v___x_25_);
lean_dec(v_snd_23_);
lean_dec(v_a_11_);
lean_dec(v_stx_8_);
v___x_114_ = l_Lean_Fmt_Error_partialFormatter;
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___y_14_);
return v___x_115_;
}
}
else
{
lean_object* v___x_116_; 
lean_del_object(v___x_25_);
lean_inc(v___x_81_);
v___x_116_ = l_Lean_Fmt_fmt(v___x_81_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v_doc_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_128_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
v_a_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_116_, 2);
v_doc_119_ = lean_ctor_get(v_a_117_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v_a_117_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v_a_117_, 1);
lean_dec(v_unused_129_);
v___x_121_ = v_a_117_;
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_doc_119_);
lean_dec(v_a_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_123_, 0, v_doc_119_);
v___x_124_ = lean_array_push(v_snd_23_, v___x_123_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_124_);
lean_ctor_set(v___x_121_, 0, v___x_51_);
v___x_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v_a_16_ = v___x_126_;
v_a_17_ = v_a_118_;
goto v___jp_15_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec(v_snd_23_);
lean_dec(v_a_11_);
lean_dec(v_stx_8_);
v_a_130_ = lean_ctor_get(v___x_116_, 0);
v_a_131_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_116_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_inc(v_a_130_);
lean_dec(v___x_116_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_130_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
v___jp_27_:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Fmt_fmtAtomic(v_stx_8_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_41_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_41_ == 0)
{
v___x_32_ = v___x_28_;
v_isShared_33_ = v_isSharedCheck_41_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_41_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v_a_29_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_34_);
v___x_36_ = v___x_25_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_snd_23_);
v___x_36_ = v_reuseFailAlloc_40_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_38_; 
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_36_);
v___x_38_ = v___x_32_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_a_30_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
else
{
lean_object* v_a_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
lean_del_object(v___x_25_);
lean_dec(v_snd_23_);
v_a_42_ = lean_ctor_get(v___x_28_, 0);
v_a_43_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v___x_28_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_inc(v_a_42_);
lean_dec(v___x_28_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_42_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_a_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_array_mk(v___y_53_);
v___x_55_ = lean_array_pop(v___x_54_);
v___x_56_ = lean_array_to_list(v___x_55_);
lean_inc(v_snd_23_);
v___x_57_ = l_Lean_Fmt_fmtStr_lex(v___x_56_, v_snd_23_);
if (lean_obj_tag(v___x_57_) == 1)
{
lean_object* v_val_58_; lean_object* v___x_59_; 
lean_dec(v_snd_23_);
v_val_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_val_58_);
lean_dec_ref_known(v___x_57_, 1);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_51_);
lean_ctor_set(v___x_59_, 1, v_val_58_);
v_a_16_ = v___x_59_;
v_a_17_ = v___y_14_;
goto v___jp_15_;
}
else
{
lean_object* v___x_60_; 
lean_dec(v___x_57_);
lean_dec(v_a_11_);
v___x_60_ = l_Lean_Fmt_fmtAtomic(v_stx_8_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_71_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_a_62_ = lean_ctor_get(v___x_60_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_71_ == 0)
{
v___x_64_ = v___x_60_;
v_isShared_65_ = v_isSharedCheck_71_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_71_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v_a_61_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_snd_23_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_67_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_a_62_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
else
{
lean_object* v_a_72_; lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec(v_snd_23_);
v_a_72_ = lean_ctor_get(v___x_60_, 0);
v_a_73_ = lean_ctor_get(v___x_60_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_60_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_inc(v_a_72_);
lean_dec(v___x_60_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_72_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
}
v___jp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v_a_11_, v___x_18_);
lean_dec(v_a_11_);
v_a_11_ = v___x_19_;
v_b_12_ = v_a_16_;
v___y_14_ = v_a_17_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg___boxed(lean_object* v_upperBound_141_, lean_object* v_stx_142_, lean_object* v_args_143_, lean_object* v___x_144_, lean_object* v_a_145_, lean_object* v_b_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg(v_upperBound_141_, v_stx_142_, v_args_143_, v___x_144_, v_a_145_, v_b_146_, v___y_147_, v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___x_144_);
lean_dec_ref(v_args_143_);
lean_dec(v_upperBound_141_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInterpolatedStr(lean_object* v_stx_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_args_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_args_158_ = l_Lean_Syntax_getArgs(v_stx_155_);
v___x_159_ = lean_array_get_size(v_args_158_);
v___x_160_ = lean_unsigned_to_nat(2u);
v___x_161_ = lean_nat_mod(v___x_159_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_dec_eq(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec_ref(v_args_158_);
lean_dec(v_stx_155_);
v___x_164_ = l_Lean_Fmt_Error_partialFormatter;
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_a_157_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = ((lean_object*)(l_Lean_Fmt_fmtInterpolatedStr___closed__1));
lean_inc(v_stx_155_);
v___x_168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg(v___x_159_, v_stx_155_, v_args_158_, v___x_159_, v___x_166_, v___x_167_, v_a_156_, v_a_157_);
lean_dec_ref(v_args_158_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_fst_170_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_fst_170_ = lean_ctor_get(v_a_169_, 0);
if (lean_obj_tag(v_fst_170_) == 0)
{
lean_object* v_a_171_; lean_object* v_snd_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_inc(v_a_169_);
v_a_171_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_168_, 2);
v_snd_172_ = lean_ctor_get(v_a_169_, 1);
lean_inc(v_snd_172_);
lean_dec(v_a_169_);
v___x_173_ = l_Lean_Fmt_fmtStr_build(v_snd_172_);
v___x_174_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_173_, v_stx_155_, v_a_171_);
lean_dec(v_stx_155_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_185_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_a_176_ = lean_ctor_get(v___x_174_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_185_ == 0)
{
v___x_178_ = v___x_174_;
v_isShared_179_ = v_isSharedCheck_185_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_185_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_180_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_181_ = l_Lean_Fmt_Layouts_strLit(v___x_180_, v_a_175_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_181_);
v___x_183_ = v___x_178_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_a_176_);
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
return v___x_174_;
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
lean_inc_ref(v_fst_170_);
lean_dec(v_stx_155_);
v_a_186_ = lean_ctor_get(v___x_168_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v___x_168_, 0);
lean_dec(v_unused_195_);
v___x_188_ = v___x_168_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_168_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_val_190_; lean_object* v___x_192_; 
v_val_190_ = lean_ctor_get(v_fst_170_, 0);
lean_inc(v_val_190_);
lean_dec_ref_known(v_fst_170_, 1);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v_val_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_val_190_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_a_186_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_stx_155_);
v_a_196_ = lean_ctor_get(v___x_168_, 0);
v_a_197_ = lean_ctor_get(v___x_168_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_168_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_inc(v_a_196_);
lean_dec(v___x_168_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_196_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInterpolatedStr___boxed(lean_object* v_stx_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Fmt_fmtInterpolatedStr(v_stx_205_, v_a_206_, v_a_207_);
lean_dec_ref(v_a_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0(lean_object* v_upperBound_209_, lean_object* v_stx_210_, lean_object* v_args_211_, lean_object* v___x_212_, lean_object* v_inst_213_, lean_object* v_R_214_, lean_object* v_a_215_, lean_object* v_b_216_, lean_object* v_c_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___redArg(v_upperBound_209_, v_stx_210_, v_args_211_, v___x_212_, v_a_215_, v_b_216_, v___y_218_, v___y_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0___boxed(lean_object* v_upperBound_221_, lean_object* v_stx_222_, lean_object* v_args_223_, lean_object* v___x_224_, lean_object* v_inst_225_, lean_object* v_R_226_, lean_object* v_a_227_, lean_object* v_b_228_, lean_object* v_c_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtInterpolatedStr_spec__0(v_upperBound_221_, v_stx_222_, v_args_223_, v___x_224_, v_inst_225_, v_R_226_, v_a_227_, v_b_228_, v_c_229_, v___y_230_, v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___x_224_);
lean_dec_ref(v_args_223_);
lean_dec(v_upperBound_221_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1(){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_244_ = l_Lean_Fmt_fmtAttribute;
v___x_245_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__1));
v___x_246_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___closed__5));
v___x_247_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInterpolatedStr___boxed), 3, 0);
v___x_248_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_244_, v___x_245_, v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1___boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1();
return v_res_250_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation_0__Lean_Fmt_fmtInterpolatedStr___regBuiltin_Lean_Fmt_fmtInterpolatedStr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_StrInterpolation(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_StrInterpolation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_StrInterpolation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_StrInterpolation(builtin);
}
#ifdef __cplusplus
}
#endif
