// Lean compiler output
// Module: Lean.Elab.Do.ForwardSyntax
// Imports: public import Lean.Parser.Term import Lean.Elab.Term.TermElabM meta import Lean.Parser.Do
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_Term_dropParens(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__6 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForward"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__7 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(207, 164, 175, 48, 233, 61, 15, 76)}};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__9 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__11 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12_value;
static const lean_array_object l_Lean_Elab_Do_Forward_matchApp_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f___closed__13 = (const lean_object*)&l_Lean_Elab_Do_Forward_matchApp_x3f___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f(lean_object* v_e_33_){
_start:
{
lean_object* v___y_35_; lean_object* v___y_36_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_39_ = l_Lean_Parser_Term_dropParens(v_e_33_);
v___x_40_ = ((lean_object*)(l_Lean_Elab_Do_Forward_matchApp_x3f___closed__4));
lean_inc(v___x_39_);
v___x_41_ = l_Lean_Syntax_isOfKind(v___x_39_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v_args_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = l_Lean_Syntax_getArg(v___x_39_, v___x_43_);
v_args_45_ = l_Lean_Syntax_getArgs(v___x_44_);
lean_dec(v___x_44_);
v___x_46_ = lean_array_get_size(v_args_45_);
v___x_47_ = lean_nat_sub(v___x_46_, v___x_43_);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v___x_46_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec(v___x_47_);
lean_dec_ref(v_args_45_);
lean_dec(v___x_39_);
v___x_49_ = lean_box(0);
return v___x_49_;
}
else
{
lean_object* v___x_50_; lean_object* v_head_51_; lean_object* v_arg_53_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v_head_51_ = l_Lean_Syntax_getArg(v___x_39_, v___x_50_);
lean_dec(v___x_39_);
v___x_65_ = lean_array_fget(v_args_45_, v___x_47_);
lean_dec(v___x_47_);
v___x_66_ = l_Lean_Parser_Term_dropParens(v___x_65_);
v___x_67_ = ((lean_object*)(l_Lean_Elab_Do_Forward_matchApp_x3f___closed__8));
lean_inc(v___x_66_);
v___x_68_ = l_Lean_Syntax_isOfKind(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_Do_Forward_matchApp_x3f___closed__10));
lean_inc(v___x_66_);
v___x_70_ = l_Lean_Syntax_isOfKind(v___x_66_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v___x_66_);
lean_dec(v_head_51_);
lean_dec_ref(v_args_45_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = l_Lean_Syntax_getArg(v___x_66_, v___x_43_);
lean_dec(v___x_66_);
v___x_73_ = ((lean_object*)(l_Lean_Elab_Do_Forward_matchApp_x3f___closed__12));
lean_inc(v___x_72_);
v___x_74_ = l_Lean_Syntax_isOfKind(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec(v___x_72_);
lean_dec(v_head_51_);
lean_dec_ref(v_args_45_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = l_Lean_Syntax_getArg(v___x_72_, v___x_43_);
v___x_77_ = l_Lean_Syntax_matchesNull(v___x_76_, v___x_50_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
lean_dec(v___x_72_);
lean_dec(v_head_51_);
lean_dec_ref(v_args_45_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_79_ = lean_unsigned_to_nat(3u);
v___x_80_ = l_Lean_Syntax_getArg(v___x_72_, v___x_79_);
v___x_81_ = l_Lean_Parser_Term_dropParens(v___x_80_);
lean_inc(v___x_81_);
v___x_82_ = l_Lean_Syntax_isOfKind(v___x_81_, v___x_67_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec(v___x_81_);
lean_dec(v___x_72_);
lean_dec(v_head_51_);
lean_dec_ref(v_args_45_);
v___x_83_ = lean_box(0);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = l_Lean_Syntax_getArg(v___x_72_, v___x_50_);
lean_dec(v___x_72_);
v___x_85_ = lean_unsigned_to_nat(2u);
v___x_86_ = l_Lean_Syntax_getArgs(v___x_84_);
lean_dec(v___x_84_);
v___x_87_ = l_Lean_Syntax_getArg(v___x_81_, v___x_85_);
lean_dec(v___x_81_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v_arg_53_ = v___x_88_;
goto v___jp_52_;
}
}
}
}
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = ((lean_object*)(l_Lean_Elab_Do_Forward_matchApp_x3f___closed__13));
v___x_90_ = lean_unsigned_to_nat(2u);
v___x_91_ = l_Lean_Syntax_getArg(v___x_66_, v___x_90_);
lean_dec(v___x_66_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_89_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v_arg_53_ = v___x_92_;
goto v___jp_52_;
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_54_ = lean_array_pop(v_args_45_);
v___x_55_ = lean_array_get_size(v___x_54_);
v___x_56_ = lean_nat_dec_eq(v___x_55_, v___x_50_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_57_ = ((lean_object*)(l_Lean_Elab_Do_Forward_matchApp_x3f___closed__6));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_54_);
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = lean_mk_empty_array_with_capacity(v___x_60_);
v___x_62_ = lean_array_push(v___x_61_, v_head_51_);
v___x_63_ = lean_array_push(v___x_62_, v___x_59_);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_58_);
lean_ctor_set(v___x_64_, 1, v___x_40_);
lean_ctor_set(v___x_64_, 2, v___x_63_);
v___y_35_ = v_arg_53_;
v___y_36_ = v___x_64_;
goto v___jp_34_;
}
else
{
lean_dec_ref(v___x_54_);
v___y_35_ = v_arg_53_;
v___y_36_ = v_head_51_;
goto v___jp_34_;
}
}
}
}
v___jp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___y_36_);
lean_ctor_set(v___x_37_, 1, v___y_35_);
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_ForwardSyntax(builtin);
}
#ifdef __cplusplus
}
#endif
