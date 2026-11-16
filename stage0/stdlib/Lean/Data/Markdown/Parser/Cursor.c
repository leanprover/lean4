// Lean compiler output
// Module: Lean.Data.Markdown.Parser.Cursor
// Imports: public import Init.While public import Lean.Data.Markdown.Block
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_Cursor_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_Cursor_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_toEol___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_toEol(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_toEol___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_front_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_front_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_advanceWhile___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_advanceWhile___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_Cursor_advanceWhile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__0 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__0_value;
static const lean_closure_object l_Lean_Markdown_Cursor_advanceWhile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__1 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__1_value;
static const lean_closure_object l_Lean_Markdown_Cursor_advanceWhile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__2 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__2_value;
static const lean_closure_object l_Lean_Markdown_Cursor_advanceWhile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__3 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__3_value;
static const lean_closure_object l_Lean_Markdown_Cursor_advanceWhile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__4 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__4_value;
static const lean_closure_object l_Lean_Markdown_Cursor_advanceWhile___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__5 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__5_value;
static const lean_closure_object l_Lean_Markdown_Cursor_advanceWhile___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__6 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__6_value;
static const lean_ctor_object l_Lean_Markdown_Cursor_advanceWhile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__0_value),((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__1_value)}};
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__7 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__7_value;
static const lean_ctor_object l_Lean_Markdown_Cursor_advanceWhile___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__7_value),((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__2_value),((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__3_value),((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__4_value),((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__5_value)}};
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__8 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__8_value;
static const lean_ctor_object l_Lean_Markdown_Cursor_advanceWhile___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__8_value),((lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__6_value)}};
static const lean_object* l_Lean_Markdown_Cursor_advanceWhile___closed__9 = (const lean_object*)&l_Lean_Markdown_Cursor_advanceWhile___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_advanceWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_Cursor_isBlank(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_isBlank___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_verbatimLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_verbatimLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine___redArg(lean_object* v_line_1_){
_start:
{
lean_object* v_startInclusive_2_; lean_object* v_endExclusive_3_; lean_object* v___x_4_; uint8_t v___x_5_; lean_object* v___x_6_; 
v_startInclusive_2_ = lean_ctor_get(v_line_1_, 0);
v_endExclusive_3_ = lean_ctor_get(v_line_1_, 1);
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = 0;
lean_inc(v_endExclusive_3_);
lean_inc(v_startInclusive_2_);
v___x_6_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6_, 0, v_startInclusive_2_);
lean_ctor_set(v___x_6_, 1, v_endExclusive_3_);
lean_ctor_set(v___x_6_, 2, v___x_4_);
lean_ctor_set_uint8(v___x_6_, sizeof(void*)*3, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine___redArg___boxed(lean_object* v_line_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Markdown_Cursor_ofLine___redArg(v_line_7_);
lean_dec_ref(v_line_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine(lean_object* v_s_9_, lean_object* v_line_10_){
_start:
{
lean_object* v_startInclusive_11_; lean_object* v_endExclusive_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; 
v_startInclusive_11_ = lean_ctor_get(v_line_10_, 0);
v_endExclusive_12_ = lean_ctor_get(v_line_10_, 1);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = 0;
lean_inc(v_endExclusive_12_);
lean_inc(v_startInclusive_11_);
v___x_15_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_15_, 0, v_startInclusive_11_);
lean_ctor_set(v___x_15_, 1, v_endExclusive_12_);
lean_ctor_set(v___x_15_, 2, v___x_13_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*3, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_ofLine___boxed(lean_object* v_s_16_, lean_object* v_line_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Markdown_Cursor_ofLine(v_s_16_, v_line_17_);
lean_dec_ref(v_line_17_);
lean_dec_ref(v_s_16_);
return v_res_18_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_Cursor_isEmpty___redArg(lean_object* v_c_19_){
_start:
{
lean_object* v_pos_20_; lean_object* v_stop_21_; uint8_t v___x_22_; 
v_pos_20_ = lean_ctor_get(v_c_19_, 0);
v_stop_21_ = lean_ctor_get(v_c_19_, 1);
v___x_22_ = lean_nat_dec_le(v_stop_21_, v_pos_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_isEmpty___redArg___boxed(lean_object* v_c_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_Markdown_Cursor_isEmpty___redArg(v_c_23_);
lean_dec_ref(v_c_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_Cursor_isEmpty(lean_object* v_s_26_, lean_object* v_c_27_){
_start:
{
lean_object* v_pos_28_; lean_object* v_stop_29_; uint8_t v___x_30_; 
v_pos_28_ = lean_ctor_get(v_c_27_, 0);
v_stop_29_ = lean_ctor_get(v_c_27_, 1);
v___x_30_ = lean_nat_dec_le(v_stop_29_, v_pos_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_isEmpty___boxed(lean_object* v_s_31_, lean_object* v_c_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Markdown_Cursor_isEmpty(v_s_31_, v_c_32_);
lean_dec_ref(v_c_32_);
lean_dec_ref(v_s_31_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_toEol___redArg(lean_object* v_c_35_){
_start:
{
lean_object* v_pos_36_; lean_object* v_stop_37_; lean_object* v___x_38_; 
v_pos_36_ = lean_ctor_get(v_c_35_, 0);
lean_inc(v_pos_36_);
v_stop_37_ = lean_ctor_get(v_c_35_, 1);
lean_inc(v_stop_37_);
lean_dec_ref(v_c_35_);
v___x_38_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_36_, v_stop_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_toEol(lean_object* v_s_39_, lean_object* v_c_40_){
_start:
{
lean_object* v_pos_41_; lean_object* v_stop_42_; lean_object* v___x_43_; 
v_pos_41_ = lean_ctor_get(v_c_40_, 0);
lean_inc(v_pos_41_);
v_stop_42_ = lean_ctor_get(v_c_40_, 1);
lean_inc(v_stop_42_);
lean_dec_ref(v_c_40_);
v___x_43_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_41_, v_stop_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_toEol___boxed(lean_object* v_s_44_, lean_object* v_c_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Markdown_Cursor_toEol(v_s_44_, v_c_45_);
lean_dec_ref(v_s_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab___redArg(lean_object* v_c_47_, lean_object* v_cols_48_){
_start:
{
lean_object* v_pos_49_; lean_object* v_stop_50_; lean_object* v_col_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_60_; 
v_pos_49_ = lean_ctor_get(v_c_47_, 0);
v_stop_50_ = lean_ctor_get(v_c_47_, 1);
v_col_51_ = lean_ctor_get(v_c_47_, 2);
v_isSharedCheck_60_ = !lean_is_exclusive(v_c_47_);
if (v_isSharedCheck_60_ == 0)
{
v___x_53_ = v_c_47_;
v_isShared_54_ = v_isSharedCheck_60_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_col_51_);
lean_inc(v_stop_50_);
lean_inc(v_pos_49_);
lean_dec(v_c_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_60_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_58_; 
v___x_55_ = lean_nat_add(v_col_51_, v_cols_48_);
lean_dec(v_col_51_);
v___x_56_ = 1;
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 2, v___x_55_);
v___x_58_ = v___x_53_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_pos_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_stop_50_);
lean_ctor_set(v_reuseFailAlloc_59_, 2, v___x_55_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*3, v___x_56_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab___redArg___boxed(lean_object* v_c_61_, lean_object* v_cols_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Markdown_Cursor_intoTab___redArg(v_c_61_, v_cols_62_);
lean_dec(v_cols_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab(lean_object* v_s_64_, lean_object* v_c_65_, lean_object* v_cols_66_){
_start:
{
lean_object* v_pos_67_; lean_object* v_stop_68_; lean_object* v_col_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_78_; 
v_pos_67_ = lean_ctor_get(v_c_65_, 0);
v_stop_68_ = lean_ctor_get(v_c_65_, 1);
v_col_69_ = lean_ctor_get(v_c_65_, 2);
v_isSharedCheck_78_ = !lean_is_exclusive(v_c_65_);
if (v_isSharedCheck_78_ == 0)
{
v___x_71_ = v_c_65_;
v_isShared_72_ = v_isSharedCheck_78_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_col_69_);
lean_inc(v_stop_68_);
lean_inc(v_pos_67_);
lean_dec(v_c_65_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_78_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_76_; 
v___x_73_ = lean_nat_add(v_col_69_, v_cols_66_);
lean_dec(v_col_69_);
v___x_74_ = 1;
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 2, v___x_73_);
v___x_76_ = v___x_71_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_pos_67_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_stop_68_);
lean_ctor_set(v_reuseFailAlloc_77_, 2, v___x_73_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*3, v___x_74_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_intoTab___boxed(lean_object* v_s_79_, lean_object* v_c_80_, lean_object* v_cols_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Markdown_Cursor_intoTab(v_s_79_, v_c_80_, v_cols_81_);
lean_dec(v_cols_81_);
lean_dec_ref(v_s_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_front_x3f(lean_object* v_s_83_, lean_object* v_c_84_){
_start:
{
lean_object* v_pos_85_; lean_object* v_stop_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_pos_85_ = lean_ctor_get(v_c_84_, 0);
v_stop_86_ = lean_ctor_get(v_c_84_, 1);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_pos_85_, v___x_87_);
v___x_89_ = lean_nat_dec_le(v___x_88_, v_stop_86_);
lean_dec(v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = l_String_Slice_Pos_get_x3f(v_s_83_, v_pos_85_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_front_x3f___boxed(lean_object* v_s_92_, lean_object* v_c_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Markdown_Cursor_front_x3f(v_s_92_, v_c_93_);
lean_dec_ref(v_c_93_);
lean_dec_ref(v_s_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_next(lean_object* v_s_95_, lean_object* v_c_96_){
_start:
{
lean_object* v_pos_97_; lean_object* v_stop_98_; lean_object* v_col_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_pos_97_ = lean_ctor_get(v_c_96_, 0);
v_stop_98_ = lean_ctor_get(v_c_96_, 1);
v_col_99_ = lean_ctor_get(v_c_96_, 2);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_pos_97_, v___x_100_);
v___x_102_ = lean_nat_dec_le(v___x_101_, v_stop_98_);
lean_dec(v___x_101_);
if (v___x_102_ == 0)
{
return v_c_96_;
}
else
{
lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_col_99_);
lean_inc(v_stop_98_);
lean_inc(v_pos_97_);
v_isSharedCheck_116_ = !lean_is_exclusive(v_c_96_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; lean_object* v_unused_118_; lean_object* v_unused_119_; 
v_unused_117_ = lean_ctor_get(v_c_96_, 2);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_c_96_, 1);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_c_96_, 0);
lean_dec(v_unused_119_);
v___x_104_ = v_c_96_;
v_isShared_105_ = v_isSharedCheck_116_;
goto v_resetjp_103_;
}
else
{
lean_dec(v_c_96_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_116_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_str_106_; lean_object* v_startInclusive_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_114_; 
v_str_106_ = lean_ctor_get(v_s_95_, 0);
v_startInclusive_107_ = lean_ctor_get(v_s_95_, 1);
v___x_108_ = lean_nat_add(v_startInclusive_107_, v_pos_97_);
lean_dec(v_pos_97_);
v___x_109_ = lean_string_utf8_next_fast(v_str_106_, v___x_108_);
lean_dec(v___x_108_);
v___x_110_ = lean_nat_sub(v___x_109_, v_startInclusive_107_);
v___x_111_ = lean_nat_add(v_col_99_, v___x_100_);
lean_dec(v_col_99_);
v___x_112_ = 0;
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 2, v___x_111_);
lean_ctor_set(v___x_104_, 0, v___x_110_);
v___x_114_ = v___x_104_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_stop_98_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v___x_111_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*3, v___x_112_);
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_next___boxed(lean_object* v_s_120_, lean_object* v_c_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Markdown_Cursor_next(v_s_120_, v_c_121_);
lean_dec_ref(v_s_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_advanceWhile___lam__0(lean_object* v_s_123_, lean_object* v_pred_124_, lean_object* v_b_125_){
_start:
{
lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_171_; 
v_fst_126_ = lean_ctor_get(v_b_125_, 0);
v_snd_127_ = lean_ctor_get(v_b_125_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_b_125_);
if (v_isSharedCheck_171_ == 0)
{
v___x_129_ = v_b_125_;
v_isShared_130_ = v_isSharedCheck_171_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_126_);
lean_dec(v_b_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_171_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_pos_131_; lean_object* v_stop_132_; lean_object* v_col_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_pos_131_ = lean_ctor_get(v_fst_126_, 0);
v_stop_132_ = lean_ctor_get(v_fst_126_, 1);
v_col_133_ = lean_ctor_get(v_fst_126_, 2);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_pos_131_, v___x_134_);
v___x_136_ = lean_nat_dec_le(v___x_135_, v_stop_132_);
lean_dec(v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_138_; 
lean_dec_ref(v_pred_124_);
if (v_isShared_130_ == 0)
{
v___x_138_ = v___x_129_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_fst_126_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_snd_127_);
v___x_138_ = v_reuseFailAlloc_140_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
else
{
lean_object* v_str_141_; lean_object* v_startInclusive_142_; lean_object* v___x_143_; uint32_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_str_141_ = lean_ctor_get(v_s_123_, 0);
v_startInclusive_142_ = lean_ctor_get(v_s_123_, 1);
v___x_143_ = lean_nat_add(v_startInclusive_142_, v_pos_131_);
v___x_144_ = lean_string_utf8_get_fast(v_str_141_, v___x_143_);
v___x_145_ = lean_box_uint32(v___x_144_);
v___x_146_ = lean_apply_1(v_pred_124_, v___x_145_);
v___x_147_ = lean_unbox(v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_149_; 
lean_dec(v___x_143_);
if (v_isShared_130_ == 0)
{
v___x_149_ = v___x_129_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_fst_126_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_snd_127_);
v___x_149_ = v_reuseFailAlloc_151_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
else
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_167_; 
lean_inc(v_col_133_);
lean_inc(v_stop_132_);
v_isSharedCheck_167_ = !lean_is_exclusive(v_fst_126_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; lean_object* v_unused_169_; lean_object* v_unused_170_; 
v_unused_168_ = lean_ctor_get(v_fst_126_, 2);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_fst_126_, 1);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_fst_126_, 0);
lean_dec(v_unused_170_);
v___x_153_ = v_fst_126_;
v_isShared_154_ = v_isSharedCheck_167_;
goto v_resetjp_152_;
}
else
{
lean_dec(v_fst_126_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_167_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_155_ = 0;
v___x_156_ = lean_nat_add(v_snd_127_, v___x_134_);
lean_dec(v_snd_127_);
v___x_157_ = lean_string_utf8_next_fast(v_str_141_, v___x_143_);
lean_dec(v___x_143_);
v___x_158_ = lean_nat_sub(v___x_157_, v_startInclusive_142_);
v___x_159_ = lean_nat_add(v_col_133_, v___x_134_);
lean_dec(v_col_133_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 2, v___x_159_);
lean_ctor_set(v___x_153_, 0, v___x_158_);
v___x_161_ = v___x_153_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_stop_132_);
lean_ctor_set(v_reuseFailAlloc_166_, 2, v___x_159_);
v___x_161_ = v_reuseFailAlloc_166_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_163_; 
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*3, v___x_155_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_156_);
lean_ctor_set(v___x_129_, 0, v___x_161_);
v___x_163_ = v___x_129_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_156_);
v___x_163_ = v_reuseFailAlloc_165_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_advanceWhile___lam__0___boxed(lean_object* v_s_172_, lean_object* v_pred_173_, lean_object* v_b_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Markdown_Cursor_advanceWhile___lam__0(v_s_172_, v_pred_173_, v_b_174_);
lean_dec_ref(v_s_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_advanceWhile(lean_object* v_s_195_, lean_object* v_c_196_, lean_object* v_pred_197_){
_start:
{
lean_object* v___f_198_; lean_object* v___x_199_; lean_object* v_count_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_fst_203_; lean_object* v_snd_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v___f_198_ = lean_alloc_closure((void*)(l_Lean_Markdown_Cursor_advanceWhile___lam__0___boxed), 3, 2);
lean_closure_set(v___f_198_, 0, v_s_195_);
lean_closure_set(v___f_198_, 1, v_pred_197_);
v___x_199_ = ((lean_object*)(l_Lean_Markdown_Cursor_advanceWhile___closed__9));
v_count_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v_c_196_);
lean_ctor_set(v___x_201_, 1, v_count_200_);
v___x_202_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_199_, v___f_198_, v___x_201_);
v_fst_203_ = lean_ctor_get(v___x_202_, 0);
v_snd_204_ = lean_ctor_get(v___x_202_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_202_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_snd_204_);
lean_inc(v_fst_203_);
lean_dec(v___x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_fst_203_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_snd_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___redArg(lean_object* v_s_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_248_; 
v_fst_214_ = lean_ctor_get(v_a_213_, 0);
v_snd_215_ = lean_ctor_get(v_a_213_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_248_ == 0)
{
v___x_217_ = v_a_213_;
v_isShared_218_ = v_isSharedCheck_248_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
lean_dec(v_a_213_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_248_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_pos_219_; lean_object* v_stop_220_; lean_object* v_col_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_pos_219_ = lean_ctor_get(v_fst_214_, 0);
v_stop_220_ = lean_ctor_get(v_fst_214_, 1);
v_col_221_ = lean_ctor_get(v_fst_214_, 2);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_pos_219_, v___x_222_);
v___x_224_ = lean_nat_dec_le(v___x_223_, v_stop_220_);
lean_dec(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_226_; 
if (v_isShared_218_ == 0)
{
v___x_226_ = v___x_217_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_fst_214_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_snd_215_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
else
{
lean_object* v_str_228_; lean_object* v_startInclusive_229_; lean_object* v___x_230_; uint32_t v___x_242_; uint32_t v___x_243_; uint8_t v___x_244_; 
v_str_228_ = lean_ctor_get(v_s_212_, 0);
v_startInclusive_229_ = lean_ctor_get(v_s_212_, 1);
v___x_230_ = lean_nat_add(v_startInclusive_229_, v_pos_219_);
v___x_242_ = lean_string_utf8_get_fast(v_str_228_, v___x_230_);
v___x_243_ = 32;
v___x_244_ = lean_uint32_dec_eq(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = 9;
v___x_246_ = lean_uint32_dec_eq(v___x_242_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
lean_dec(v___x_230_);
lean_del_object(v___x_217_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_fst_214_);
lean_ctor_set(v___x_247_, 1, v_snd_215_);
return v___x_247_;
}
else
{
lean_inc(v_col_221_);
lean_inc(v_stop_220_);
lean_dec(v_fst_214_);
goto v___jp_231_;
}
}
else
{
lean_inc(v_col_221_);
lean_inc(v_stop_220_);
lean_dec(v_fst_214_);
goto v___jp_231_;
}
v___jp_231_:
{
uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_232_ = 0;
v___x_233_ = lean_nat_add(v_snd_215_, v___x_222_);
lean_dec(v_snd_215_);
v___x_234_ = lean_string_utf8_next_fast(v_str_228_, v___x_230_);
lean_dec(v___x_230_);
v___x_235_ = lean_nat_sub(v___x_234_, v_startInclusive_229_);
v___x_236_ = lean_nat_add(v_col_221_, v___x_222_);
lean_dec(v_col_221_);
v___x_237_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v_stop_220_);
lean_ctor_set(v___x_237_, 2, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*3, v___x_232_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_233_);
lean_ctor_set(v___x_217_, 0, v___x_237_);
v___x_239_ = v___x_217_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_233_);
v___x_239_ = v_reuseFailAlloc_241_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v_a_213_ = v___x_239_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___redArg___boxed(lean_object* v_s_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___redArg(v_s_249_, v_a_250_);
lean_dec_ref(v_s_249_);
return v_res_251_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_Cursor_isBlank(lean_object* v_s_252_, lean_object* v_c_253_){
_start:
{
lean_object* v_count_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_fst_257_; lean_object* v_pos_258_; lean_object* v_stop_259_; uint8_t v___x_260_; 
v_count_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_c_253_);
lean_ctor_set(v___x_255_, 1, v_count_254_);
v___x_256_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___redArg(v_s_252_, v___x_255_);
v_fst_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_fst_257_);
lean_dec_ref(v___x_256_);
v_pos_258_ = lean_ctor_get(v_fst_257_, 0);
lean_inc(v_pos_258_);
v_stop_259_ = lean_ctor_get(v_fst_257_, 1);
lean_inc(v_stop_259_);
lean_dec(v_fst_257_);
v___x_260_ = lean_nat_dec_le(v_stop_259_, v_pos_258_);
lean_dec(v_pos_258_);
lean_dec(v_stop_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_isBlank___boxed(lean_object* v_s_261_, lean_object* v_c_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Lean_Markdown_Cursor_isBlank(v_s_261_, v_c_262_);
lean_dec_ref(v_s_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0(lean_object* v_s_265_, lean_object* v_inst_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___redArg(v_s_265_, v_a_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0___boxed(lean_object* v_s_269_, lean_object* v_inst_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_Cursor_isBlank_spec__0(v_s_269_, v_inst_270_, v_a_271_);
lean_dec_ref(v_s_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_verbatimLine(lean_object* v_s_273_, lean_object* v_c_274_){
_start:
{
lean_object* v_pos_275_; lean_object* v_stop_276_; lean_object* v_col_277_; uint8_t v_partialTab_278_; lean_object* v_pos_280_; 
v_pos_275_ = lean_ctor_get(v_c_274_, 0);
lean_inc(v_pos_275_);
v_stop_276_ = lean_ctor_get(v_c_274_, 1);
lean_inc(v_stop_276_);
v_col_277_ = lean_ctor_get(v_c_274_, 2);
lean_inc(v_col_277_);
v_partialTab_278_ = lean_ctor_get_uint8(v_c_274_, sizeof(void*)*3);
lean_dec_ref(v_c_274_);
if (v_partialTab_278_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_col_277_);
v___x_286_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_275_, v_stop_276_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_pos_275_, v___x_289_);
v___x_291_ = lean_nat_dec_le(v___x_290_, v_stop_276_);
lean_dec(v___x_290_);
if (v___x_291_ == 0)
{
v_pos_280_ = v_pos_275_;
goto v___jp_279_;
}
else
{
lean_object* v_str_292_; lean_object* v_startInclusive_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_str_292_ = lean_ctor_get(v_s_273_, 0);
v_startInclusive_293_ = lean_ctor_get(v_s_273_, 1);
v___x_294_ = lean_nat_add(v_startInclusive_293_, v_pos_275_);
lean_dec(v_pos_275_);
v___x_295_ = lean_string_utf8_next_fast(v_str_292_, v___x_294_);
lean_dec(v___x_294_);
v___x_296_ = lean_nat_sub(v___x_295_, v_startInclusive_293_);
v_pos_280_ = v___x_296_;
goto v___jp_279_;
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_281_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_280_, v_stop_276_);
v___x_282_ = lean_unsigned_to_nat(4u);
v___x_283_ = lean_nat_mod(v_col_277_, v___x_282_);
lean_dec(v_col_277_);
v___x_284_ = lean_nat_sub(v___x_282_, v___x_283_);
lean_dec(v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_281_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Cursor_verbatimLine___boxed(lean_object* v_s_297_, lean_object* v_c_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_297_, v_c_298_);
lean_dec_ref(v_s_297_);
return v_res_299_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Block(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Cursor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_Cursor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Block(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_Cursor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Cursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_Cursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_Cursor(builtin);
}
#ifdef __cplusplus
}
#endif
