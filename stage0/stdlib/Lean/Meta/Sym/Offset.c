// Lean compiler output
// Module: Lean.Meta.Sym.Offset
// Imports: public import Lean.Meta.Sym.LitValues
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedOffset_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedOffset = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_isOffset_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_isOffset_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_isOffset_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Sym_isOffset_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_isOffset_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_isOffset_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_isOffset_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Sym_isOffset_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_isOffset_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_isOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_isOffset___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_isOffset___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_isOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_isOffset___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_isOffset___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_isOffset___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Sym_isOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isOffset___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isOffset___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Sym_isOffset___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_isOffset___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Sym_Offset_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_k_8_; lean_object* v___x_9_; 
v_k_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_k_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_k_8_);
return v___x_9_;
}
else
{
lean_object* v_e_10_; lean_object* v_k_11_; lean_object* v___x_12_; 
v_e_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_e_10_);
v_k_11_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_k_11_);
lean_dec_ref(v_t_6_);
v___x_12_ = lean_apply_2(v_k_7_, v_e_10_, v_k_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Sym_Offset_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim___redArg(lean_object* v_t_25_, lean_object* v_num_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_25_, v_num_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_num_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_29_, v_num_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim___redArg(lean_object* v_t_33_, lean_object* v_add_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_33_, v_add_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_add_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_37_, v_add_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc(lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v_k_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_55_; 
v_k_47_ = lean_ctor_get(v_x_45_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_55_ == 0)
{
v___x_49_ = v_x_45_;
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_k_47_);
lean_dec(v_x_45_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_51_ = lean_nat_add(v_k_47_, v_x_46_);
lean_dec(v_k_47_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_51_);
v___x_53_ = v___x_49_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
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
lean_object* v_e_56_; lean_object* v_k_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_65_; 
v_e_56_ = lean_ctor_get(v_x_45_, 0);
v_k_57_ = lean_ctor_get(v_x_45_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_65_ == 0)
{
v___x_59_ = v_x_45_;
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_k_57_);
lean_inc(v_e_56_);
lean_dec(v_x_45_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_61_ = lean_nat_add(v_k_57_, v_x_46_);
lean_dec(v_k_57_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_61_);
v___x_63_ = v___x_59_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_e_56_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc___boxed(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_Sym_Offset_inc(v_x_66_, v_x_67_);
lean_dec(v_x_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f(lean_object* v_e_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = l_Lean_Expr_cleanupAnnotations(v_e_81_);
v___x_83_ = l_Lean_Expr_isApp(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v___x_82_);
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v_arg_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_arg_85_ = lean_ctor_get(v___x_82_, 1);
lean_inc_ref(v_arg_85_);
v___x_86_ = l_Lean_Expr_appFnCleanup___redArg(v___x_82_);
v___x_87_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__2));
v___x_88_ = l_Lean_Expr_isConstOf(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
uint8_t v___x_89_; 
v___x_89_ = l_Lean_Expr_isApp(v___x_86_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec_ref(v___x_86_);
lean_dec_ref(v_arg_85_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v_arg_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v_arg_91_ = lean_ctor_get(v___x_86_, 1);
lean_inc_ref(v_arg_91_);
v___x_92_ = l_Lean_Expr_appFnCleanup___redArg(v___x_86_);
v___x_93_ = l_Lean_Expr_isApp(v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v___x_92_);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_85_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = l_Lean_Expr_appFnCleanup___redArg(v___x_92_);
v___x_96_ = l_Lean_Expr_isApp(v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_95_);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_85_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = l_Lean_Expr_appFnCleanup___redArg(v___x_95_);
v___x_99_ = l_Lean_Expr_isApp(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v___x_98_);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_85_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_98_);
v___x_102_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v___x_101_);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_85_);
v___x_103_ = lean_box(0);
return v___x_103_;
}
else
{
lean_object* v_arg_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_arg_104_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_104_);
v___x_105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_106_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__5));
v___x_107_ = l_Lean_Expr_isConstOf(v___x_105_, v___x_106_);
lean_dec_ref(v___x_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec_ref(v_arg_104_);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_85_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__6));
v___x_110_ = l_Lean_Expr_isConstOf(v_arg_104_, v___x_109_);
lean_dec_ref(v_arg_104_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_85_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_85_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_113_; 
lean_dec_ref(v_arg_91_);
v___x_113_ = lean_box(0);
return v___x_113_;
}
else
{
lean_object* v_val_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_123_; 
v_val_114_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_123_ == 0)
{
v___x_116_ = v___x_112_;
v_isShared_117_ = v_isSharedCheck_123_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_val_114_);
lean_dec(v___x_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_123_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_118_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(v_arg_91_);
v___x_119_ = l_Lean_Meta_Sym_Offset_inc(v___x_118_, v_val_114_);
lean_dec(v_val_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_119_);
v___x_121_ = v___x_116_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref(v___x_86_);
v___x_124_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(v_arg_85_);
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = l_Lean_Meta_Sym_Offset_inc(v___x_124_, v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(lean_object* v_e_128_){
_start:
{
lean_object* v___x_129_; 
lean_inc_ref(v_e_128_);
v___x_129_ = l_Lean_Meta_Sym_isOffset_x3f(v_e_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v_e_128_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v_val_132_; 
lean_dec_ref(v_e_128_);
v_val_132_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_val_132_);
lean_dec_ref(v___x_129_);
return v_val_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27(lean_object* v_declName_133_, lean_object* v_p_134_){
_start:
{
uint8_t v___y_136_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__2));
v___x_140_ = lean_name_eq(v_declName_133_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__5));
v___x_142_ = lean_name_eq(v_declName_133_, v___x_141_);
v___y_136_ = v___x_142_;
goto v___jp_135_;
}
else
{
v___y_136_ = v___x_140_;
goto v___jp_135_;
}
v___jp_135_:
{
if (v___y_136_ == 0)
{
lean_object* v___x_137_; 
lean_dec_ref(v_p_134_);
v___x_137_ = lean_box(0);
return v___x_137_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Sym_isOffset_x3f(v_p_134_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(lean_object* v_declName_143_, lean_object* v_p_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Sym_isOffset_x3f_x27(v_declName_143_, v_p_144_);
lean_dec(v_declName_143_);
return v_res_145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset(lean_object* v_e_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = l_Lean_Expr_cleanupAnnotations(v_e_151_);
v___x_153_ = l_Lean_Expr_isApp(v___x_152_);
if (v___x_153_ == 0)
{
lean_dec_ref(v___x_152_);
return v___x_153_;
}
else
{
lean_object* v_arg_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_arg_154_ = lean_ctor_get(v___x_152_, 1);
lean_inc_ref(v_arg_154_);
v___x_155_ = l_Lean_Expr_appFnCleanup___redArg(v___x_152_);
v___x_156_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__2));
v___x_157_ = l_Lean_Expr_isConstOf(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
uint8_t v___x_158_; 
v___x_158_ = l_Lean_Expr_isApp(v___x_155_);
if (v___x_158_ == 0)
{
lean_dec_ref(v___x_155_);
lean_dec_ref(v_arg_154_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_155_);
v___x_160_ = l_Lean_Expr_isApp(v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v___x_159_);
lean_dec_ref(v_arg_154_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_159_);
v___x_162_ = l_Lean_Expr_isApp(v___x_161_);
if (v___x_162_ == 0)
{
lean_dec_ref(v___x_161_);
lean_dec_ref(v_arg_154_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = l_Lean_Expr_appFnCleanup___redArg(v___x_161_);
v___x_164_ = l_Lean_Expr_isApp(v___x_163_);
if (v___x_164_ == 0)
{
lean_dec_ref(v___x_163_);
lean_dec_ref(v_arg_154_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = l_Lean_Expr_appFnCleanup___redArg(v___x_163_);
v___x_166_ = l_Lean_Expr_isApp(v___x_165_);
if (v___x_166_ == 0)
{
lean_dec_ref(v___x_165_);
lean_dec_ref(v_arg_154_);
return v___x_166_;
}
else
{
lean_object* v_arg_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_arg_167_ = lean_ctor_get(v___x_165_, 1);
lean_inc_ref(v_arg_167_);
v___x_168_ = l_Lean_Expr_appFnCleanup___redArg(v___x_165_);
v___x_169_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__5));
v___x_170_ = l_Lean_Expr_isConstOf(v___x_168_, v___x_169_);
lean_dec_ref(v___x_168_);
if (v___x_170_ == 0)
{
lean_dec_ref(v_arg_167_);
lean_dec_ref(v_arg_154_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__6));
v___x_172_ = l_Lean_Expr_isConstOf(v_arg_167_, v___x_171_);
lean_dec_ref(v_arg_167_);
if (v___x_172_ == 0)
{
lean_dec_ref(v_arg_154_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = l_Lean_Expr_cleanupAnnotations(v_arg_154_);
v___x_174_ = l_Lean_Expr_isApp(v___x_173_);
if (v___x_174_ == 0)
{
lean_dec_ref(v___x_173_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = l_Lean_Expr_appFnCleanup___redArg(v___x_173_);
v___x_176_ = l_Lean_Expr_isApp(v___x_175_);
if (v___x_176_ == 0)
{
lean_dec_ref(v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_arg_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_arg_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc_ref(v_arg_177_);
v___x_178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_175_);
v___x_179_ = l_Lean_Expr_isApp(v___x_178_);
if (v___x_179_ == 0)
{
lean_dec_ref(v___x_178_);
lean_dec_ref(v_arg_177_);
return v___x_179_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_180_ = l_Lean_Expr_appFnCleanup___redArg(v___x_178_);
v___x_181_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset___closed__2));
v___x_182_ = l_Lean_Expr_isConstOf(v___x_180_, v___x_181_);
lean_dec_ref(v___x_180_);
if (v___x_182_ == 0)
{
lean_dec_ref(v_arg_177_);
return v___x_182_;
}
else
{
if (lean_obj_tag(v_arg_177_) == 9)
{
lean_object* v_a_183_; 
v_a_183_ = lean_ctor_get(v_arg_177_, 0);
lean_inc_ref(v_a_183_);
lean_dec_ref(v_arg_177_);
if (lean_obj_tag(v_a_183_) == 0)
{
lean_dec_ref(v_a_183_);
return v___x_172_;
}
else
{
lean_dec_ref(v_a_183_);
return v___x_157_;
}
}
else
{
lean_dec_ref(v_arg_177_);
return v___x_157_;
}
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_155_);
lean_dec_ref(v_arg_154_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset___boxed(lean_object* v_e_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Meta_Sym_isOffset(v_e_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object* v_declName_187_, lean_object* v_p_188_){
_start:
{
uint8_t v___y_190_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__2));
v___x_193_ = lean_name_eq(v_declName_187_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__5));
v___x_195_ = lean_name_eq(v_declName_187_, v___x_194_);
v___y_190_ = v___x_195_;
goto v___jp_189_;
}
else
{
v___y_190_ = v___x_193_;
goto v___jp_189_;
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
lean_dec_ref(v_p_188_);
return v___y_190_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = l_Lean_Meta_Sym_isOffset(v_p_188_);
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object* v_declName_196_, lean_object* v_p_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_196_, v_p_197_);
lean_dec(v_declName_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object* v_e_200_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
lean_inc_ref(v_e_200_);
v___x_207_ = l_Lean_Expr_cleanupAnnotations(v_e_200_);
v___x_208_ = l_Lean_Expr_isApp(v___x_207_);
if (v___x_208_ == 0)
{
lean_dec_ref(v___x_207_);
goto v___jp_201_;
}
else
{
lean_object* v_arg_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_arg_209_ = lean_ctor_get(v___x_207_, 1);
lean_inc_ref(v_arg_209_);
v___x_210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_207_);
v___x_211_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__2));
v___x_212_ = l_Lean_Expr_isConstOf(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
v___x_213_ = l_Lean_Expr_isApp(v___x_210_);
if (v___x_213_ == 0)
{
lean_dec_ref(v___x_210_);
lean_dec_ref(v_arg_209_);
goto v___jp_201_;
}
else
{
lean_object* v_arg_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_arg_214_ = lean_ctor_get(v___x_210_, 1);
lean_inc_ref(v_arg_214_);
v___x_215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_210_);
v___x_216_ = l_Lean_Expr_isApp(v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v___x_215_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_209_);
goto v___jp_201_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = l_Lean_Expr_appFnCleanup___redArg(v___x_215_);
v___x_218_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset___closed__2));
v___x_219_ = l_Lean_Expr_isConstOf(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
uint8_t v___x_220_; 
v___x_220_ = l_Lean_Expr_isApp(v___x_217_);
if (v___x_220_ == 0)
{
lean_dec_ref(v___x_217_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_209_);
goto v___jp_201_;
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_217_);
v___x_222_ = l_Lean_Expr_isApp(v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v___x_221_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_209_);
goto v___jp_201_;
}
else
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_221_);
v___x_224_ = l_Lean_Expr_isApp(v___x_223_);
if (v___x_224_ == 0)
{
lean_dec_ref(v___x_223_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_209_);
goto v___jp_201_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_223_);
v___x_226_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__5));
v___x_227_ = l_Lean_Expr_isConstOf(v___x_225_, v___x_226_);
lean_dec_ref(v___x_225_);
if (v___x_227_ == 0)
{
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_209_);
goto v___jp_201_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_209_);
if (lean_obj_tag(v___x_228_) == 1)
{
lean_object* v_val_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec_ref(v_e_200_);
v_val_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_229_);
lean_dec_ref(v___x_228_);
v___x_230_ = l_Lean_Meta_Sym_toOffset(v_arg_214_);
v___x_231_ = l_Lean_Meta_Sym_Offset_inc(v___x_230_, v_val_229_);
lean_dec(v_val_229_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v___x_228_);
lean_dec_ref(v_arg_214_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v_e_200_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_217_);
lean_dec_ref(v_arg_209_);
if (lean_obj_tag(v_arg_214_) == 9)
{
lean_object* v_a_234_; 
v_a_234_ = lean_ctor_get(v_arg_214_, 0);
lean_inc_ref(v_a_234_);
lean_dec_ref(v_arg_214_);
if (lean_obj_tag(v_a_234_) == 0)
{
lean_object* v_val_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_e_200_);
v_val_235_ = lean_ctor_get(v_a_234_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_a_234_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v_a_234_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_val_235_);
lean_dec(v_a_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_val_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_dec_ref(v_a_234_);
goto v___jp_204_;
}
}
else
{
lean_dec_ref(v_arg_214_);
goto v___jp_204_;
}
}
}
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v___x_210_);
lean_dec_ref(v_e_200_);
v___x_243_ = l_Lean_Meta_Sym_toOffset(v_arg_209_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = l_Lean_Meta_Sym_Offset_inc(v___x_243_, v___x_244_);
return v___x_245_;
}
}
v___jp_201_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v_e_200_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
return v___x_203_;
}
v___jp_204_:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v_e_200_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Offset(builtin);
}
#ifdef __cplusplus
}
#endif
