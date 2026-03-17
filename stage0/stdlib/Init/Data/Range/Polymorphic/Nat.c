// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Nat
// Imports: import Init.Data.Nat.Lemmas public import Init.Data.Range.Polymorphic.Instances import Init.Data.Nat.MinMax import Init.Omega import Init.RCases
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instUpwardEnumerableNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableNat___closed__0 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__0_value;
static const lean_closure_object l_Std_PRange_instUpwardEnumerableNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableNat___closed__1 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__1_value;
static const lean_ctor_object l_Std_PRange_instUpwardEnumerableNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__0_value),((lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__1_value)}};
static const lean_object* l_Std_PRange_instUpwardEnumerableNat___closed__2 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instUpwardEnumerableNat = (const lean_object*)&l_Std_PRange_instUpwardEnumerableNat___closed__2_value;
static const lean_ctor_object l_Std_PRange_instLeast_x3fNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_PRange_instLeast_x3fNat___closed__0 = (const lean_object*)&l_Std_PRange_instLeast_x3fNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instLeast_x3fNat = (const lean_object*)&l_Std_PRange_instLeast_x3fNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeNat___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeNat = (const lean_object*)&l_Std_PRange_instHasSizeNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeNat__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeNat__1___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeNat__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeNat__1 = (const lean_object*)&l_Std_PRange_instHasSizeNat__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat = (const lean_object*)&l_Std_instHasRcoIntersectionNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__1___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__1 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__2___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__2 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__3___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__3___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__3___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__3 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__4___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__4___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__4___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__4 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__5___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__5___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__5___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__5 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__5___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__6___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__6___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__6___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__6 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instHasRcoIntersectionNat__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instHasRcoIntersectionNat__7___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instHasRcoIntersectionNat__7___closed__0 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__7___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instHasRcoIntersectionNat__7 = (const lean_object*)&l_Std_instHasRcoIntersectionNat__7___closed__0_value;
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lean_nat_add(v_n_1_, v___x_2_);
v___x_4_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed(lean_object* v_n_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_PRange_instUpwardEnumerableNat___lam__0(v_n_5_);
lean_dec(v_n_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1(lean_object* v_k_7_, lean_object* v_n_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_nat_add(v_n_8_, v_k_7_);
v___x_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed(lean_object* v_k_11_, lean_object* v_n_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_PRange_instUpwardEnumerableNat___lam__1(v_k_11_, v_n_12_);
lean_dec(v_n_12_);
lean_dec(v_k_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0(lean_object* v_lo_23_, lean_object* v_hi_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v_hi_24_, v___x_25_);
v___x_27_ = lean_nat_sub(v___x_26_, v_lo_23_);
lean_dec(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat___lam__0___boxed(lean_object* v_lo_28_, lean_object* v_hi_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_PRange_instHasSizeNat___lam__0(v_lo_28_, v_hi_29_);
lean_dec(v_hi_29_);
lean_dec(v_lo_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0(lean_object* v_lo_33_, lean_object* v_hi_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_hi_34_, v___x_35_);
v___x_37_ = lean_nat_sub(v___x_36_, v_lo_33_);
lean_dec(v___x_36_);
v___x_38_ = lean_nat_sub(v___x_37_, v___x_35_);
lean_dec(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeNat__1___lam__0___boxed(lean_object* v_lo_39_, lean_object* v_hi_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_PRange_instHasSizeNat__1___lam__0(v_lo_39_, v_hi_40_);
lean_dec(v_hi_40_);
lean_dec(v_lo_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0(lean_object* v_r_44_, lean_object* v_s_45_){
_start:
{
lean_object* v_lower_46_; lean_object* v_upper_47_; lean_object* v_lower_48_; lean_object* v_upper_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_65_; 
v_lower_46_ = lean_ctor_get(v_r_44_, 0);
v_upper_47_ = lean_ctor_get(v_r_44_, 1);
v_lower_48_ = lean_ctor_get(v_s_45_, 0);
v_upper_49_ = lean_ctor_get(v_s_45_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_s_45_);
if (v_isSharedCheck_65_ == 0)
{
v___x_51_ = v_s_45_;
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_upper_49_);
lean_inc(v_lower_48_);
lean_dec(v_s_45_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___y_54_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_lower_46_, v___x_62_);
v___x_64_ = lean_nat_dec_le(v___x_63_, v_lower_48_);
if (v___x_64_ == 0)
{
lean_dec(v_lower_48_);
v___y_54_ = v___x_63_;
goto v___jp_53_;
}
else
{
lean_dec(v___x_63_);
v___y_54_ = v_lower_48_;
goto v___jp_53_;
}
v___jp_53_:
{
uint8_t v___x_55_; 
v___x_55_ = lean_nat_dec_le(v_upper_47_, v_upper_49_);
if (v___x_55_ == 0)
{
lean_object* v___x_57_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___y_54_);
v___x_57_ = v___x_51_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___y_54_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_upper_49_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
else
{
lean_object* v___x_60_; 
lean_dec(v_upper_49_);
lean_inc(v_upper_47_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v_upper_47_);
lean_ctor_set(v___x_51_, 0, v___y_54_);
v___x_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___y_54_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_upper_47_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat___lam__0___boxed(lean_object* v_r_66_, lean_object* v_s_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_instHasRcoIntersectionNat___lam__0(v_r_66_, v_s_67_);
lean_dec_ref(v_r_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0(lean_object* v_r_71_, lean_object* v_s_72_){
_start:
{
lean_object* v_lower_73_; lean_object* v_upper_74_; lean_object* v_lower_75_; lean_object* v_upper_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_93_; 
v_lower_73_ = lean_ctor_get(v_r_71_, 0);
v_upper_74_ = lean_ctor_get(v_r_71_, 1);
v_lower_75_ = lean_ctor_get(v_s_72_, 0);
v_upper_76_ = lean_ctor_get(v_s_72_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_s_72_);
if (v_isSharedCheck_93_ == 0)
{
v___x_78_ = v_s_72_;
v_isShared_79_ = v_isSharedCheck_93_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_upper_76_);
lean_inc(v_lower_75_);
lean_dec(v_s_72_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_93_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___y_82_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_lower_73_, v___x_80_);
v___x_92_ = lean_nat_dec_le(v___x_91_, v_lower_75_);
if (v___x_92_ == 0)
{
lean_dec(v_lower_75_);
v___y_82_ = v___x_91_;
goto v___jp_81_;
}
else
{
lean_dec(v___x_91_);
v___y_82_ = v_lower_75_;
goto v___jp_81_;
}
v___jp_81_:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_nat_add(v_upper_74_, v___x_80_);
v___x_84_ = lean_nat_dec_le(v___x_83_, v_upper_76_);
if (v___x_84_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v___x_83_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___y_82_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___y_82_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_upper_76_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v___x_89_; 
lean_dec(v_upper_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_83_);
lean_ctor_set(v___x_78_, 0, v___y_82_);
v___x_89_ = v___x_78_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___y_82_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_83_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__1___lam__0___boxed(lean_object* v_r_94_, lean_object* v_s_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_instHasRcoIntersectionNat__1___lam__0(v_r_94_, v_s_95_);
lean_dec_ref(v_r_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0(lean_object* v_r_99_, lean_object* v_s_100_){
_start:
{
lean_object* v_lower_101_; lean_object* v_upper_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_115_; 
v_lower_101_ = lean_ctor_get(v_s_100_, 0);
v_upper_102_ = lean_ctor_get(v_s_100_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_s_100_);
if (v_isSharedCheck_115_ == 0)
{
v___x_104_ = v_s_100_;
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_upper_102_);
lean_inc(v_lower_101_);
lean_dec(v_s_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_r_99_, v___x_106_);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_lower_101_);
if (v___x_108_ == 0)
{
lean_object* v___x_110_; 
lean_dec(v_lower_101_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_upper_102_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
else
{
lean_object* v___x_113_; 
lean_dec(v___x_107_);
if (v_isShared_105_ == 0)
{
v___x_113_ = v___x_104_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_lower_101_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_upper_102_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__2___lam__0___boxed(lean_object* v_r_116_, lean_object* v_s_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_instHasRcoIntersectionNat__2___lam__0(v_r_116_, v_s_117_);
lean_dec(v_r_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__3___lam__0(lean_object* v_r_121_, lean_object* v_s_122_){
_start:
{
lean_object* v_lower_123_; lean_object* v_upper_124_; lean_object* v_lower_125_; lean_object* v_upper_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_140_; 
v_lower_123_ = lean_ctor_get(v_r_121_, 0);
lean_inc(v_lower_123_);
v_upper_124_ = lean_ctor_get(v_r_121_, 1);
lean_inc(v_upper_124_);
lean_dec_ref(v_r_121_);
v_lower_125_ = lean_ctor_get(v_s_122_, 0);
v_upper_126_ = lean_ctor_get(v_s_122_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_s_122_);
if (v_isSharedCheck_140_ == 0)
{
v___x_128_ = v_s_122_;
v_isShared_129_ = v_isSharedCheck_140_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_upper_126_);
lean_inc(v_lower_125_);
lean_dec(v_s_122_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_140_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___y_131_; uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_le(v_lower_123_, v_lower_125_);
if (v___x_139_ == 0)
{
lean_dec(v_lower_125_);
v___y_131_ = v_lower_123_;
goto v___jp_130_;
}
else
{
lean_dec(v_lower_123_);
v___y_131_ = v_lower_125_;
goto v___jp_130_;
}
v___jp_130_:
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_le(v_upper_124_, v_upper_126_);
if (v___x_132_ == 0)
{
lean_object* v___x_134_; 
lean_dec(v_upper_124_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___y_131_);
v___x_134_ = v___x_128_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___y_131_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_upper_126_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v___x_137_; 
lean_dec(v_upper_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_upper_124_);
lean_ctor_set(v___x_128_, 0, v___y_131_);
v___x_137_ = v___x_128_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___y_131_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_upper_124_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__4___lam__0(lean_object* v_r_143_, lean_object* v_s_144_){
_start:
{
lean_object* v_lower_145_; lean_object* v_upper_146_; lean_object* v_lower_147_; lean_object* v_upper_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_164_; 
v_lower_145_ = lean_ctor_get(v_r_143_, 0);
lean_inc(v_lower_145_);
v_upper_146_ = lean_ctor_get(v_r_143_, 1);
lean_inc(v_upper_146_);
lean_dec_ref(v_r_143_);
v_lower_147_ = lean_ctor_get(v_s_144_, 0);
v_upper_148_ = lean_ctor_get(v_s_144_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_s_144_);
if (v_isSharedCheck_164_ == 0)
{
v___x_150_ = v_s_144_;
v_isShared_151_ = v_isSharedCheck_164_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_upper_148_);
lean_inc(v_lower_147_);
lean_dec(v_s_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_164_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___y_153_; uint8_t v___x_163_; 
v___x_163_ = lean_nat_dec_le(v_lower_145_, v_lower_147_);
if (v___x_163_ == 0)
{
lean_dec(v_lower_147_);
v___y_153_ = v_lower_145_;
goto v___jp_152_;
}
else
{
lean_dec(v_lower_145_);
v___y_153_ = v_lower_147_;
goto v___jp_152_;
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_upper_146_, v___x_154_);
lean_dec(v_upper_146_);
v___x_156_ = lean_nat_dec_le(v___x_155_, v_upper_148_);
if (v___x_156_ == 0)
{
lean_object* v___x_158_; 
lean_dec(v___x_155_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___y_153_);
v___x_158_ = v___x_150_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___y_153_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_upper_148_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
else
{
lean_object* v___x_161_; 
lean_dec(v_upper_148_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_155_);
lean_ctor_set(v___x_150_, 0, v___y_153_);
v___x_161_ = v___x_150_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___y_153_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_155_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__5___lam__0(lean_object* v_r_167_, lean_object* v_s_168_){
_start:
{
lean_object* v_lower_169_; lean_object* v_upper_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_181_; 
v_lower_169_ = lean_ctor_get(v_s_168_, 0);
v_upper_170_ = lean_ctor_get(v_s_168_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_s_168_);
if (v_isSharedCheck_181_ == 0)
{
v___x_172_ = v_s_168_;
v_isShared_173_ = v_isSharedCheck_181_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_upper_170_);
lean_inc(v_lower_169_);
lean_dec(v_s_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_181_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_le(v_r_167_, v_lower_169_);
if (v___x_174_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v_lower_169_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v_r_167_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_r_167_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_upper_170_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
else
{
lean_object* v___x_179_; 
lean_dec(v_r_167_);
if (v_isShared_173_ == 0)
{
v___x_179_ = v___x_172_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_lower_169_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_upper_170_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__6___lam__0(lean_object* v_r_184_, lean_object* v_s_185_){
_start:
{
lean_object* v_lower_186_; lean_object* v_upper_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_198_; 
v_lower_186_ = lean_ctor_get(v_s_185_, 0);
v_upper_187_ = lean_ctor_get(v_s_185_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_s_185_);
if (v_isSharedCheck_198_ == 0)
{
v___x_189_ = v_s_185_;
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_upper_187_);
lean_inc(v_lower_186_);
lean_dec(v_s_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
uint8_t v___x_191_; 
v___x_191_ = lean_nat_dec_le(v_r_184_, v_upper_187_);
if (v___x_191_ == 0)
{
lean_object* v___x_193_; 
lean_dec(v_r_184_);
if (v_isShared_190_ == 0)
{
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_lower_186_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_upper_187_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v_upper_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v_r_184_);
v___x_196_ = v___x_189_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_lower_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_r_184_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0(lean_object* v_r_201_, lean_object* v_s_202_){
_start:
{
lean_object* v_lower_203_; lean_object* v_upper_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_217_; 
v_lower_203_ = lean_ctor_get(v_s_202_, 0);
v_upper_204_ = lean_ctor_get(v_s_202_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_s_202_);
if (v_isSharedCheck_217_ == 0)
{
v___x_206_ = v_s_202_;
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_upper_204_);
lean_inc(v_lower_203_);
lean_dec(v_s_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_r_201_, v___x_208_);
v___x_210_ = lean_nat_dec_le(v___x_209_, v_upper_204_);
if (v___x_210_ == 0)
{
lean_object* v___x_212_; 
lean_dec(v___x_209_);
if (v_isShared_207_ == 0)
{
v___x_212_ = v___x_206_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_lower_203_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_upper_204_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
else
{
lean_object* v___x_215_; 
lean_dec(v_upper_204_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_209_);
v___x_215_ = v___x_206_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_lower_203_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_209_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instHasRcoIntersectionNat__7___lam__0___boxed(lean_object* v_r_218_, lean_object* v_s_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_instHasRcoIntersectionNat__7___lam__0(v_r_218_, v_s_219_);
lean_dec(v_r_218_);
return v_res_220_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Nat(builtin);
}
#ifdef __cplusplus
}
#endif
