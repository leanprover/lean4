// Lean compiler output
// Module: Init.Data.Nat.ExtendedGcd
// Imports: public import Init.Data.Nat.Gcd public import Init.Data.Int.Basic public import Init.Data.Int.Repr import Init.Data.Int.Lemmas import Init.Data.AC import Init.TacticsExtra
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_instReprExtendedGcdResult_repr_spec__0(lean_object*);
static const lean_string_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__0 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__0_value;
static const lean_string_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "gcd"};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__1 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__1_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__1_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__2 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__2_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__2_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__3 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__3_value;
static const lean_string_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__4 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__4_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__4_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__5 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__5_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__3_value),((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__5_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__6 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__6_value;
static lean_once_cell_t l_Nat_instReprExtendedGcdResult_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__7;
static const lean_string_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__8 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__8_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__8_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__9 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__9_value;
static const lean_string_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "coeffA"};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__10 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__10_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__10_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__11 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__11_value;
static lean_once_cell_t l_Nat_instReprExtendedGcdResult_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__12;
static const lean_string_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__13 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__13_value;
static lean_once_cell_t l_Nat_instReprExtendedGcdResult_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__14;
static lean_once_cell_t l_Nat_instReprExtendedGcdResult_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__15;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__0_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__16 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__16_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__13_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__17 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__17_value;
static const lean_string_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "coeffB"};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__18 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__18_value;
static const lean_ctor_object l_Nat_instReprExtendedGcdResult_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__18_value)}};
static const lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__19 = (const lean_object*)&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__19_value;
static lean_once_cell_t l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20;
LEAN_EXPORT lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_instReprExtendedGcdResult_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instReprExtendedGcdResult_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Nat_instReprExtendedGcdResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_instReprExtendedGcdResult_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_instReprExtendedGcdResult___closed__0 = (const lean_object*)&l_Nat_instReprExtendedGcdResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_instReprExtendedGcdResult = (const lean_object*)&l_Nat_instReprExtendedGcdResult___closed__0_value;
LEAN_EXPORT uint8_t l_Nat_instDecidableEqExtendedGcdResult_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instDecidableEqExtendedGcdResult_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_instDecidableEqExtendedGcdResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instDecidableEqExtendedGcdResult___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Nat_instInhabitedExtendedGcdResult_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_instInhabitedExtendedGcdResult_default___closed__0;
LEAN_EXPORT lean_object* l_Nat_instInhabitedExtendedGcdResult_default;
LEAN_EXPORT lean_object* l_Nat_instInhabitedExtendedGcdResult;
LEAN_EXPORT lean_object* l_Nat_extendedGcd_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_extended_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_extendedGcd___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Nat_ExtendedGcd_0__Nat_extendedGcdFallback___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_ExtendedGcd_0__Nat_extendedGcdFallback___closed__0;
LEAN_EXPORT lean_object* lean_nat_extended_gcd_fallback(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_instReprExtendedGcdResult_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(7u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(10u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__0));
v___x_28_ = lean_string_length(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__14, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__14_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__14);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Nat_instReprExtendedGcdResult_repr___redArg(lean_object* v_x_40_){
_start:
{
lean_object* v_gcd_41_; lean_object* v_coeffA_42_; lean_object* v_coeffB_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___y_62_; lean_object* v___y_63_; lean_object* v___y_75_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v_gcd_41_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_gcd_41_);
v_coeffA_42_ = lean_ctor_get(v_x_40_, 1);
lean_inc(v_coeffA_42_);
v_coeffB_43_ = lean_ctor_get(v_x_40_, 2);
lean_inc(v_coeffB_43_);
lean_dec_ref(v_x_40_);
v___x_44_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__5));
v___x_45_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__6));
v___x_46_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__7, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__7_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__7);
v___x_47_ = l_Nat_reprFast(v_gcd_41_);
v___x_48_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_46_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = 0;
v___x_51_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*1, v___x_50_);
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_45_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__9));
v___x_54_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_box(1);
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__11));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_44_);
v___x_60_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__12, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__12_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__12);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20);
v___x_94_ = lean_int_dec_lt(v_coeffA_42_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = l_Int_repr(v_coeffA_42_);
lean_dec(v_coeffA_42_);
v___x_96_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
v___y_75_ = v___x_96_;
goto v___jp_74_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = l_Int_repr(v_coeffA_42_);
lean_dec(v_coeffA_42_);
v___x_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v___x_92_);
v___y_75_ = v___x_99_;
goto v___jp_74_;
}
v___jp_61_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_64_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_60_);
lean_ctor_set(v___x_64_, 1, v___y_63_);
v___x_65_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*1, v___x_50_);
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___y_62_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__15, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__15_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__15);
v___x_68_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__16));
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_66_);
v___x_70_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__17));
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_67_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1, v___x_50_);
return v___x_73_;
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_76_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_60_);
lean_ctor_set(v___x_76_, 1, v___y_75_);
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_50_);
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_59_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_53_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_55_);
v___x_81_ = ((lean_object*)(l_Nat_instReprExtendedGcdResult_repr___redArg___closed__19));
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_44_);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20);
v___x_86_ = lean_int_dec_lt(v_coeffB_43_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = l_Int_repr(v_coeffB_43_);
lean_dec(v_coeffB_43_);
v___x_88_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
v___y_62_ = v___x_83_;
v___y_63_ = v___x_88_;
goto v___jp_61_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = l_Int_repr(v_coeffB_43_);
lean_dec(v_coeffB_43_);
v___x_90_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
v___x_91_ = l_Repr_addAppParen(v___x_90_, v___x_84_);
v___y_62_ = v___x_83_;
v___y_63_ = v___x_91_;
goto v___jp_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_instReprExtendedGcdResult_repr(lean_object* v_x_100_, lean_object* v_prec_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Nat_instReprExtendedGcdResult_repr___redArg(v_x_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Nat_instReprExtendedGcdResult_repr___boxed(lean_object* v_x_103_, lean_object* v_prec_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Nat_instReprExtendedGcdResult_repr(v_x_103_, v_prec_104_);
lean_dec(v_prec_104_);
return v_res_105_;
}
}
LEAN_EXPORT uint8_t l_Nat_instDecidableEqExtendedGcdResult_decEq(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_gcd_110_; lean_object* v_coeffA_111_; lean_object* v_coeffB_112_; lean_object* v_gcd_113_; lean_object* v_coeffA_114_; lean_object* v_coeffB_115_; uint8_t v___x_116_; 
v_gcd_110_ = lean_ctor_get(v_x_108_, 0);
v_coeffA_111_ = lean_ctor_get(v_x_108_, 1);
v_coeffB_112_ = lean_ctor_get(v_x_108_, 2);
v_gcd_113_ = lean_ctor_get(v_x_109_, 0);
v_coeffA_114_ = lean_ctor_get(v_x_109_, 1);
v_coeffB_115_ = lean_ctor_get(v_x_109_, 2);
v___x_116_ = lean_nat_dec_eq(v_gcd_110_, v_gcd_113_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = lean_int_dec_eq(v_coeffA_111_, v_coeffA_114_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = lean_int_dec_eq(v_coeffB_112_, v_coeffB_115_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_instDecidableEqExtendedGcdResult_decEq___boxed(lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Nat_instDecidableEqExtendedGcdResult_decEq(v_x_119_, v_x_120_);
lean_dec_ref(v_x_120_);
lean_dec_ref(v_x_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Nat_instDecidableEqExtendedGcdResult(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = l_Nat_instDecidableEqExtendedGcdResult_decEq(v_x_123_, v_x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Nat_instDecidableEqExtendedGcdResult___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Nat_instDecidableEqExtendedGcdResult(v_x_126_, v_x_127_);
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
static lean_object* _init_l_Nat_instInhabitedExtendedGcdResult_default___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Nat_instInhabitedExtendedGcdResult_default(void){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Nat_instInhabitedExtendedGcdResult_default___closed__0, &l_Nat_instInhabitedExtendedGcdResult_default___closed__0_once, _init_l_Nat_instInhabitedExtendedGcdResult_default___closed__0);
return v___x_133_;
}
}
static lean_object* _init_l_Nat_instInhabitedExtendedGcdResult(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Nat_instInhabitedExtendedGcdResult_default;
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Nat_extendedGcd_go(lean_object* v_r_135_, lean_object* v_s_136_, lean_object* v_t_137_, lean_object* v_r_x27_138_, lean_object* v_s_x27_139_, lean_object* v_t_x27_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_nat_dec_eq(v_r_135_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v_q_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_143_ = lean_nat_div(v_r_x27_138_, v_r_135_);
v_q_144_ = lean_nat_to_int(v___x_143_);
v___x_145_ = lean_nat_mod(v_r_x27_138_, v_r_135_);
lean_dec(v_r_x27_138_);
v___x_146_ = lean_int_mul(v_q_144_, v_s_136_);
v___x_147_ = lean_int_sub(v_s_x27_139_, v___x_146_);
lean_dec(v___x_146_);
lean_dec(v_s_x27_139_);
v___x_148_ = lean_int_mul(v_q_144_, v_t_137_);
lean_dec(v_q_144_);
v___x_149_ = lean_int_sub(v_t_x27_140_, v___x_148_);
lean_dec(v___x_148_);
lean_dec(v_t_x27_140_);
{
lean_object* _tmp_0 = v___x_145_;
lean_object* _tmp_1 = v___x_147_;
lean_object* _tmp_2 = v___x_149_;
lean_object* _tmp_3 = v_r_135_;
lean_object* _tmp_4 = v_s_136_;
lean_object* _tmp_5 = v_t_137_;
v_r_135_ = _tmp_0;
v_s_136_ = _tmp_1;
v_t_137_ = _tmp_2;
v_r_x27_138_ = _tmp_3;
v_s_x27_139_ = _tmp_4;
v_t_x27_140_ = _tmp_5;
}
goto _start;
}
else
{
lean_object* v___x_151_; 
lean_dec(v_t_137_);
lean_dec(v_s_136_);
lean_dec(v_r_135_);
v___x_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_151_, 0, v_r_x27_138_);
lean_ctor_set(v___x_151_, 1, v_s_x27_139_);
lean_ctor_set(v___x_151_, 2, v_t_x27_140_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_extendedGcd___boxed(lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = lean_nat_extended_gcd(v_a_154_, v_b_155_);
lean_dec(v_b_155_);
lean_dec(v_a_154_);
return v_res_156_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_ExtendedGcd_0__Nat_extendedGcdFallback___closed__0(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* lean_nat_extended_gcd_fallback(lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l___private_Init_Data_Nat_ExtendedGcd_0__Nat_extendedGcdFallback___closed__0, &l___private_Init_Data_Nat_ExtendedGcd_0__Nat_extendedGcdFallback___closed__0_once, _init_l___private_Init_Data_Nat_ExtendedGcd_0__Nat_extendedGcdFallback___closed__0);
v___x_162_ = lean_obj_once(&l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20, &l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20_once, _init_l_Nat_instReprExtendedGcdResult_repr___redArg___closed__20);
v___x_163_ = l_Nat_extendedGcd_go(v_a_159_, v___x_161_, v___x_162_, v_b_160_, v___x_162_, v___x_161_);
return v___x_163_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_ExtendedGcd(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_instInhabitedExtendedGcdResult_default = _init_l_Nat_instInhabitedExtendedGcdResult_default();
lean_mark_persistent(l_Nat_instInhabitedExtendedGcdResult_default);
l_Nat_instInhabitedExtendedGcdResult = _init_l_Nat_instInhabitedExtendedGcdResult();
lean_mark_persistent(l_Nat_instInhabitedExtendedGcdResult);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_ExtendedGcd(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_AC(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_ExtendedGcd(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_ExtendedGcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_ExtendedGcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_ExtendedGcd(builtin);
}
#ifdef __cplusplus
}
#endif
