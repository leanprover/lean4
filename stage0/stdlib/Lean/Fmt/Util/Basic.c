// Lean compiler output
// Module: Lean.Fmt.Util.Basic
// Imports: public import Init.Data.Ord.Basic public import Init.Data.String.Subslice import Init.Data.Hashable import Init.Data.ToString public import Lean.Syntax
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_instHashableRaw__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_instHashableRaw__lean_hash___boxed(lean_object*);
static const lean_closure_object l_instHashableRaw__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableRaw__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableRaw__lean___closed__0 = (const lean_object*)&l_instHashableRaw__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableRaw__lean = (const lean_object*)&l_instHashableRaw__lean___closed__0_value;
LEAN_EXPORT uint8_t l_instOrdRaw__lean_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdRaw__lean_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdRaw__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdRaw__lean_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdRaw__lean___closed__0 = (const lean_object*)&l_instOrdRaw__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrdRaw__lean = (const lean_object*)&l_instOrdRaw__lean___closed__0_value;
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashablePos__lean(lean_object*);
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdPos__lean(lean_object*);
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqSubslice__lean(lean_object*);
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableSubslice__lean(lean_object*);
static const lean_string_object l_instToStringSubslice__lean___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " - "};
static const lean_object* l_instToStringSubslice__lean___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringSubslice__lean___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___redArg___lam__0(lean_object*);
static const lean_closure_object l_instToStringSubslice__lean___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringSubslice__lean___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringSubslice__lean___redArg___closed__0 = (const lean_object*)&l_instToStringSubslice__lean___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___redArg();
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubslice__lean(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprSubslice__lean___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprSubslice__lean___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprSubslice__lean___redArg___closed__0 = (const lean_object*)&l_instReprSubslice__lean___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg();
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubslice__lean(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubslice__lean___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_split___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_split(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableRaw__lean_hash(lean_object* v_x_1_){
_start:
{
uint64_t v___x_2_; uint64_t v___x_3_; uint64_t v___x_4_; 
v___x_2_ = 0ULL;
v___x_3_ = lean_uint64_of_nat(v_x_1_);
v___x_4_ = lean_uint64_mix_hash(v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_instHashableRaw__lean_hash___boxed(lean_object* v_x_5_){
_start:
{
uint64_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_instHashableRaw__lean_hash(v_x_5_);
lean_dec(v_x_5_);
v_r_7_ = lean_box_uint64(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_instOrdRaw__lean_ord(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_lt(v_x_10_, v_x_11_);
if (v___x_12_ == 0)
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_eq(v_x_10_, v_x_11_);
if (v___x_13_ == 0)
{
uint8_t v___x_14_; 
v___x_14_ = 2;
return v___x_14_;
}
else
{
uint8_t v___x_15_; 
v___x_15_ = 1;
return v___x_15_;
}
}
else
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdRaw__lean_ord___boxed(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_instOrdRaw__lean_ord(v_x_17_, v_x_18_);
lean_dec(v_x_18_);
lean_dec(v_x_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash___redArg(lean_object* v_x_23_){
_start:
{
uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; 
v___x_24_ = 0ULL;
v___x_25_ = l_instHashableRaw__lean_hash(v_x_23_);
v___x_26_ = lean_uint64_mix_hash(v___x_24_, v___x_25_);
v___x_27_ = lean_uint64_mix_hash(v___x_26_, v___x_24_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___redArg___boxed(lean_object* v_x_28_){
_start:
{
uint64_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_instHashablePos__lean_hash___redArg(v_x_28_);
lean_dec(v_x_28_);
v_r_30_ = lean_box_uint64(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint64_t l_instHashablePos__lean_hash(lean_object* v_s_31_, lean_object* v_x_32_){
_start:
{
uint64_t v___x_33_; 
v___x_33_ = l_instHashablePos__lean_hash___redArg(v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_instHashablePos__lean_hash___boxed(lean_object* v_s_34_, lean_object* v_x_35_){
_start:
{
uint64_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_instHashablePos__lean_hash(v_s_34_, v_x_35_);
lean_dec(v_x_35_);
lean_dec_ref(v_s_34_);
v_r_37_ = lean_box_uint64(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_instHashablePos__lean(lean_object* v_s_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_closure((void*)(l_instHashablePos__lean_hash___boxed), 2, 1);
lean_closure_set(v___x_39_, 0, v_s_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord___redArg(lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = l_instOrdRaw__lean_ord(v_x_40_, v_x_41_);
if (v___x_42_ == 1)
{
return v___x_42_;
}
else
{
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___redArg___boxed(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_instOrdPos__lean_ord___redArg(v_x_43_, v_x_44_);
lean_dec(v_x_44_);
lean_dec(v_x_43_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_instOrdPos__lean_ord(lean_object* v_s_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
uint8_t v___x_50_; 
v___x_50_ = l_instOrdPos__lean_ord___redArg(v_x_48_, v_x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_instOrdPos__lean_ord___boxed(lean_object* v_s_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_instOrdPos__lean_ord(v_s_51_, v_x_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec(v_x_52_);
lean_dec_ref(v_s_51_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_instOrdPos__lean(lean_object* v_s_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_alloc_closure((void*)(l_instOrdPos__lean_ord___boxed), 3, 1);
lean_closure_set(v___x_57_, 0, v_s_56_);
return v___x_57_;
}
}
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq___redArg(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_startInclusive_60_; lean_object* v_endExclusive_61_; lean_object* v_startInclusive_62_; lean_object* v_endExclusive_63_; uint8_t v_decide_64_; 
v_startInclusive_60_ = lean_ctor_get(v_x_58_, 0);
v_endExclusive_61_ = lean_ctor_get(v_x_58_, 1);
v_startInclusive_62_ = lean_ctor_get(v_x_59_, 0);
v_endExclusive_63_ = lean_ctor_get(v_x_59_, 1);
v_decide_64_ = lean_nat_dec_eq(v_startInclusive_60_, v_startInclusive_62_);
if (v_decide_64_ == 0)
{
return v_decide_64_;
}
else
{
uint8_t v_decide_65_; 
v_decide_65_ = lean_nat_dec_eq(v_endExclusive_61_, v_endExclusive_63_);
return v_decide_65_;
}
}
}
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___redArg___boxed(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_instBEqSubslice__lean_beq___redArg(v_x_66_, v_x_67_);
lean_dec_ref(v_x_67_);
lean_dec_ref(v_x_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_instBEqSubslice__lean_beq(lean_object* v_s_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_instBEqSubslice__lean_beq___redArg(v_x_71_, v_x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_instBEqSubslice__lean_beq___boxed(lean_object* v_s_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_instBEqSubslice__lean_beq(v_s_74_, v_x_75_, v_x_76_);
lean_dec_ref(v_x_76_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_s_74_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_instBEqSubslice__lean(lean_object* v_s_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_closure((void*)(l_instBEqSubslice__lean_beq___boxed), 3, 1);
lean_closure_set(v___x_80_, 0, v_s_79_);
return v___x_80_;
}
}
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash___redArg(lean_object* v_x_81_){
_start:
{
lean_object* v_startInclusive_82_; lean_object* v_endExclusive_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; 
v_startInclusive_82_ = lean_ctor_get(v_x_81_, 0);
v_endExclusive_83_ = lean_ctor_get(v_x_81_, 1);
v___x_84_ = 0ULL;
v___x_85_ = l_instHashablePos__lean_hash___redArg(v_startInclusive_82_);
v___x_86_ = lean_uint64_mix_hash(v___x_84_, v___x_85_);
v___x_87_ = l_instHashablePos__lean_hash___redArg(v_endExclusive_83_);
v___x_88_ = lean_uint64_mix_hash(v___x_86_, v___x_87_);
v___x_89_ = lean_uint64_mix_hash(v___x_88_, v___x_84_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___redArg___boxed(lean_object* v_x_90_){
_start:
{
uint64_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_instHashableSubslice__lean_hash___redArg(v_x_90_);
lean_dec_ref(v_x_90_);
v_r_92_ = lean_box_uint64(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint64_t l_instHashableSubslice__lean_hash(lean_object* v_s_93_, lean_object* v_x_94_){
_start:
{
uint64_t v___x_95_; 
v___x_95_ = l_instHashableSubslice__lean_hash___redArg(v_x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_instHashableSubslice__lean_hash___boxed(lean_object* v_s_96_, lean_object* v_x_97_){
_start:
{
uint64_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_instHashableSubslice__lean_hash(v_s_96_, v_x_97_);
lean_dec_ref(v_x_97_);
lean_dec_ref(v_s_96_);
v_r_99_ = lean_box_uint64(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_instHashableSubslice__lean(lean_object* v_s_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_closure((void*)(l_instHashableSubslice__lean_hash___boxed), 2, 1);
lean_closure_set(v___x_101_, 0, v_s_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___redArg___lam__0(lean_object* v_s_103_){
_start:
{
lean_object* v_startInclusive_104_; lean_object* v_endExclusive_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_startInclusive_104_ = lean_ctor_get(v_s_103_, 0);
lean_inc(v_startInclusive_104_);
v_endExclusive_105_ = lean_ctor_get(v_s_103_, 1);
lean_inc(v_endExclusive_105_);
lean_dec_ref(v_s_103_);
v___x_106_ = l_Nat_reprFast(v_startInclusive_104_);
v___x_107_ = ((lean_object*)(l_instToStringSubslice__lean___redArg___lam__0___closed__0));
v___x_108_ = lean_string_append(v___x_106_, v___x_107_);
v___x_109_ = l_Nat_reprFast(v_endExclusive_105_);
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
lean_dec_ref(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___redArg(){
_start:
{
lean_object* v___f_113_; 
v___f_113_ = ((lean_object*)(l_instToStringSubslice__lean___redArg___closed__0));
return v___f_113_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___redArg___boxed(lean_object* v___dummy_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_instToStringSubslice__lean___redArg();
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean(lean_object* v_s_116_){
_start:
{
lean_object* v___f_117_; 
v___f_117_ = ((lean_object*)(l_instToStringSubslice__lean___redArg___closed__0));
return v___f_117_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubslice__lean___boxed(lean_object* v_s_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_instToStringSubslice__lean(v_s_118_);
lean_dec_ref(v_s_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg___lam__0(lean_object* v_s_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_startInclusive_122_; lean_object* v_endExclusive_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_startInclusive_122_ = lean_ctor_get(v_s_120_, 0);
lean_inc(v_startInclusive_122_);
v_endExclusive_123_ = lean_ctor_get(v_s_120_, 1);
lean_inc(v_endExclusive_123_);
lean_dec_ref(v_s_120_);
v___x_124_ = l_Nat_reprFast(v_startInclusive_122_);
v___x_125_ = ((lean_object*)(l_instToStringSubslice__lean___redArg___lam__0___closed__0));
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
v___x_127_ = l_Nat_reprFast(v_endExclusive_123_);
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg___lam__0___boxed(lean_object* v_s_130_, lean_object* v_x_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_instReprSubslice__lean___redArg___lam__0(v_s_130_, v_x_131_);
lean_dec(v_x_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg(){
_start:
{
lean_object* v___f_135_; 
v___f_135_ = ((lean_object*)(l_instReprSubslice__lean___redArg___closed__0));
return v___f_135_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___redArg___boxed(lean_object* v___dummy_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_instReprSubslice__lean___redArg();
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean(lean_object* v_s_138_){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = ((lean_object*)(l_instReprSubslice__lean___redArg___closed__0));
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l_instReprSubslice__lean___boxed(lean_object* v_s_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_instReprSubslice__lean(v_s_140_);
lean_dec_ref(v_s_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f(lean_object* v_info_142_){
_start:
{
if (lean_obj_tag(v_info_142_) == 0)
{
lean_object* v_leading_143_; lean_object* v___x_144_; 
v_leading_143_ = lean_ctor_get(v_info_142_, 0);
lean_inc_ref(v_leading_143_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_leading_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getLeading_x3f___boxed(lean_object* v_info_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_SourceInfo_getLeading_x3f(v_info_146_);
lean_dec(v_info_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f(lean_object* v_stx_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = l_Lean_Syntax_getHeadInfo(v_stx_148_);
v___x_150_ = l_Lean_SourceInfo_getLeading_x3f(v___x_149_);
lean_dec(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getLeading_x3f___boxed(lean_object* v_stx_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Syntax_getLeading_x3f(v_stx_151_);
lean_dec(v_stx_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f(lean_object* v_stx_153_){
_start:
{
lean_object* v_info_154_; lean_object* v___x_155_; 
v_info_154_ = l_Lean_Syntax_getHeadInfo(v_stx_153_);
v___x_155_ = l_Lean_SourceInfo_getLeading_x3f(v_info_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
uint8_t v___x_156_; lean_object* v___x_157_; 
v___x_156_ = 0;
v___x_157_ = l_Lean_SourceInfo_getPos_x3f(v_info_154_, v___x_156_);
lean_dec(v_info_154_);
return v___x_157_;
}
else
{
lean_object* v_val_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
lean_dec(v_info_154_);
v_val_158_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_155_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_val_158_);
lean_dec(v___x_155_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_startPos_162_; lean_object* v___x_164_; 
v_startPos_162_ = lean_ctor_get(v_val_158_, 1);
lean_inc(v_startPos_162_);
lean_dec(v_val_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v_startPos_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_startPos_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getStartPos_x3f___boxed(lean_object* v_stx_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Syntax_getStartPos_x3f(v_stx_167_);
lean_dec(v_stx_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring(lean_object* v_s_169_){
_start:
{
lean_object* v_startPos_170_; lean_object* v_stopPos_171_; lean_object* v___x_172_; 
v_startPos_170_ = lean_ctor_get(v_s_169_, 1);
v_stopPos_171_ = lean_ctor_get(v_s_169_, 2);
lean_inc(v_stopPos_171_);
lean_inc(v_startPos_170_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_startPos_170_);
lean_ctor_set(v___x_172_, 1, v_stopPos_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_ofSubstring___boxed(lean_object* v_s_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Syntax_Range_ofSubstring(v_s_173_);
lean_dec_ref(v_s_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg___lam__0(lean_object* v_toPure_175_, lean_object* v_00_u03b1_176_, lean_object* v_o_x3f_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_apply_2(v_toPure_175_, lean_box(0), v_o_x3f_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean___redArg(lean_object* v_inst_179_){
_start:
{
lean_object* v_toApplicative_180_; lean_object* v_toPure_181_; lean_object* v___f_182_; 
v_toApplicative_180_ = lean_ctor_get(v_inst_179_, 0);
lean_inc_ref(v_toApplicative_180_);
lean_dec_ref(v_inst_179_);
v_toPure_181_ = lean_ctor_get(v_toApplicative_180_, 1);
lean_inc(v_toPure_181_);
lean_dec_ref(v_toApplicative_180_);
v___f_182_ = lean_alloc_closure((void*)(l_instMonadLiftOptionOptionTOfMonad__lean___redArg___lam__0), 3, 1);
lean_closure_set(v___f_182_, 0, v_toPure_181_);
return v___f_182_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftOptionOptionTOfMonad__lean(lean_object* v_m_183_, lean_object* v_inst_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_instMonadLiftOptionOptionTOfMonad__lean___redArg(v_inst_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Option_split___redArg(lean_object* v_o_186_){
_start:
{
lean_object* v___y_188_; 
if (lean_obj_tag(v_o_186_) == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
v___y_188_ = v___x_208_;
goto v___jp_187_;
}
else
{
lean_object* v_val_209_; lean_object* v_fst_210_; lean_object* v___x_211_; 
v_val_209_ = lean_ctor_get(v_o_186_, 0);
v_fst_210_ = lean_ctor_get(v_val_209_, 0);
lean_inc(v_fst_210_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v_fst_210_);
v___y_188_ = v___x_211_;
goto v___jp_187_;
}
v___jp_187_:
{
if (lean_obj_tag(v_o_186_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___y_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_207_; 
v_val_191_ = lean_ctor_get(v_o_186_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_o_186_);
if (v_isSharedCheck_207_ == 0)
{
v___x_193_ = v_o_186_;
v_isShared_194_ = v_isSharedCheck_207_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_dec(v_o_186_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_207_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v_snd_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_205_; 
v_snd_195_ = lean_ctor_get(v_val_191_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_val_191_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_val_191_, 0);
lean_dec(v_unused_206_);
v___x_197_ = v_val_191_;
v_isShared_198_ = v_isSharedCheck_205_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_snd_195_);
lean_dec(v_val_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_205_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v_snd_195_);
v___x_200_ = v___x_193_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_snd_195_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_200_);
lean_ctor_set(v___x_197_, 0, v___y_188_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___y_188_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_200_);
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
}
}
LEAN_EXPORT lean_object* l_Option_split(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b2_213_, lean_object* v_o_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Option_split___redArg(v_o_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(lean_object* v_as_225_, size_t v_i_226_, size_t v_stop_227_, lean_object* v_b_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_usize_dec_eq(v_i_226_, v_stop_227_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v_fst_231_; lean_object* v_snd_232_; lean_object* v___y_234_; 
v___x_230_ = lean_array_uget_borrowed(v_as_225_, v_i_226_);
v_fst_231_ = lean_ctor_get(v___x_230_, 0);
v_snd_232_ = lean_ctor_get(v___x_230_, 1);
if (lean_obj_tag(v_snd_232_) == 0)
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3));
v___y_234_ = v___x_243_;
goto v___jp_233_;
}
else
{
lean_object* v_val_244_; 
v_val_244_ = lean_ctor_get(v_snd_232_, 0);
lean_inc(v_val_244_);
v___y_234_ = v_val_244_;
goto v___jp_233_;
}
v___jp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; size_t v___x_240_; size_t v___x_241_; 
v___x_235_ = lean_unsigned_to_nat(2u);
v___x_236_ = lean_mk_empty_array_with_capacity(v___x_235_);
lean_inc(v_fst_231_);
v___x_237_ = lean_array_push(v___x_236_, v_fst_231_);
v___x_238_ = lean_array_push(v___x_237_, v___y_234_);
v___x_239_ = l_Array_append___redArg(v_b_228_, v___x_238_);
lean_dec_ref(v___x_238_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_add(v_i_226_, v___x_240_);
v_i_226_ = v___x_241_;
v_b_228_ = v___x_239_;
goto _start;
}
}
else
{
return v_b_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___boxed(lean_object* v_as_245_, lean_object* v_i_246_, lean_object* v_stop_247_, lean_object* v_b_248_){
_start:
{
size_t v_i_boxed_249_; size_t v_stop_boxed_250_; lean_object* v_res_251_; 
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_stop_boxed_250_ = lean_unbox_usize(v_stop_247_);
lean_dec(v_stop_247_);
v_res_251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(v_as_245_, v_i_boxed_249_, v_stop_boxed_250_, v_b_248_);
lean_dec_ref(v_as_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(lean_object* v_elems_252_, lean_object* v_seps_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_254_ = l_Array_zip___redArg(v_elems_252_, v_seps_253_);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0));
v___x_257_ = lean_array_get_size(v___x_254_);
v___x_258_ = lean_nat_dec_lt(v___x_255_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec_ref(v___x_254_);
return v___x_256_;
}
else
{
size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; 
v___x_259_ = ((size_t)0ULL);
v___x_260_ = lean_usize_of_nat(v___x_257_);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(v___x_254_, v___x_259_, v___x_260_, v___x_256_);
lean_dec_ref(v___x_254_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg___boxed(lean_object* v_elems_262_, lean_object* v_seps_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v_elems_262_, v_seps_263_);
lean_dec_ref(v_seps_263_);
lean_dec_ref(v_elems_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps(lean_object* v_kinds_265_, lean_object* v_elems_266_, lean_object* v_seps_267_, lean_object* v_sep_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v_elems_266_, v_seps_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___boxed(lean_object* v_kinds_270_, lean_object* v_elems_271_, lean_object* v_seps_272_, lean_object* v_sep_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps(v_kinds_270_, v_elems_271_, v_seps_272_, v_sep_273_);
lean_dec_ref(v_sep_273_);
lean_dec_ref(v_seps_272_);
lean_dec_ref(v_elems_271_);
lean_dec(v_kinds_270_);
return v_res_274_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Util_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Util_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lean_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Util_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Util_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
