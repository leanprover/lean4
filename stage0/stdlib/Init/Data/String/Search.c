// Lean compiler output
// Module: Init.Data.String.Search
// Imports: public import Init.Data.String.Slice.Pattern public import Init.Data.String.Slice.Numeric import Init.Data.Iterators.Consumers.Collect
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toInt_x3f(lean_object*);
uint8_t l_String_Slice_isInt(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_lines(lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_splitInclusive___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_Pos_find_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pos_find_x3f___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_Pos_find_x3f___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pos_find_x3f___redArg___closed__0_value;
static const lean_closure_object l_String_Slice_Pos_find_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_String_Slice_Pos_find_x3f___redArg___closed__1 = (const lean_object*)&l_String_Slice_Pos_find_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_posof(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitInclusive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitInclusive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitInclusive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(lean_object*, uint32_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_any___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_any___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object*);
LEAN_EXPORT uint8_t l_String_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object*);
static const lean_string_object l_String_toInt_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Int expected"};
static const lean_object* l_String_toInt_x21___closed__0 = (const lean_object*)&l_String_toInt_x21___closed__0_value;
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_front_x3f(lean_object*);
LEAN_EXPORT uint32_t l_String_front(lean_object*);
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_string_front(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_back_x3f(lean_object*);
LEAN_EXPORT uint32_t l_String_back(lean_object*);
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_lines(lean_object*);
LEAN_EXPORT lean_object* l_String_replace___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_s_3_, lean_object* v_inst_4_, lean_object* v_replacement_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_string_utf8_byte_size(v_s_3_);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v_s_3_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_7_);
v___x_9_ = l_String_Slice_replace___redArg(v_inst_1_, v_inst_2_, v___x_8_, v_inst_4_, v_replacement_5_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_String_replace(lean_object* v_00_u03c1_10_, lean_object* v_00_u03c3_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_s_16_, lean_object* v_pattern_17_, lean_object* v_inst_18_, lean_object* v_replacement_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_string_utf8_byte_size(v_s_16_);
v___x_22_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_22_, 0, v_s_16_);
lean_ctor_set(v___x_22_, 1, v___x_20_);
lean_ctor_set(v___x_22_, 2, v___x_21_);
v___x_23_ = l_String_Slice_replace___redArg(v_inst_13_, v_inst_15_, v___x_22_, v_inst_18_, v_replacement_19_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_String_replace___boxed(lean_object* v_00_u03c1_24_, lean_object* v_00_u03c3_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_s_30_, lean_object* v_pattern_31_, lean_object* v_inst_32_, lean_object* v_replacement_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_String_replace(v_00_u03c1_24_, v_00_u03c3_25_, v_inst_26_, v_inst_27_, v_00_u03b1_28_, v_inst_29_, v_s_30_, v_pattern_31_, v_inst_32_, v_replacement_33_);
lean_dec(v_pattern_31_);
lean_dec(v_inst_26_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__0(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_f_37_, lean_object* v_c_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_apply_1(v_f_37_, v_c_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1(lean_object* v___x_40_, lean_object* v_x1_41_, lean_object* v_x2_42_, lean_object* v_x3_43_){
_start:
{
if (lean_obj_tag(v_x1_41_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_40_);
return v___x_44_;
}
else
{
lean_object* v_startPos_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v___x_40_);
v_startPos_45_ = lean_ctor_get(v_x1_41_, 0);
lean_inc(v_startPos_45_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v_startPos_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed(lean_object* v___x_48_, lean_object* v_x1_49_, lean_object* v_x2_50_, lean_object* v_x3_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_String_Slice_Pos_find_x3f___redArg___lam__1(v___x_48_, v_x1_49_, v_x2_50_, v_x3_51_);
lean_dec(v_x3_51_);
lean_dec_ref(v_x1_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg(lean_object* v_inst_56_, lean_object* v_s_57_, lean_object* v_pos_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v_str_60_; lean_object* v_startInclusive_61_; lean_object* v_endExclusive_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_84_; 
v_str_60_ = lean_ctor_get(v_s_57_, 0);
v_startInclusive_61_ = lean_ctor_get(v_s_57_, 1);
v_endExclusive_62_ = lean_ctor_get(v_s_57_, 2);
v_isSharedCheck_84_ = !lean_is_exclusive(v_s_57_);
if (v_isSharedCheck_84_ == 0)
{
v___x_64_ = v_s_57_;
v_isShared_65_ = v_isSharedCheck_84_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_endExclusive_62_);
lean_inc(v_startInclusive_61_);
lean_inc(v_str_60_);
lean_dec(v_s_57_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_84_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___f_66_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_67_ = lean_nat_add(v_startInclusive_61_, v_pos_58_);
lean_dec(v_startInclusive_61_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___x_67_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_str_60_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_endExclusive_62_);
v___x_69_ = v_reuseFailAlloc_83_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v_searcher_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
lean_inc_ref(v___x_69_);
v_searcher_70_ = lean_apply_1(v_inst_59_, v___x_69_);
v___x_71_ = lean_box(0);
v___f_72_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_73_ = lean_apply_7(v_inst_56_, v___x_69_, v___f_66_, lean_box(0), lean_box(0), v_searcher_70_, v___x_71_, v___f_72_);
if (lean_obj_tag(v___x_73_) == 0)
{
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_82_; 
v_val_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_82_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_val_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_nat_add(v_pos_58_, v_val_74_);
lean_dec(v_val_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_78_);
v___x_80_ = v___x_76_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___boxed(lean_object* v_inst_85_, lean_object* v_s_86_, lean_object* v_pos_87_, lean_object* v_inst_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_String_Slice_Pos_find_x3f___redArg(v_inst_85_, v_s_86_, v_pos_87_, v_inst_88_);
lean_dec(v_pos_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f(lean_object* v_00_u03c1_90_, lean_object* v_00_u03c3_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_s_94_, lean_object* v_pos_95_, lean_object* v_pattern_96_, lean_object* v_inst_97_){
_start:
{
lean_object* v_str_98_; lean_object* v_startInclusive_99_; lean_object* v_endExclusive_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_122_; 
v_str_98_ = lean_ctor_get(v_s_94_, 0);
v_startInclusive_99_ = lean_ctor_get(v_s_94_, 1);
v_endExclusive_100_ = lean_ctor_get(v_s_94_, 2);
v_isSharedCheck_122_ = !lean_is_exclusive(v_s_94_);
if (v_isSharedCheck_122_ == 0)
{
v___x_102_ = v_s_94_;
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_endExclusive_100_);
lean_inc(v_startInclusive_99_);
lean_inc(v_str_98_);
lean_dec(v_s_94_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___f_104_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_105_ = lean_nat_add(v_startInclusive_99_, v_pos_95_);
lean_dec(v_startInclusive_99_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_105_);
v___x_107_ = v___x_102_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_str_98_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_endExclusive_100_);
v___x_107_ = v_reuseFailAlloc_121_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v_searcher_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___x_111_; 
lean_inc_ref(v___x_107_);
v_searcher_108_ = lean_apply_1(v_inst_97_, v___x_107_);
v___x_109_ = lean_box(0);
v___f_110_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_111_ = lean_apply_7(v_inst_93_, v___x_107_, v___f_104_, lean_box(0), lean_box(0), v_searcher_108_, v___x_109_, v___f_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
v_val_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_nat_add(v_pos_95_, v_val_112_);
lean_dec(v_val_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___boxed(lean_object* v_00_u03c1_123_, lean_object* v_00_u03c3_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_s_127_, lean_object* v_pos_128_, lean_object* v_pattern_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_String_Slice_Pos_find_x3f(v_00_u03c1_123_, v_00_u03c3_124_, v_inst_125_, v_inst_126_, v_s_127_, v_pos_128_, v_pattern_129_, v_inst_130_);
lean_dec(v_pattern_129_);
lean_dec(v_pos_128_);
lean_dec(v_inst_125_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg(lean_object* v_inst_132_, lean_object* v_s_133_, lean_object* v_pos_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v_str_136_; lean_object* v_startInclusive_137_; lean_object* v_endExclusive_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_155_; 
v_str_136_ = lean_ctor_get(v_s_133_, 0);
v_startInclusive_137_ = lean_ctor_get(v_s_133_, 1);
v_endExclusive_138_ = lean_ctor_get(v_s_133_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_s_133_);
if (v_isSharedCheck_155_ == 0)
{
v___x_140_ = v_s_133_;
v_isShared_141_ = v_isSharedCheck_155_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_endExclusive_138_);
lean_inc(v_startInclusive_137_);
lean_inc(v_str_136_);
lean_dec(v_s_133_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_155_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___f_142_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_143_ = lean_nat_add(v_startInclusive_137_, v_pos_134_);
lean_dec(v_startInclusive_137_);
lean_inc(v_endExclusive_138_);
lean_inc(v___x_143_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_str_136_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_endExclusive_138_);
v___x_145_ = v_reuseFailAlloc_154_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v_searcher_146_; lean_object* v___x_147_; lean_object* v___f_148_; lean_object* v___x_149_; 
lean_inc_ref(v___x_145_);
v_searcher_146_ = lean_apply_1(v_inst_135_, v___x_145_);
v___x_147_ = lean_box(0);
v___f_148_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_149_ = lean_apply_7(v_inst_132_, v___x_145_, v___f_142_, lean_box(0), lean_box(0), v_searcher_146_, v___x_147_, v___f_148_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_nat_sub(v_endExclusive_138_, v___x_143_);
lean_dec(v___x_143_);
lean_dec(v_endExclusive_138_);
v___x_151_ = lean_nat_add(v_pos_134_, v___x_150_);
lean_dec(v___x_150_);
return v___x_151_;
}
else
{
lean_object* v_val_152_; lean_object* v___x_153_; 
lean_dec(v___x_143_);
lean_dec(v_endExclusive_138_);
v_val_152_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_149_, 1);
v___x_153_ = lean_nat_add(v_pos_134_, v_val_152_);
lean_dec(v_val_152_);
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg___boxed(lean_object* v_inst_156_, lean_object* v_s_157_, lean_object* v_pos_158_, lean_object* v_inst_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_String_Slice_Pos_find___redArg(v_inst_156_, v_s_157_, v_pos_158_, v_inst_159_);
lean_dec(v_pos_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find(lean_object* v_00_u03c1_161_, lean_object* v_00_u03c3_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_s_165_, lean_object* v_pos_166_, lean_object* v_pattern_167_, lean_object* v_inst_168_){
_start:
{
lean_object* v_str_169_; lean_object* v_startInclusive_170_; lean_object* v_endExclusive_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_188_; 
v_str_169_ = lean_ctor_get(v_s_165_, 0);
v_startInclusive_170_ = lean_ctor_get(v_s_165_, 1);
v_endExclusive_171_ = lean_ctor_get(v_s_165_, 2);
v_isSharedCheck_188_ = !lean_is_exclusive(v_s_165_);
if (v_isSharedCheck_188_ == 0)
{
v___x_173_ = v_s_165_;
v_isShared_174_ = v_isSharedCheck_188_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_endExclusive_171_);
lean_inc(v_startInclusive_170_);
lean_inc(v_str_169_);
lean_dec(v_s_165_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_188_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___f_175_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_176_ = lean_nat_add(v_startInclusive_170_, v_pos_166_);
lean_dec(v_startInclusive_170_);
lean_inc(v_endExclusive_171_);
lean_inc(v___x_176_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_176_);
v___x_178_ = v___x_173_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_str_169_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_endExclusive_171_);
v___x_178_ = v_reuseFailAlloc_187_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v_searcher_179_; lean_object* v___x_180_; lean_object* v___f_181_; lean_object* v___x_182_; 
lean_inc_ref(v___x_178_);
v_searcher_179_ = lean_apply_1(v_inst_168_, v___x_178_);
v___x_180_ = lean_box(0);
v___f_181_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_182_ = lean_apply_7(v_inst_164_, v___x_178_, v___f_175_, lean_box(0), lean_box(0), v_searcher_179_, v___x_180_, v___f_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_nat_sub(v_endExclusive_171_, v___x_176_);
lean_dec(v___x_176_);
lean_dec(v_endExclusive_171_);
v___x_184_ = lean_nat_add(v_pos_166_, v___x_183_);
lean_dec(v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_val_185_; lean_object* v___x_186_; 
lean_dec(v___x_176_);
lean_dec(v_endExclusive_171_);
v_val_185_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_185_);
lean_dec_ref_known(v___x_182_, 1);
v___x_186_ = lean_nat_add(v_pos_166_, v_val_185_);
lean_dec(v_val_185_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___boxed(lean_object* v_00_u03c1_189_, lean_object* v_00_u03c3_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_s_193_, lean_object* v_pos_194_, lean_object* v_pattern_195_, lean_object* v_inst_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_String_Slice_Pos_find(v_00_u03c1_189_, v_00_u03c3_190_, v_inst_191_, v_inst_192_, v_s_193_, v_pos_194_, v_pattern_195_, v_inst_196_);
lean_dec(v_pattern_195_);
lean_dec(v_pos_194_);
lean_dec(v_inst_191_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___redArg(lean_object* v_inst_198_, lean_object* v_s_199_, lean_object* v_pos_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_searcher_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v___f_202_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_203_ = lean_string_utf8_byte_size(v_s_199_);
lean_inc(v_pos_200_);
v___x_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_204_, 0, v_s_199_);
lean_ctor_set(v___x_204_, 1, v_pos_200_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
lean_inc_ref(v___x_204_);
v_searcher_205_ = lean_apply_1(v_inst_201_, v___x_204_);
v___x_206_ = lean_box(0);
v___f_207_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_208_ = lean_apply_7(v_inst_198_, v___x_204_, v___f_202_, lean_box(0), lean_box(0), v_searcher_205_, v___x_206_, v___f_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_dec(v_pos_200_);
return v___x_206_;
}
else
{
lean_object* v_val_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_val_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_val_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_nat_add(v_pos_200_, v_val_209_);
lean_dec(v_val_209_);
lean_dec(v_pos_200_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
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
LEAN_EXPORT lean_object* l_String_Pos_find_x3f(lean_object* v_00_u03c1_218_, lean_object* v_00_u03c3_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_s_222_, lean_object* v_pos_223_, lean_object* v_pattern_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_searcher_229_; lean_object* v___x_230_; lean_object* v___f_231_; lean_object* v___x_232_; 
v___f_226_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_227_ = lean_string_utf8_byte_size(v_s_222_);
lean_inc(v_pos_223_);
v___x_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_228_, 0, v_s_222_);
lean_ctor_set(v___x_228_, 1, v_pos_223_);
lean_ctor_set(v___x_228_, 2, v___x_227_);
lean_inc_ref(v___x_228_);
v_searcher_229_ = lean_apply_1(v_inst_225_, v___x_228_);
v___x_230_ = lean_box(0);
v___f_231_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_232_ = lean_apply_7(v_inst_221_, v___x_228_, v___f_226_, lean_box(0), lean_box(0), v_searcher_229_, v___x_230_, v___f_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_dec(v_pos_223_);
return v___x_230_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_val_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_nat_add(v_pos_223_, v_val_233_);
lean_dec(v_val_233_);
lean_dec(v_pos_223_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___boxed(lean_object* v_00_u03c1_242_, lean_object* v_00_u03c3_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_s_246_, lean_object* v_pos_247_, lean_object* v_pattern_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_String_Pos_find_x3f(v_00_u03c1_242_, v_00_u03c3_243_, v_inst_244_, v_inst_245_, v_s_246_, v_pos_247_, v_pattern_248_, v_inst_249_);
lean_dec(v_pattern_248_);
lean_dec(v_inst_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_find___redArg(lean_object* v_inst_251_, lean_object* v_s_252_, lean_object* v_pos_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_searcher_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v___f_255_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_256_ = lean_string_utf8_byte_size(v_s_252_);
lean_inc(v_pos_253_);
v___x_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_257_, 0, v_s_252_);
lean_ctor_set(v___x_257_, 1, v_pos_253_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_inc_ref(v___x_257_);
v_searcher_258_ = lean_apply_1(v_inst_254_, v___x_257_);
v___x_259_ = lean_box(0);
v___f_260_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_261_ = lean_apply_7(v_inst_251_, v___x_257_, v___f_255_, lean_box(0), lean_box(0), v_searcher_258_, v___x_259_, v___f_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_nat_sub(v___x_256_, v_pos_253_);
v___x_263_ = lean_nat_add(v_pos_253_, v___x_262_);
lean_dec(v___x_262_);
lean_dec(v_pos_253_);
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_265_; 
v_val_264_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___x_261_, 1);
v___x_265_ = lean_nat_add(v_pos_253_, v_val_264_);
lean_dec(v_val_264_);
lean_dec(v_pos_253_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_find(lean_object* v_00_u03c1_266_, lean_object* v_00_u03c3_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_s_270_, lean_object* v_pos_271_, lean_object* v_pattern_272_, lean_object* v_inst_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_searcher_277_; lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___x_280_; 
v___f_274_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_275_ = lean_string_utf8_byte_size(v_s_270_);
lean_inc(v_pos_271_);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v_s_270_);
lean_ctor_set(v___x_276_, 1, v_pos_271_);
lean_ctor_set(v___x_276_, 2, v___x_275_);
lean_inc_ref(v___x_276_);
v_searcher_277_ = lean_apply_1(v_inst_273_, v___x_276_);
v___x_278_ = lean_box(0);
v___f_279_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_280_ = lean_apply_7(v_inst_269_, v___x_276_, v___f_274_, lean_box(0), lean_box(0), v_searcher_277_, v___x_278_, v___f_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_nat_sub(v___x_275_, v_pos_271_);
v___x_282_ = lean_nat_add(v_pos_271_, v___x_281_);
lean_dec(v___x_281_);
lean_dec(v_pos_271_);
return v___x_282_;
}
else
{
lean_object* v_val_283_; lean_object* v___x_284_; 
v_val_283_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v___x_280_, 1);
v___x_284_ = lean_nat_add(v_pos_271_, v_val_283_);
lean_dec(v_val_283_);
lean_dec(v_pos_271_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_find___boxed(lean_object* v_00_u03c1_285_, lean_object* v_00_u03c3_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_s_289_, lean_object* v_pos_290_, lean_object* v_pattern_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_String_Pos_find(v_00_u03c1_285_, v_00_u03c3_286_, v_inst_287_, v_inst_288_, v_s_289_, v_pos_290_, v_pattern_291_, v_inst_292_);
lean_dec(v_pattern_291_);
lean_dec(v_inst_287_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_String_find_x3f___redArg(lean_object* v_inst_294_, lean_object* v_s_295_, lean_object* v_inst_296_){
_start:
{
lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_searcher_301_; lean_object* v___x_302_; lean_object* v___f_303_; lean_object* v___x_304_; 
v___f_297_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_string_utf8_byte_size(v_s_295_);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v_s_295_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_299_);
lean_inc_ref(v___x_300_);
v_searcher_301_ = lean_apply_1(v_inst_296_, v___x_300_);
v___x_302_ = lean_box(0);
v___f_303_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_304_ = lean_apply_7(v_inst_294_, v___x_300_, v___f_297_, lean_box(0), lean_box(0), v_searcher_301_, v___x_302_, v___f_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
return v___x_302_;
}
else
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_val_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_val_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_find_x3f(lean_object* v_00_u03c1_313_, lean_object* v_00_u03c3_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_s_317_, lean_object* v_pattern_318_, lean_object* v_inst_319_){
_start:
{
lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_searcher_324_; lean_object* v___x_325_; lean_object* v___f_326_; lean_object* v___x_327_; 
v___f_320_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_string_utf8_byte_size(v_s_317_);
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v_s_317_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
lean_inc_ref(v___x_323_);
v_searcher_324_ = lean_apply_1(v_inst_319_, v___x_323_);
v___x_325_ = lean_box(0);
v___f_326_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_327_ = lean_apply_7(v_inst_316_, v___x_323_, v___f_320_, lean_box(0), lean_box(0), v_searcher_324_, v___x_325_, v___f_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
return v___x_325_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
v_val_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_val_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_val_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_find_x3f___boxed(lean_object* v_00_u03c1_336_, lean_object* v_00_u03c3_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_s_340_, lean_object* v_pattern_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_String_find_x3f(v_00_u03c1_336_, v_00_u03c3_337_, v_inst_338_, v_inst_339_, v_s_340_, v_pattern_341_, v_inst_342_);
lean_dec(v_pattern_341_);
lean_dec(v_inst_338_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_String_find___redArg(lean_object* v_inst_344_, lean_object* v_s_345_, lean_object* v_inst_346_){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_searcher_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___x_354_; 
v___f_347_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_string_utf8_byte_size(v_s_345_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v_s_345_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_inc_ref(v___x_350_);
v_searcher_351_ = lean_apply_1(v_inst_346_, v___x_350_);
v___x_352_ = lean_box(0);
v___f_353_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_354_ = lean_apply_7(v_inst_344_, v___x_350_, v___f_347_, lean_box(0), lean_box(0), v_searcher_351_, v___x_352_, v___f_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
return v___x_349_;
}
else
{
lean_object* v_val_355_; 
v_val_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v___x_354_, 1);
return v_val_355_;
}
}
}
LEAN_EXPORT lean_object* l_String_find(lean_object* v_00_u03c1_356_, lean_object* v_00_u03c3_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_s_360_, lean_object* v_pattern_361_, lean_object* v_inst_362_){
_start:
{
lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_searcher_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___x_370_; 
v___f_363_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_string_utf8_byte_size(v_s_360_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v_s_360_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
lean_inc_ref(v___x_366_);
v_searcher_367_ = lean_apply_1(v_inst_362_, v___x_366_);
v___x_368_ = lean_box(0);
v___f_369_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_370_ = lean_apply_7(v_inst_359_, v___x_366_, v___f_363_, lean_box(0), lean_box(0), v_searcher_367_, v___x_368_, v___f_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
return v___x_365_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_370_, 1);
return v_val_371_;
}
}
}
LEAN_EXPORT lean_object* l_String_find___boxed(lean_object* v_00_u03c1_372_, lean_object* v_00_u03c3_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_s_376_, lean_object* v_pattern_377_, lean_object* v_inst_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_find(v_00_u03c1_372_, v_00_u03c3_373_, v_inst_374_, v_inst_375_, v_s_376_, v_pattern_377_, v_inst_378_);
lean_dec(v_pattern_377_);
lean_dec(v_inst_374_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg(lean_object* v_inst_380_, lean_object* v_s_381_, lean_object* v_pos_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v_str_384_; lean_object* v_startInclusive_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_402_; 
v_str_384_ = lean_ctor_get(v_s_381_, 0);
v_startInclusive_385_ = lean_ctor_get(v_s_381_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_s_381_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; 
v_unused_403_ = lean_ctor_get(v_s_381_, 2);
lean_dec(v_unused_403_);
v___x_387_ = v_s_381_;
v_isShared_388_ = v_isSharedCheck_402_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_startInclusive_385_);
lean_inc(v_str_384_);
lean_dec(v_s_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_402_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_nat_add(v_startInclusive_385_, v_pos_382_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 2, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_str_384_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_startInclusive_385_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v___x_389_);
v___x_391_ = v_reuseFailAlloc_401_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; 
v___x_392_ = l_String_Slice_revFind_x3f___redArg(v_inst_380_, v___x_391_, v_inst_383_);
if (lean_obj_tag(v___x_392_) == 0)
{
return v___x_392_;
}
else
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_val_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_val_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg___boxed(lean_object* v_inst_404_, lean_object* v_s_405_, lean_object* v_pos_406_, lean_object* v_inst_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_String_Slice_Pos_revFind_x3f___redArg(v_inst_404_, v_s_405_, v_pos_406_, v_inst_407_);
lean_dec(v_pos_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f(lean_object* v_00_u03c1_409_, lean_object* v_00_u03c3_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_s_413_, lean_object* v_pos_414_, lean_object* v_pattern_415_, lean_object* v_inst_416_){
_start:
{
lean_object* v_str_417_; lean_object* v_startInclusive_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_435_; 
v_str_417_ = lean_ctor_get(v_s_413_, 0);
v_startInclusive_418_ = lean_ctor_get(v_s_413_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_s_413_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_s_413_, 2);
lean_dec(v_unused_436_);
v___x_420_ = v_s_413_;
v_isShared_421_ = v_isSharedCheck_435_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_startInclusive_418_);
lean_inc(v_str_417_);
lean_dec(v_s_413_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_435_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_nat_add(v_startInclusive_418_, v_pos_414_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 2, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_str_417_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_startInclusive_418_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v___x_422_);
v___x_424_ = v_reuseFailAlloc_434_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; 
v___x_425_ = l_String_Slice_revFind_x3f___redArg(v_inst_412_, v___x_424_, v_inst_416_);
if (lean_obj_tag(v___x_425_) == 0)
{
return v___x_425_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_val_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_val_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___boxed(lean_object* v_00_u03c1_437_, lean_object* v_00_u03c3_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_s_441_, lean_object* v_pos_442_, lean_object* v_pattern_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_String_Slice_Pos_revFind_x3f(v_00_u03c1_437_, v_00_u03c3_438_, v_inst_439_, v_inst_440_, v_s_441_, v_pos_442_, v_pattern_443_, v_inst_444_);
lean_dec(v_pattern_443_);
lean_dec(v_pos_442_);
lean_dec(v_inst_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___redArg(lean_object* v_inst_446_, lean_object* v_s_447_, lean_object* v_pos_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v_s_447_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_ctor_set(v___x_451_, 2, v_pos_448_);
v___x_452_ = l_String_Slice_revFind_x3f___redArg(v_inst_446_, v___x_451_, v_inst_449_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_val_454_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_452_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v___x_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_val_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f(lean_object* v_00_u03c1_462_, lean_object* v_00_u03c3_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_s_466_, lean_object* v_pos_467_, lean_object* v_pattern_468_, lean_object* v_inst_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_471_, 0, v_s_466_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
lean_ctor_set(v___x_471_, 2, v_pos_467_);
v___x_472_ = l_String_Slice_revFind_x3f___redArg(v_inst_465_, v___x_471_, v_inst_469_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_val_474_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_472_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_val_474_);
lean_dec(v___x_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_val_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___boxed(lean_object* v_00_u03c1_482_, lean_object* v_00_u03c3_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_s_486_, lean_object* v_pos_487_, lean_object* v_pattern_488_, lean_object* v_inst_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_String_Pos_revFind_x3f(v_00_u03c1_482_, v_00_u03c3_483_, v_inst_484_, v_inst_485_, v_s_486_, v_pos_487_, v_pattern_488_, v_inst_489_);
lean_dec(v_pattern_488_);
lean_dec(v_inst_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f___redArg(lean_object* v_inst_491_, lean_object* v_s_492_, lean_object* v_inst_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_string_utf8_byte_size(v_s_492_);
v___x_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_496_, 0, v_s_492_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v___x_497_ = l_String_Slice_revFind_x3f___redArg(v_inst_491_, v___x_496_, v_inst_493_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_val_499_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_497_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_val_499_);
lean_dec(v___x_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_val_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f(lean_object* v_00_u03c1_507_, lean_object* v_00_u03c3_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_s_511_, lean_object* v_pattern_512_, lean_object* v_inst_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_string_utf8_byte_size(v_s_511_);
v___x_516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_516_, 0, v_s_511_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_515_);
v___x_517_ = l_String_Slice_revFind_x3f___redArg(v_inst_510_, v___x_516_, v_inst_513_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = lean_box(0);
return v___x_518_;
}
else
{
lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_val_519_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_517_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v___x_517_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_val_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f___boxed(lean_object* v_00_u03c1_527_, lean_object* v_00_u03c3_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_s_531_, lean_object* v_pattern_532_, lean_object* v_inst_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_String_revFind_x3f(v_00_u03c1_527_, v_00_u03c3_528_, v_inst_529_, v_inst_530_, v_s_531_, v_pattern_532_, v_inst_533_);
lean_dec(v_pattern_532_);
lean_dec(v_inst_529_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(lean_object* v___x_535_, lean_object* v_s_536_, uint32_t v_c_537_, lean_object* v_a_538_, lean_object* v_b_539_){
_start:
{
uint8_t v_decide_540_; 
v_decide_540_ = lean_nat_dec_eq(v_a_538_, v___x_535_);
if (v_decide_540_ == 0)
{
uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_string_utf8_get_fast(v_s_536_, v_a_538_);
v___x_542_ = lean_uint32_dec_eq(v___x_541_, v_c_537_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_string_utf8_next_fast(v_s_536_, v_a_538_);
lean_dec(v_a_538_);
v_a_538_ = v___x_544_;
v_b_539_ = v___x_543_;
goto _start;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_a_538_);
return v___x_546_;
}
}
else
{
lean_dec(v_a_538_);
lean_inc(v_b_539_);
return v_b_539_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg___boxed(lean_object* v___x_547_, lean_object* v_s_548_, lean_object* v_c_549_, lean_object* v_a_550_, lean_object* v_b_551_){
_start:
{
uint32_t v_c_boxed_552_; lean_object* v_res_553_; 
v_c_boxed_552_ = lean_unbox_uint32(v_c_549_);
lean_dec(v_c_549_);
v_res_553_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_547_, v_s_548_, v_c_boxed_552_, v_a_550_, v_b_551_);
lean_dec(v_b_551_);
lean_dec_ref(v_s_548_);
lean_dec(v___x_547_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* lean_string_posof(lean_object* v_s_554_, uint32_t v_c_555_){
_start:
{
lean_object* v_searcher_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_searcher_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_string_utf8_byte_size(v_s_554_);
v___x_558_ = lean_box(0);
v___x_559_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_557_, v_s_554_, v_c_555_, v_searcher_556_, v___x_558_);
lean_dec_ref(v_s_554_);
if (lean_obj_tag(v___x_559_) == 0)
{
return v___x_557_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_559_, 1);
return v_val_560_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object* v_s_561_, lean_object* v_c_562_){
_start:
{
uint32_t v_c_boxed_563_; lean_object* v_res_564_; 
v_c_boxed_563_ = lean_unbox_uint32(v_c_562_);
lean_dec(v_c_562_);
v_res_564_ = lean_string_posof(v_s_561_, v_c_boxed_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v_s_567_, uint32_t v_c_568_, lean_object* v_inst_569_, lean_object* v_R_570_, lean_object* v_a_571_, lean_object* v_b_572_, lean_object* v_c_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_565_, v_s_567_, v_c_568_, v_a_571_, v_b_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___boxed(lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v_s_577_, lean_object* v_c_578_, lean_object* v_inst_579_, lean_object* v_R_580_, lean_object* v_a_581_, lean_object* v_b_582_, lean_object* v_c_583_){
_start:
{
uint32_t v_c_boxed_584_; lean_object* v_res_585_; 
v_c_boxed_584_ = lean_unbox_uint32(v_c_578_);
lean_dec(v_c_578_);
v_res_585_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(v___x_575_, v___x_576_, v_s_577_, v_c_boxed_584_, v_inst_579_, v_R_580_, v_a_581_, v_b_582_, v_c_583_);
lean_dec(v_b_582_);
lean_dec_ref(v_s_577_);
lean_dec_ref(v___x_576_);
lean_dec(v___x_575_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_String_split___redArg(lean_object* v_s_586_, lean_object* v_inst_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_string_utf8_byte_size(v_s_586_);
v___x_590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_590_, 0, v_s_586_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_589_);
v___x_591_ = l_String_Slice_splitToSubslice___redArg(v___x_590_, v_inst_587_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_String_split(lean_object* v_00_u03c1_592_, lean_object* v_00_u03c3_593_, lean_object* v_inst_594_, lean_object* v_s_595_, lean_object* v_pat_596_, lean_object* v_inst_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_string_utf8_byte_size(v_s_595_);
v___x_600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_600_, 0, v_s_595_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
lean_ctor_set(v___x_600_, 2, v___x_599_);
v___x_601_ = l_String_Slice_splitToSubslice___redArg(v___x_600_, v_inst_597_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object* v_00_u03c1_602_, lean_object* v_00_u03c3_603_, lean_object* v_inst_604_, lean_object* v_s_605_, lean_object* v_pat_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_String_split(v_00_u03c1_602_, v_00_u03c3_603_, v_inst_604_, v_s_605_, v_pat_606_, v_inst_607_);
lean_dec(v_pat_606_);
lean_dec(v_inst_604_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive___redArg(lean_object* v_s_609_, lean_object* v_inst_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_string_utf8_byte_size(v_s_609_);
v___x_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_613_, 0, v_s_609_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
lean_ctor_set(v___x_613_, 2, v___x_612_);
v___x_614_ = l_String_Slice_splitInclusive___redArg(v___x_613_, v_inst_610_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive(lean_object* v_00_u03c1_615_, lean_object* v_00_u03c3_616_, lean_object* v_s_617_, lean_object* v_pat_618_, lean_object* v_inst_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_string_utf8_byte_size(v_s_617_);
v___x_622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_622_, 0, v_s_617_);
lean_ctor_set(v___x_622_, 1, v___x_620_);
lean_ctor_set(v___x_622_, 2, v___x_621_);
v___x_623_ = l_String_Slice_splitInclusive___redArg(v___x_622_, v_inst_619_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive___boxed(lean_object* v_00_u03c1_624_, lean_object* v_00_u03c3_625_, lean_object* v_s_626_, lean_object* v_pat_627_, lean_object* v_inst_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_String_splitInclusive(v_00_u03c1_624_, v_00_u03c3_625_, v_s_626_, v_pat_627_, v_inst_628_);
lean_dec(v_pat_627_);
return v_res_629_;
}
}
LEAN_EXPORT uint8_t l_String_contains___redArg(lean_object* v_inst_630_, lean_object* v_s_631_, lean_object* v_inst_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_string_utf8_byte_size(v_s_631_);
v___x_635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_635_, 0, v_s_631_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
v___x_636_ = l_String_Slice_contains___redArg(v_inst_630_, v___x_635_, v_inst_632_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_String_contains___redArg___boxed(lean_object* v_inst_637_, lean_object* v_s_638_, lean_object* v_inst_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_String_contains___redArg(v_inst_637_, v_s_638_, v_inst_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT uint8_t l_String_contains(lean_object* v_00_u03c1_642_, lean_object* v_00_u03c3_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_s_646_, lean_object* v_pat_647_, lean_object* v_inst_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_string_utf8_byte_size(v_s_646_);
v___x_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_651_, 0, v_s_646_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
v___x_652_ = l_String_Slice_contains___redArg(v_inst_645_, v___x_651_, v_inst_648_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object* v_00_u03c1_653_, lean_object* v_00_u03c3_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_s_657_, lean_object* v_pat_658_, lean_object* v_inst_659_){
_start:
{
uint8_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_String_contains(v_00_u03c1_653_, v_00_u03c3_654_, v_inst_655_, v_inst_656_, v_s_657_, v_pat_658_, v_inst_659_);
lean_dec(v_pat_658_);
lean_dec(v_inst_655_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(lean_object* v_s_662_, uint32_t v_c_663_, lean_object* v_a_664_, uint8_t v_b_665_){
_start:
{
lean_object* v_str_666_; lean_object* v_startInclusive_667_; lean_object* v_endExclusive_668_; lean_object* v___x_669_; uint8_t v_decide_670_; 
v_str_666_ = lean_ctor_get(v_s_662_, 0);
v_startInclusive_667_ = lean_ctor_get(v_s_662_, 1);
v_endExclusive_668_ = lean_ctor_get(v_s_662_, 2);
v___x_669_ = lean_nat_sub(v_endExclusive_668_, v_startInclusive_667_);
v_decide_670_ = lean_nat_dec_eq(v_a_664_, v___x_669_);
lean_dec(v___x_669_);
if (v_decide_670_ == 0)
{
lean_object* v___x_671_; uint32_t v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_nat_add(v_startInclusive_667_, v_a_664_);
lean_dec(v_a_664_);
v___x_672_ = lean_string_utf8_get_fast(v_str_666_, v___x_671_);
v___x_673_ = lean_uint32_dec_eq(v___x_672_, v_c_663_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_string_utf8_next_fast(v_str_666_, v___x_671_);
lean_dec(v___x_671_);
v___x_675_ = lean_nat_sub(v___x_674_, v_startInclusive_667_);
v_a_664_ = v___x_675_;
v_b_665_ = v___x_673_;
goto _start;
}
else
{
lean_dec(v___x_671_);
return v___x_673_;
}
}
else
{
lean_dec(v_a_664_);
return v_b_665_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg___boxed(lean_object* v_s_677_, lean_object* v_c_678_, lean_object* v_a_679_, lean_object* v_b_680_){
_start:
{
uint32_t v_c_boxed_681_; uint8_t v_b_boxed_682_; uint8_t v_res_683_; lean_object* v_r_684_; 
v_c_boxed_681_ = lean_unbox_uint32(v_c_678_);
lean_dec(v_c_678_);
v_b_boxed_682_ = lean_unbox(v_b_680_);
v_res_683_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_677_, v_c_boxed_681_, v_a_679_, v_b_boxed_682_);
lean_dec_ref(v_s_677_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(uint32_t v_c_685_, lean_object* v_s_686_){
_start:
{
lean_object* v_searcher_687_; uint8_t v___x_688_; uint8_t v___x_689_; 
v_searcher_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = 0;
v___x_689_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_686_, v_c_685_, v_searcher_687_, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0___boxed(lean_object* v_c_690_, lean_object* v_s_691_){
_start:
{
uint32_t v_c_boxed_692_; uint8_t v_res_693_; lean_object* v_r_694_; 
v_c_boxed_692_ = lean_unbox_uint32(v_c_690_);
lean_dec(v_c_690_);
v_res_693_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(v_c_boxed_692_, v_s_691_);
lean_dec_ref(v_s_691_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t lean_string_contains(lean_object* v_s_695_, uint32_t v_c_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_string_utf8_byte_size(v_s_695_);
v___x_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_699_, 0, v_s_695_);
lean_ctor_set(v___x_699_, 1, v___x_697_);
lean_ctor_set(v___x_699_, 2, v___x_698_);
v___x_700_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(v_c_696_, v___x_699_);
lean_dec_ref_known(v___x_699_, 3);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object* v_s_701_, lean_object* v_c_702_){
_start:
{
uint32_t v_c_boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v_c_boxed_703_ = lean_unbox_uint32(v_c_702_);
lean_dec(v_c_702_);
v_res_704_ = lean_string_contains(v_s_701_, v_c_boxed_703_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(lean_object* v_s_706_, uint32_t v_c_707_, lean_object* v_inst_708_, lean_object* v_R_709_, lean_object* v_a_710_, uint8_t v_b_711_, lean_object* v_c_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_706_, v_c_707_, v_a_710_, v_b_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___boxed(lean_object* v_s_714_, lean_object* v_c_715_, lean_object* v_inst_716_, lean_object* v_R_717_, lean_object* v_a_718_, lean_object* v_b_719_, lean_object* v_c_720_){
_start:
{
uint32_t v_c_boxed_721_; uint8_t v_b_boxed_722_; uint8_t v_res_723_; lean_object* v_r_724_; 
v_c_boxed_721_ = lean_unbox_uint32(v_c_715_);
lean_dec(v_c_715_);
v_b_boxed_722_ = lean_unbox(v_b_719_);
v_res_723_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(v_s_714_, v_c_boxed_721_, v_inst_716_, v_R_717_, v_a_718_, v_b_boxed_722_, v_c_720_);
lean_dec_ref(v_s_714_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT uint8_t l_String_any___redArg(lean_object* v_inst_725_, lean_object* v_s_726_, lean_object* v_inst_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_string_utf8_byte_size(v_s_726_);
v___x_730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_730_, 0, v_s_726_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_729_);
v___x_731_ = l_String_Slice_contains___redArg(v_inst_725_, v___x_730_, v_inst_727_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_String_any___redArg___boxed(lean_object* v_inst_732_, lean_object* v_s_733_, lean_object* v_inst_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_String_any___redArg(v_inst_732_, v_s_733_, v_inst_734_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT uint8_t l_String_any(lean_object* v_00_u03c1_737_, lean_object* v_00_u03c3_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_s_741_, lean_object* v_pat_742_, lean_object* v_inst_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_string_utf8_byte_size(v_s_741_);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v_s_741_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
lean_ctor_set(v___x_746_, 2, v___x_745_);
v___x_747_ = l_String_Slice_contains___redArg(v_inst_740_, v___x_746_, v_inst_743_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object* v_00_u03c1_748_, lean_object* v_00_u03c3_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_s_752_, lean_object* v_pat_753_, lean_object* v_inst_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_String_any(v_00_u03c1_748_, v_00_u03c3_749_, v_inst_750_, v_inst_751_, v_s_752_, v_pat_753_, v_inst_754_);
lean_dec(v_pat_753_);
lean_dec(v_inst_750_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(lean_object* v_s_757_, lean_object* v_p_758_, lean_object* v_a_759_, uint8_t v_b_760_){
_start:
{
lean_object* v_str_761_; lean_object* v_startInclusive_762_; lean_object* v_endExclusive_763_; lean_object* v___x_764_; uint8_t v_decide_765_; 
v_str_761_ = lean_ctor_get(v_s_757_, 0);
v_startInclusive_762_ = lean_ctor_get(v_s_757_, 1);
v_endExclusive_763_ = lean_ctor_get(v_s_757_, 2);
v___x_764_ = lean_nat_sub(v_endExclusive_763_, v_startInclusive_762_);
v_decide_765_ = lean_nat_dec_eq(v_a_759_, v___x_764_);
lean_dec(v___x_764_);
if (v_decide_765_ == 0)
{
lean_object* v___x_766_; uint32_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_766_ = lean_nat_add(v_startInclusive_762_, v_a_759_);
lean_dec(v_a_759_);
v___x_767_ = lean_string_utf8_get_fast(v_str_761_, v___x_766_);
v___x_768_ = lean_box_uint32(v___x_767_);
lean_inc_ref(v_p_758_);
v___x_769_ = lean_apply_1(v_p_758_, v___x_768_);
v___x_770_ = lean_unbox(v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_string_utf8_next_fast(v_str_761_, v___x_766_);
lean_dec(v___x_766_);
v___x_772_ = lean_nat_sub(v___x_771_, v_startInclusive_762_);
v___x_773_ = lean_unbox(v___x_769_);
v_a_759_ = v___x_772_;
v_b_760_ = v___x_773_;
goto _start;
}
else
{
uint8_t v___x_775_; 
lean_dec(v___x_766_);
lean_dec_ref(v_p_758_);
v___x_775_ = lean_unbox(v___x_769_);
return v___x_775_;
}
}
else
{
lean_dec(v_a_759_);
lean_dec_ref(v_p_758_);
return v_b_760_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg___boxed(lean_object* v_s_776_, lean_object* v_p_777_, lean_object* v_a_778_, lean_object* v_b_779_){
_start:
{
uint8_t v_b_boxed_780_; uint8_t v_res_781_; lean_object* v_r_782_; 
v_b_boxed_780_ = lean_unbox(v_b_779_);
v_res_781_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(v_s_776_, v_p_777_, v_a_778_, v_b_boxed_780_);
lean_dec_ref(v_s_776_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0(lean_object* v_p_783_, lean_object* v_s_784_){
_start:
{
lean_object* v_searcher_785_; uint8_t v___x_786_; uint8_t v___x_787_; 
v_searcher_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = 0;
v___x_787_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(v_s_784_, v_p_783_, v_searcher_785_, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0___boxed(lean_object* v_p_788_, lean_object* v_s_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0(v_p_788_, v_s_789_);
lean_dec_ref(v_s_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t lean_string_any(lean_object* v_s_792_, lean_object* v_p_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_string_utf8_byte_size(v_s_792_);
v___x_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_796_, 0, v_s_792_);
lean_ctor_set(v___x_796_, 1, v___x_794_);
lean_ctor_set(v___x_796_, 2, v___x_795_);
v___x_797_ = l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0(v_p_793_, v___x_796_);
lean_dec_ref_known(v___x_796_, 3);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object* v_s_798_, lean_object* v_p_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = lean_string_any(v_s_798_, v_p_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0(lean_object* v_s_802_, lean_object* v_p_803_, lean_object* v_inst_804_, lean_object* v_R_805_, lean_object* v_a_806_, uint8_t v_b_807_, lean_object* v_c_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(v_s_802_, v_p_803_, v_a_806_, v_b_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___boxed(lean_object* v_s_810_, lean_object* v_p_811_, lean_object* v_inst_812_, lean_object* v_R_813_, lean_object* v_a_814_, lean_object* v_b_815_, lean_object* v_c_816_){
_start:
{
uint8_t v_b_boxed_817_; uint8_t v_res_818_; lean_object* v_r_819_; 
v_b_boxed_817_ = lean_unbox(v_b_815_);
v_res_818_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0(v_s_810_, v_p_811_, v_inst_812_, v_R_813_, v_a_814_, v_b_boxed_817_, v_c_816_);
lean_dec_ref(v_s_810_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l_String_isNat(lean_object* v_s_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_string_utf8_byte_size(v_s_820_);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v_s_820_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
v___x_824_ = l_String_Slice_isNat(v___x_823_);
lean_dec_ref_known(v___x_823_, 3);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object* v_s_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_String_isNat(v_s_825_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object* v_s_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_string_utf8_byte_size(v_s_828_);
v___x_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_831_, 0, v_s_828_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
v___x_832_ = l_String_Slice_toNat_x3f(v___x_831_);
lean_dec_ref_known(v___x_831_, 3);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object* v_s_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_string_utf8_byte_size(v_s_833_);
v___x_836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_836_, 0, v_s_833_);
lean_ctor_set(v___x_836_, 1, v___x_834_);
lean_ctor_set(v___x_836_, 2, v___x_835_);
v___x_837_ = l_String_Slice_toNat_x21(v___x_836_);
lean_dec_ref_known(v___x_836_, 3);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object* v_s_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_string_utf8_byte_size(v_s_838_);
v___x_841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_841_, 0, v_s_838_);
lean_ctor_set(v___x_841_, 1, v___x_839_);
lean_ctor_set(v___x_841_, 2, v___x_840_);
v___x_842_ = l_String_Slice_toInt_x3f(v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT uint8_t l_String_isInt(lean_object* v_s_843_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_string_utf8_byte_size(v_s_843_);
v___x_846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_846_, 0, v_s_843_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
lean_ctor_set(v___x_846_, 2, v___x_845_);
v___x_847_ = l_String_Slice_isInt(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object* v_s_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_String_isInt(v_s_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object* v_s_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_string_utf8_byte_size(v_s_852_);
v___x_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_855_, 0, v_s_852_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
v___x_856_ = l_String_Slice_toInt_x3f(v___x_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = l_Int_instInhabited;
v___x_858_ = ((lean_object*)(l_String_toInt_x21___closed__0));
v___x_859_ = l_panic___redArg(v___x_857_, v___x_858_);
return v___x_859_;
}
else
{
lean_object* v_val_860_; 
v_val_860_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v___x_856_, 1);
return v_val_860_;
}
}
}
LEAN_EXPORT lean_object* l_String_front_x3f(lean_object* v_s_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_string_utf8_byte_size(v_s_861_);
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v_s_861_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
lean_ctor_set(v___x_864_, 2, v___x_863_);
v___x_865_ = l_String_Slice_Pos_get_x3f(v___x_864_, v___x_862_);
lean_dec_ref_known(v___x_864_, 3);
return v___x_865_;
}
}
LEAN_EXPORT uint32_t l_String_front(lean_object* v_s_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_string_utf8_byte_size(v_s_866_);
v___x_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_869_, 0, v_s_866_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
v___x_870_ = l_String_Slice_Pos_get_x3f(v___x_869_, v___x_867_);
lean_dec_ref_known(v___x_869_, 3);
if (lean_obj_tag(v___x_870_) == 0)
{
uint32_t v___x_871_; 
v___x_871_ = 65;
return v___x_871_;
}
else
{
lean_object* v_val_872_; uint32_t v___x_873_; 
v_val_872_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v___x_870_, 1);
v___x_873_ = lean_unbox_uint32(v_val_872_);
lean_dec(v_val_872_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object* v_s_874_){
_start:
{
uint32_t v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l_String_front(v_s_874_);
v_r_876_ = lean_box_uint32(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT uint32_t lean_string_front(lean_object* v_s_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_string_utf8_byte_size(v_s_877_);
v___x_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_880_, 0, v_s_877_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
v___x_881_ = l_String_Slice_Pos_get_x3f(v___x_880_, v___x_878_);
lean_dec_ref_known(v___x_880_, 3);
if (lean_obj_tag(v___x_881_) == 0)
{
uint32_t v___x_882_; 
v___x_882_ = 65;
return v___x_882_;
}
else
{
lean_object* v_val_883_; uint32_t v___x_884_; 
v_val_883_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v___x_881_, 1);
v___x_884_ = lean_unbox_uint32(v_val_883_);
lean_dec(v_val_883_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object* v_s_885_){
_start:
{
uint32_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = lean_string_front(v_s_885_);
v_r_887_ = lean_box_uint32(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT lean_object* l_String_back_x3f(lean_object* v_s_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_string_utf8_byte_size(v_s_888_);
v___x_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_891_, 0, v_s_888_);
lean_ctor_set(v___x_891_, 1, v___x_889_);
lean_ctor_set(v___x_891_, 2, v___x_890_);
v___x_892_ = l_String_Slice_Pos_prev_x3f(v___x_891_, v___x_890_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; 
lean_dec_ref_known(v___x_891_, 3);
v___x_893_ = lean_box(0);
return v___x_893_;
}
else
{
lean_object* v_val_894_; lean_object* v___x_895_; 
v_val_894_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v___x_892_, 1);
v___x_895_ = l_String_Slice_Pos_get_x3f(v___x_891_, v_val_894_);
lean_dec(v_val_894_);
lean_dec_ref_known(v___x_891_, 3);
return v___x_895_;
}
}
}
LEAN_EXPORT uint32_t l_String_back(lean_object* v_s_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_string_utf8_byte_size(v_s_896_);
v___x_899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_899_, 0, v_s_896_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
lean_ctor_set(v___x_899_, 2, v___x_898_);
v___x_900_ = l_String_Slice_Pos_prev_x3f(v___x_899_, v___x_898_);
if (lean_obj_tag(v___x_900_) == 0)
{
uint32_t v___x_901_; 
lean_dec_ref_known(v___x_899_, 3);
v___x_901_ = 65;
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_903_; 
v_val_902_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v___x_900_, 1);
v___x_903_ = l_String_Slice_Pos_get_x3f(v___x_899_, v_val_902_);
lean_dec(v_val_902_);
lean_dec_ref_known(v___x_899_, 3);
if (lean_obj_tag(v___x_903_) == 0)
{
uint32_t v___x_904_; 
v___x_904_ = 65;
return v___x_904_;
}
else
{
lean_object* v_val_905_; uint32_t v___x_906_; 
v_val_905_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v___x_903_, 1);
v___x_906_ = lean_unbox_uint32(v_val_905_);
lean_dec(v_val_905_);
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object* v_s_907_){
_start:
{
uint32_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_String_back(v_s_907_);
v_r_909_ = lean_box_uint32(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_String_lines(lean_object* v_s_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_string_utf8_byte_size(v_s_910_);
v___x_913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_913_, 0, v_s_910_);
lean_ctor_set(v___x_913_, 1, v___x_911_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
v___x_914_ = l_String_Slice_lines(v___x_913_);
lean_dec_ref_known(v___x_913_, 3);
return v___x_914_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice_Numeric(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Numeric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Slice_Pattern(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice_Numeric(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice_Numeric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Search(builtin);
}
#ifdef __cplusplus
}
#endif
