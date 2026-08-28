// Lean compiler output
// Module: Init.Data.String.Search
// Imports: public import Init.Data.String.Slice import Init.Data.Iterators.Consumers.Collect
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
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_455_; 
v_val_454_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_val_454_);
lean_dec_ref_known(v___x_452_, 1);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_val_454_);
return v___x_455_;
}
}
else
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_val_456_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_452_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v___x_452_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_val_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f(lean_object* v_00_u03c1_464_, lean_object* v_00_u03c3_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_s_468_, lean_object* v_pos_469_, lean_object* v_pattern_470_, lean_object* v_inst_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_473_, 0, v_s_468_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_ctor_set(v___x_473_, 2, v_pos_469_);
v___x_474_ = l_String_Slice_revFind_x3f___redArg(v_inst_467_, v___x_473_, v_inst_471_);
if (lean_obj_tag(v___x_474_) == 0)
{
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_box(0);
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_477_; 
v_val_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v___x_474_, 1);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_val_476_);
return v___x_477_;
}
}
else
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_val_478_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_474_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v___x_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_val_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___boxed(lean_object* v_00_u03c1_486_, lean_object* v_00_u03c3_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_s_490_, lean_object* v_pos_491_, lean_object* v_pattern_492_, lean_object* v_inst_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_String_Pos_revFind_x3f(v_00_u03c1_486_, v_00_u03c3_487_, v_inst_488_, v_inst_489_, v_s_490_, v_pos_491_, v_pattern_492_, v_inst_493_);
lean_dec(v_pattern_492_);
lean_dec(v_inst_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f___redArg(lean_object* v_inst_495_, lean_object* v_s_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_string_utf8_byte_size(v_s_496_);
v___x_500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_500_, 0, v_s_496_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
v___x_501_ = l_String_Slice_revFind_x3f___redArg(v_inst_495_, v___x_500_, v_inst_497_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_val_503_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_501_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v___x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_val_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f(lean_object* v_00_u03c1_511_, lean_object* v_00_u03c3_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_s_515_, lean_object* v_pattern_516_, lean_object* v_inst_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_string_utf8_byte_size(v_s_515_);
v___x_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_520_, 0, v_s_515_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = l_String_Slice_revFind_x3f___redArg(v_inst_514_, v___x_520_, v_inst_517_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_val_523_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_val_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f___boxed(lean_object* v_00_u03c1_531_, lean_object* v_00_u03c3_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_s_535_, lean_object* v_pattern_536_, lean_object* v_inst_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_String_revFind_x3f(v_00_u03c1_531_, v_00_u03c3_532_, v_inst_533_, v_inst_534_, v_s_535_, v_pattern_536_, v_inst_537_);
lean_dec(v_pattern_536_);
lean_dec(v_inst_533_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(lean_object* v___x_539_, lean_object* v_s_540_, uint32_t v_c_541_, lean_object* v_a_542_, lean_object* v_b_543_){
_start:
{
uint8_t v_decide_544_; 
v_decide_544_ = lean_nat_dec_eq(v_a_542_, v___x_539_);
if (v_decide_544_ == 0)
{
uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_string_utf8_get_fast(v_s_540_, v_a_542_);
v___x_546_ = lean_uint32_dec_eq(v___x_545_, v_c_541_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(0);
v___x_548_ = lean_string_utf8_next_fast(v_s_540_, v_a_542_);
lean_dec(v_a_542_);
v_a_542_ = v___x_548_;
v_b_543_ = v___x_547_;
goto _start;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v_a_542_);
return v___x_550_;
}
}
else
{
lean_dec(v_a_542_);
lean_inc(v_b_543_);
return v_b_543_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg___boxed(lean_object* v___x_551_, lean_object* v_s_552_, lean_object* v_c_553_, lean_object* v_a_554_, lean_object* v_b_555_){
_start:
{
uint32_t v_c_boxed_556_; lean_object* v_res_557_; 
v_c_boxed_556_ = lean_unbox_uint32(v_c_553_);
lean_dec(v_c_553_);
v_res_557_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_551_, v_s_552_, v_c_boxed_556_, v_a_554_, v_b_555_);
lean_dec(v_b_555_);
lean_dec_ref(v_s_552_);
lean_dec(v___x_551_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* lean_string_posof(lean_object* v_s_558_, uint32_t v_c_559_){
_start:
{
lean_object* v_searcher_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_searcher_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_string_utf8_byte_size(v_s_558_);
v___x_562_ = lean_box(0);
v___x_563_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_561_, v_s_558_, v_c_559_, v_searcher_560_, v___x_562_);
lean_dec_ref(v_s_558_);
if (lean_obj_tag(v___x_563_) == 0)
{
return v___x_561_;
}
else
{
lean_object* v_val_564_; 
v_val_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v___x_563_, 1);
return v_val_564_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object* v_s_565_, lean_object* v_c_566_){
_start:
{
uint32_t v_c_boxed_567_; lean_object* v_res_568_; 
v_c_boxed_567_ = lean_unbox_uint32(v_c_566_);
lean_dec(v_c_566_);
v_res_568_ = lean_string_posof(v_s_565_, v_c_boxed_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v_s_571_, uint32_t v_c_572_, lean_object* v_inst_573_, lean_object* v_R_574_, lean_object* v_a_575_, lean_object* v_b_576_, lean_object* v_c_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_569_, v_s_571_, v_c_572_, v_a_575_, v_b_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___boxed(lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v_s_581_, lean_object* v_c_582_, lean_object* v_inst_583_, lean_object* v_R_584_, lean_object* v_a_585_, lean_object* v_b_586_, lean_object* v_c_587_){
_start:
{
uint32_t v_c_boxed_588_; lean_object* v_res_589_; 
v_c_boxed_588_ = lean_unbox_uint32(v_c_582_);
lean_dec(v_c_582_);
v_res_589_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(v___x_579_, v___x_580_, v_s_581_, v_c_boxed_588_, v_inst_583_, v_R_584_, v_a_585_, v_b_586_, v_c_587_);
lean_dec(v_b_586_);
lean_dec_ref(v_s_581_);
lean_dec_ref(v___x_580_);
lean_dec(v___x_579_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_String_split___redArg(lean_object* v_s_590_, lean_object* v_inst_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_string_utf8_byte_size(v_s_590_);
v___x_594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_594_, 0, v_s_590_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_593_);
v___x_595_ = l_String_Slice_splitToSubslice___redArg(v___x_594_, v_inst_591_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_String_split(lean_object* v_00_u03c1_596_, lean_object* v_00_u03c3_597_, lean_object* v_inst_598_, lean_object* v_s_599_, lean_object* v_pat_600_, lean_object* v_inst_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_string_utf8_byte_size(v_s_599_);
v___x_604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_604_, 0, v_s_599_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_603_);
v___x_605_ = l_String_Slice_splitToSubslice___redArg(v___x_604_, v_inst_601_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object* v_00_u03c1_606_, lean_object* v_00_u03c3_607_, lean_object* v_inst_608_, lean_object* v_s_609_, lean_object* v_pat_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_String_split(v_00_u03c1_606_, v_00_u03c3_607_, v_inst_608_, v_s_609_, v_pat_610_, v_inst_611_);
lean_dec(v_pat_610_);
lean_dec(v_inst_608_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive___redArg(lean_object* v_s_613_, lean_object* v_inst_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_string_utf8_byte_size(v_s_613_);
v___x_617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_617_, 0, v_s_613_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
v___x_618_ = l_String_Slice_splitInclusive___redArg(v___x_617_, v_inst_614_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive(lean_object* v_00_u03c1_619_, lean_object* v_00_u03c3_620_, lean_object* v_s_621_, lean_object* v_pat_622_, lean_object* v_inst_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_string_utf8_byte_size(v_s_621_);
v___x_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_626_, 0, v_s_621_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
v___x_627_ = l_String_Slice_splitInclusive___redArg(v___x_626_, v_inst_623_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive___boxed(lean_object* v_00_u03c1_628_, lean_object* v_00_u03c3_629_, lean_object* v_s_630_, lean_object* v_pat_631_, lean_object* v_inst_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_String_splitInclusive(v_00_u03c1_628_, v_00_u03c3_629_, v_s_630_, v_pat_631_, v_inst_632_);
lean_dec(v_pat_631_);
return v_res_633_;
}
}
LEAN_EXPORT uint8_t l_String_contains___redArg(lean_object* v_inst_634_, lean_object* v_s_635_, lean_object* v_inst_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_string_utf8_byte_size(v_s_635_);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v_s_635_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
v___x_640_ = l_String_Slice_contains___redArg(v_inst_634_, v___x_639_, v_inst_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_String_contains___redArg___boxed(lean_object* v_inst_641_, lean_object* v_s_642_, lean_object* v_inst_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_String_contains___redArg(v_inst_641_, v_s_642_, v_inst_643_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT uint8_t l_String_contains(lean_object* v_00_u03c1_646_, lean_object* v_00_u03c3_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_s_650_, lean_object* v_pat_651_, lean_object* v_inst_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_string_utf8_byte_size(v_s_650_);
v___x_655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_655_, 0, v_s_650_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_654_);
v___x_656_ = l_String_Slice_contains___redArg(v_inst_649_, v___x_655_, v_inst_652_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object* v_00_u03c1_657_, lean_object* v_00_u03c3_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_s_661_, lean_object* v_pat_662_, lean_object* v_inst_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_String_contains(v_00_u03c1_657_, v_00_u03c3_658_, v_inst_659_, v_inst_660_, v_s_661_, v_pat_662_, v_inst_663_);
lean_dec(v_pat_662_);
lean_dec(v_inst_659_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(lean_object* v_s_666_, uint32_t v_c_667_, lean_object* v_a_668_, uint8_t v_b_669_){
_start:
{
lean_object* v_str_670_; lean_object* v_startInclusive_671_; lean_object* v_endExclusive_672_; lean_object* v___x_673_; uint8_t v_decide_674_; 
v_str_670_ = lean_ctor_get(v_s_666_, 0);
v_startInclusive_671_ = lean_ctor_get(v_s_666_, 1);
v_endExclusive_672_ = lean_ctor_get(v_s_666_, 2);
v___x_673_ = lean_nat_sub(v_endExclusive_672_, v_startInclusive_671_);
v_decide_674_ = lean_nat_dec_eq(v_a_668_, v___x_673_);
lean_dec(v___x_673_);
if (v_decide_674_ == 0)
{
lean_object* v___x_675_; uint32_t v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_nat_add(v_startInclusive_671_, v_a_668_);
lean_dec(v_a_668_);
v___x_676_ = lean_string_utf8_get_fast(v_str_670_, v___x_675_);
v___x_677_ = lean_uint32_dec_eq(v___x_676_, v_c_667_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_string_utf8_next_fast(v_str_670_, v___x_675_);
lean_dec(v___x_675_);
v___x_679_ = lean_nat_sub(v___x_678_, v_startInclusive_671_);
v_a_668_ = v___x_679_;
v_b_669_ = v___x_677_;
goto _start;
}
else
{
lean_dec(v___x_675_);
return v___x_677_;
}
}
else
{
lean_dec(v_a_668_);
return v_b_669_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg___boxed(lean_object* v_s_681_, lean_object* v_c_682_, lean_object* v_a_683_, lean_object* v_b_684_){
_start:
{
uint32_t v_c_boxed_685_; uint8_t v_b_boxed_686_; uint8_t v_res_687_; lean_object* v_r_688_; 
v_c_boxed_685_ = lean_unbox_uint32(v_c_682_);
lean_dec(v_c_682_);
v_b_boxed_686_ = lean_unbox(v_b_684_);
v_res_687_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_681_, v_c_boxed_685_, v_a_683_, v_b_boxed_686_);
lean_dec_ref(v_s_681_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(uint32_t v_c_689_, lean_object* v_s_690_){
_start:
{
lean_object* v_searcher_691_; uint8_t v___x_692_; uint8_t v___x_693_; 
v_searcher_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = 0;
v___x_693_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_690_, v_c_689_, v_searcher_691_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0___boxed(lean_object* v_c_694_, lean_object* v_s_695_){
_start:
{
uint32_t v_c_boxed_696_; uint8_t v_res_697_; lean_object* v_r_698_; 
v_c_boxed_696_ = lean_unbox_uint32(v_c_694_);
lean_dec(v_c_694_);
v_res_697_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(v_c_boxed_696_, v_s_695_);
lean_dec_ref(v_s_695_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT uint8_t lean_string_contains(lean_object* v_s_699_, uint32_t v_c_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_string_utf8_byte_size(v_s_699_);
v___x_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_703_, 0, v_s_699_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
v___x_704_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(v_c_700_, v___x_703_);
lean_dec_ref_known(v___x_703_, 3);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object* v_s_705_, lean_object* v_c_706_){
_start:
{
uint32_t v_c_boxed_707_; uint8_t v_res_708_; lean_object* v_r_709_; 
v_c_boxed_707_ = lean_unbox_uint32(v_c_706_);
lean_dec(v_c_706_);
v_res_708_ = lean_string_contains(v_s_705_, v_c_boxed_707_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(lean_object* v_s_710_, uint32_t v_c_711_, lean_object* v_inst_712_, lean_object* v_R_713_, lean_object* v_a_714_, uint8_t v_b_715_, lean_object* v_c_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_710_, v_c_711_, v_a_714_, v_b_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___boxed(lean_object* v_s_718_, lean_object* v_c_719_, lean_object* v_inst_720_, lean_object* v_R_721_, lean_object* v_a_722_, lean_object* v_b_723_, lean_object* v_c_724_){
_start:
{
uint32_t v_c_boxed_725_; uint8_t v_b_boxed_726_; uint8_t v_res_727_; lean_object* v_r_728_; 
v_c_boxed_725_ = lean_unbox_uint32(v_c_719_);
lean_dec(v_c_719_);
v_b_boxed_726_ = lean_unbox(v_b_723_);
v_res_727_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(v_s_718_, v_c_boxed_725_, v_inst_720_, v_R_721_, v_a_722_, v_b_boxed_726_, v_c_724_);
lean_dec_ref(v_s_718_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT uint8_t l_String_any___redArg(lean_object* v_inst_729_, lean_object* v_s_730_, lean_object* v_inst_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_string_utf8_byte_size(v_s_730_);
v___x_734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_734_, 0, v_s_730_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
lean_ctor_set(v___x_734_, 2, v___x_733_);
v___x_735_ = l_String_Slice_contains___redArg(v_inst_729_, v___x_734_, v_inst_731_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_String_any___redArg___boxed(lean_object* v_inst_736_, lean_object* v_s_737_, lean_object* v_inst_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_String_any___redArg(v_inst_736_, v_s_737_, v_inst_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT uint8_t l_String_any(lean_object* v_00_u03c1_741_, lean_object* v_00_u03c3_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_s_745_, lean_object* v_pat_746_, lean_object* v_inst_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_string_utf8_byte_size(v_s_745_);
v___x_750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_750_, 0, v_s_745_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
v___x_751_ = l_String_Slice_contains___redArg(v_inst_744_, v___x_750_, v_inst_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object* v_00_u03c1_752_, lean_object* v_00_u03c3_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_s_756_, lean_object* v_pat_757_, lean_object* v_inst_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_String_any(v_00_u03c1_752_, v_00_u03c3_753_, v_inst_754_, v_inst_755_, v_s_756_, v_pat_757_, v_inst_758_);
lean_dec(v_pat_757_);
lean_dec(v_inst_754_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(lean_object* v_s_761_, lean_object* v_p_762_, lean_object* v_a_763_, uint8_t v_b_764_){
_start:
{
lean_object* v_str_765_; lean_object* v_startInclusive_766_; lean_object* v_endExclusive_767_; lean_object* v___x_768_; uint8_t v_decide_769_; 
v_str_765_ = lean_ctor_get(v_s_761_, 0);
v_startInclusive_766_ = lean_ctor_get(v_s_761_, 1);
v_endExclusive_767_ = lean_ctor_get(v_s_761_, 2);
v___x_768_ = lean_nat_sub(v_endExclusive_767_, v_startInclusive_766_);
v_decide_769_ = lean_nat_dec_eq(v_a_763_, v___x_768_);
lean_dec(v___x_768_);
if (v_decide_769_ == 0)
{
lean_object* v___x_770_; uint32_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_770_ = lean_nat_add(v_startInclusive_766_, v_a_763_);
lean_dec(v_a_763_);
v___x_771_ = lean_string_utf8_get_fast(v_str_765_, v___x_770_);
v___x_772_ = lean_box_uint32(v___x_771_);
lean_inc_ref(v_p_762_);
v___x_773_ = lean_apply_1(v_p_762_, v___x_772_);
v___x_774_ = lean_unbox(v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = lean_string_utf8_next_fast(v_str_765_, v___x_770_);
lean_dec(v___x_770_);
v___x_776_ = lean_nat_sub(v___x_775_, v_startInclusive_766_);
v___x_777_ = lean_unbox(v___x_773_);
v_a_763_ = v___x_776_;
v_b_764_ = v___x_777_;
goto _start;
}
else
{
uint8_t v___x_779_; 
lean_dec(v___x_770_);
lean_dec_ref(v_p_762_);
v___x_779_ = lean_unbox(v___x_773_);
return v___x_779_;
}
}
else
{
lean_dec(v_a_763_);
lean_dec_ref(v_p_762_);
return v_b_764_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg___boxed(lean_object* v_s_780_, lean_object* v_p_781_, lean_object* v_a_782_, lean_object* v_b_783_){
_start:
{
uint8_t v_b_boxed_784_; uint8_t v_res_785_; lean_object* v_r_786_; 
v_b_boxed_784_ = lean_unbox(v_b_783_);
v_res_785_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(v_s_780_, v_p_781_, v_a_782_, v_b_boxed_784_);
lean_dec_ref(v_s_780_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0(lean_object* v_p_787_, lean_object* v_s_788_){
_start:
{
lean_object* v_searcher_789_; uint8_t v___x_790_; uint8_t v___x_791_; 
v_searcher_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = 0;
v___x_791_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(v_s_788_, v_p_787_, v_searcher_789_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0___boxed(lean_object* v_p_792_, lean_object* v_s_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0(v_p_792_, v_s_793_);
lean_dec_ref(v_s_793_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT uint8_t lean_string_any(lean_object* v_s_796_, lean_object* v_p_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_string_utf8_byte_size(v_s_796_);
v___x_800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_800_, 0, v_s_796_);
lean_ctor_set(v___x_800_, 1, v___x_798_);
lean_ctor_set(v___x_800_, 2, v___x_799_);
v___x_801_ = l_String_Slice_contains___at___00String_Internal_anyImpl_spec__0(v_p_797_, v___x_800_);
lean_dec_ref_known(v___x_800_, 3);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object* v_s_802_, lean_object* v_p_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = lean_string_any(v_s_802_, v_p_803_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0(lean_object* v_s_806_, lean_object* v_p_807_, lean_object* v_inst_808_, lean_object* v_R_809_, lean_object* v_a_810_, uint8_t v_b_811_, lean_object* v_c_812_){
_start:
{
uint8_t v___x_813_; 
v___x_813_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___redArg(v_s_806_, v_p_807_, v_a_810_, v_b_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0___boxed(lean_object* v_s_814_, lean_object* v_p_815_, lean_object* v_inst_816_, lean_object* v_R_817_, lean_object* v_a_818_, lean_object* v_b_819_, lean_object* v_c_820_){
_start:
{
uint8_t v_b_boxed_821_; uint8_t v_res_822_; lean_object* v_r_823_; 
v_b_boxed_821_ = lean_unbox(v_b_819_);
v_res_822_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_anyImpl_spec__0_spec__0(v_s_814_, v_p_815_, v_inst_816_, v_R_817_, v_a_818_, v_b_boxed_821_, v_c_820_);
lean_dec_ref(v_s_814_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_String_isNat(lean_object* v_s_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_string_utf8_byte_size(v_s_824_);
v___x_827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_827_, 0, v_s_824_);
lean_ctor_set(v___x_827_, 1, v___x_825_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
v___x_828_ = l_String_Slice_isNat(v___x_827_);
lean_dec_ref_known(v___x_827_, 3);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object* v_s_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_String_isNat(v_s_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object* v_s_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_string_utf8_byte_size(v_s_832_);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v_s_832_);
lean_ctor_set(v___x_835_, 1, v___x_833_);
lean_ctor_set(v___x_835_, 2, v___x_834_);
v___x_836_ = l_String_Slice_toNat_x3f(v___x_835_);
lean_dec_ref_known(v___x_835_, 3);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object* v_s_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_string_utf8_byte_size(v_s_837_);
v___x_840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_840_, 0, v_s_837_);
lean_ctor_set(v___x_840_, 1, v___x_838_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
v___x_841_ = l_String_Slice_toNat_x21(v___x_840_);
lean_dec_ref_known(v___x_840_, 3);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object* v_s_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_string_utf8_byte_size(v_s_842_);
v___x_845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_845_, 0, v_s_842_);
lean_ctor_set(v___x_845_, 1, v___x_843_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
v___x_846_ = l_String_Slice_toInt_x3f(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT uint8_t l_String_isInt(lean_object* v_s_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_string_utf8_byte_size(v_s_847_);
v___x_850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_850_, 0, v_s_847_);
lean_ctor_set(v___x_850_, 1, v___x_848_);
lean_ctor_set(v___x_850_, 2, v___x_849_);
v___x_851_ = l_String_Slice_isInt(v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object* v_s_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_String_isInt(v_s_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object* v_s_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_string_utf8_byte_size(v_s_856_);
v___x_859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_859_, 0, v_s_856_);
lean_ctor_set(v___x_859_, 1, v___x_857_);
lean_ctor_set(v___x_859_, 2, v___x_858_);
v___x_860_ = l_String_Slice_toInt_x3f(v___x_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = l_Int_instInhabited;
v___x_862_ = ((lean_object*)(l_String_toInt_x21___closed__0));
v___x_863_ = l_panic___redArg(v___x_861_, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v_val_864_; 
v_val_864_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v___x_860_, 1);
return v_val_864_;
}
}
}
LEAN_EXPORT lean_object* l_String_front_x3f(lean_object* v_s_865_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = lean_string_utf8_byte_size(v_s_865_);
v___x_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_868_, 0, v_s_865_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
v___x_869_ = l_String_Slice_Pos_get_x3f(v___x_868_, v___x_866_);
lean_dec_ref_known(v___x_868_, 3);
return v___x_869_;
}
}
LEAN_EXPORT uint32_t l_String_front(lean_object* v_s_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_string_utf8_byte_size(v_s_870_);
v___x_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_873_, 0, v_s_870_);
lean_ctor_set(v___x_873_, 1, v___x_871_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
v___x_874_ = l_String_Slice_Pos_get_x3f(v___x_873_, v___x_871_);
lean_dec_ref_known(v___x_873_, 3);
if (lean_obj_tag(v___x_874_) == 0)
{
uint32_t v___x_875_; 
v___x_875_ = 65;
return v___x_875_;
}
else
{
lean_object* v_val_876_; uint32_t v___x_877_; 
v_val_876_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v___x_874_, 1);
v___x_877_ = lean_unbox_uint32(v_val_876_);
lean_dec(v_val_876_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object* v_s_878_){
_start:
{
uint32_t v_res_879_; lean_object* v_r_880_; 
v_res_879_ = l_String_front(v_s_878_);
v_r_880_ = lean_box_uint32(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT uint32_t lean_string_front(lean_object* v_s_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_string_utf8_byte_size(v_s_881_);
v___x_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_884_, 0, v_s_881_);
lean_ctor_set(v___x_884_, 1, v___x_882_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
v___x_885_ = l_String_Slice_Pos_get_x3f(v___x_884_, v___x_882_);
lean_dec_ref_known(v___x_884_, 3);
if (lean_obj_tag(v___x_885_) == 0)
{
uint32_t v___x_886_; 
v___x_886_ = 65;
return v___x_886_;
}
else
{
lean_object* v_val_887_; uint32_t v___x_888_; 
v_val_887_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v___x_885_, 1);
v___x_888_ = lean_unbox_uint32(v_val_887_);
lean_dec(v_val_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object* v_s_889_){
_start:
{
uint32_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = lean_string_front(v_s_889_);
v_r_891_ = lean_box_uint32(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_String_back_x3f(lean_object* v_s_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_string_utf8_byte_size(v_s_892_);
v___x_895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_895_, 0, v_s_892_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
lean_ctor_set(v___x_895_, 2, v___x_894_);
v___x_896_ = l_String_Slice_Pos_prev_x3f(v___x_895_, v___x_894_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v___x_897_; 
lean_dec_ref_known(v___x_895_, 3);
v___x_897_ = lean_box(0);
return v___x_897_;
}
else
{
lean_object* v_val_898_; lean_object* v___x_899_; 
v_val_898_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v___x_896_, 1);
v___x_899_ = l_String_Slice_Pos_get_x3f(v___x_895_, v_val_898_);
lean_dec(v_val_898_);
lean_dec_ref_known(v___x_895_, 3);
return v___x_899_;
}
}
}
LEAN_EXPORT uint32_t l_String_back(lean_object* v_s_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_string_utf8_byte_size(v_s_900_);
v___x_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_903_, 0, v_s_900_);
lean_ctor_set(v___x_903_, 1, v___x_901_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
v___x_904_ = l_String_Slice_Pos_prev_x3f(v___x_903_, v___x_902_);
if (lean_obj_tag(v___x_904_) == 0)
{
uint32_t v___x_905_; 
lean_dec_ref_known(v___x_903_, 3);
v___x_905_ = 65;
return v___x_905_;
}
else
{
lean_object* v_val_906_; lean_object* v___x_907_; 
v_val_906_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_904_, 1);
v___x_907_ = l_String_Slice_Pos_get_x3f(v___x_903_, v_val_906_);
lean_dec(v_val_906_);
lean_dec_ref_known(v___x_903_, 3);
if (lean_obj_tag(v___x_907_) == 0)
{
uint32_t v___x_908_; 
v___x_908_ = 65;
return v___x_908_;
}
else
{
lean_object* v_val_909_; uint32_t v___x_910_; 
v_val_909_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_val_909_);
lean_dec_ref_known(v___x_907_, 1);
v___x_910_ = lean_unbox_uint32(v_val_909_);
lean_dec(v_val_909_);
return v___x_910_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object* v_s_911_){
_start:
{
uint32_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = l_String_back(v_s_911_);
v_r_913_ = lean_box_uint32(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT lean_object* l_String_lines(lean_object* v_s_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_string_utf8_byte_size(v_s_914_);
v___x_917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_917_, 0, v_s_914_);
lean_ctor_set(v___x_917_, 1, v___x_915_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
v___x_918_ = l_String_Slice_lines(v___x_917_);
lean_dec_ref_known(v___x_917_, 3);
return v___x_918_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Slice(builtin);
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
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice(builtin);
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
