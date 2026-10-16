// Lean compiler output
// Module: Init.Data.String.Slice.Basic
// Imports: public import Init.Data.String.Basic public import Init.Data.String.FindPos public import Init.Data.String.Compare public import Init.Data.Ord.Basic import Init.Data.String.Pattern.Memcmp import Init.Omega
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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
uint8_t lean_bool_to_uint8(uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instHAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instHAppend___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instHAppend___closed__0 = (const lean_object*)&l_String_Slice_instHAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instHAppend = (const lean_object*)&l_String_Slice_instHAppend___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instBEq___closed__0 = (const lean_object*)&l_String_Slice_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instBEq = (const lean_object*)&l_String_Slice_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toString___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instToString___closed__0 = (const lean_object*)&l_String_Slice_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instToString = (const lean_object*)&l_String_Slice_instToString___closed__0_value;
uint64_t lean_slice_hash(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_hash___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instHashable___closed__0 = (const lean_object*)&l_String_Slice_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instHashable = (const lean_object*)&l_String_Slice_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instLT;
uint8_t lean_slice_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instOrd___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instOrd___closed__0 = (const lean_object*)&l_String_Slice_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instOrd = (const lean_object*)&l_String_Slice_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instLE;
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_intercalate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_intercalate___closed__0 = (const lean_object*)&l_String_Slice_intercalate___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instToFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instToFormat___closed__0 = (const lean_object*)&l_String_Slice_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instToFormat = (const lean_object*)&l_String_Slice_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0(lean_object* v_s_1_, lean_object* v_t_2_){
_start:
{
lean_object* v_str_3_; lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_str_3_ = lean_ctor_get(v_t_2_, 0);
v_startInclusive_4_ = lean_ctor_get(v_t_2_, 1);
v_endExclusive_5_ = lean_ctor_get(v_t_2_, 2);
v___x_6_ = lean_string_utf8_extract_fast(v_str_3_, v_startInclusive_4_, v_endExclusive_5_);
v___x_7_ = lean_string_append(v_s_1_, v___x_6_);
lean_dec_ref(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0___boxed(lean_object* v_s_8_, lean_object* v_t_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_String_Slice_instHAppend___lam__0(v_s_8_, v_t_9_);
lean_dec_ref(v_t_9_);
return v_res_10_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_beq(lean_object* v_s1_13_, lean_object* v_s2_14_){
_start:
{
lean_object* v_str_15_; lean_object* v_startInclusive_16_; lean_object* v_endExclusive_17_; lean_object* v_str_18_; lean_object* v_startInclusive_19_; lean_object* v_endExclusive_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_str_15_ = lean_ctor_get(v_s1_13_, 0);
v_startInclusive_16_ = lean_ctor_get(v_s1_13_, 1);
v_endExclusive_17_ = lean_ctor_get(v_s1_13_, 2);
v_str_18_ = lean_ctor_get(v_s2_14_, 0);
v_startInclusive_19_ = lean_ctor_get(v_s2_14_, 1);
v_endExclusive_20_ = lean_ctor_get(v_s2_14_, 2);
v___x_21_ = lean_nat_sub(v_endExclusive_17_, v_startInclusive_16_);
v___x_22_ = lean_nat_sub(v_endExclusive_20_, v_startInclusive_19_);
v___x_23_ = lean_nat_dec_eq(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
if (v___x_23_ == 0)
{
lean_dec(v___x_21_);
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_string_memcmp(v_str_15_, v_str_18_, v_startInclusive_16_, v_startInclusive_19_, v___x_21_);
lean_dec(v___x_21_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_beq___boxed(lean_object* v_s1_25_, lean_object* v_s2_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_String_Slice_beq(v_s1_25_, v_s2_26_);
lean_dec_ref(v_s2_26_);
lean_dec_ref(v_s1_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString(lean_object* v_s_31_){
_start:
{
lean_object* v_str_32_; lean_object* v_startInclusive_33_; lean_object* v_endExclusive_34_; lean_object* v___x_35_; 
v_str_32_ = lean_ctor_get(v_s_31_, 0);
v_startInclusive_33_ = lean_ctor_get(v_s_31_, 1);
v_endExclusive_34_ = lean_ctor_get(v_s_31_, 2);
v___x_35_ = lean_string_utf8_extract_fast(v_str_32_, v_startInclusive_33_, v_endExclusive_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString___boxed(lean_object* v_s_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_String_Slice_toString(v_s_36_);
lean_dec_ref(v_s_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_hash___boxed(lean_object* v_s_41_){
_start:
{
uint64_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lean_slice_hash(v_s_41_);
lean_dec_ref(v_s_41_);
v_r_43_ = lean_box_uint64(v_res_42_);
return v_r_43_;
}
}
static lean_object* _init_l_String_Slice_instLT(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLt___boxed(lean_object* v_x_49_, lean_object* v_y_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = lean_slice_dec_lt(v_x_49_, v_y_50_);
lean_dec_ref(v_y_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instOrd___lam__0(lean_object* v_x_53_, lean_object* v_y_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = lean_slice_dec_lt(v_x_53_, v_y_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = l_String_Slice_beq(v_x_53_, v_y_54_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = 2;
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = 1;
return v___x_58_;
}
}
else
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instOrd___lam__0___boxed(lean_object* v_x_60_, lean_object* v_y_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_String_Slice_instOrd___lam__0(v_x_60_, v_y_61_);
lean_dec_ref(v_y_61_);
lean_dec_ref(v_x_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
static lean_object* _init_l_String_Slice_instLE(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLE(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_slice_dec_lt(v_x_67_, v_y_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLE___boxed(lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_String_Slice_instDecidableLE(v_x_72_, v_y_73_);
lean_dec_ref(v_y_73_);
lean_dec_ref(v_x_72_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_76_, lean_object* v_n_77_){
_start:
{
lean_object* v_str_78_; lean_object* v_startInclusive_79_; lean_object* v_endExclusive_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
v_str_78_ = lean_ctor_get(v_s_76_, 0);
lean_inc_ref(v_str_78_);
v_startInclusive_79_ = lean_ctor_get(v_s_76_, 1);
lean_inc(v_startInclusive_79_);
v_endExclusive_80_ = lean_ctor_get(v_s_76_, 2);
lean_inc(v_endExclusive_80_);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = l_String_Slice_Pos_nextn(v_s_76_, v___x_81_, v_n_77_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_s_76_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; 
v_unused_91_ = lean_ctor_get(v_s_76_, 2);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_s_76_, 1);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_s_76_, 0);
lean_dec(v_unused_93_);
v___x_84_ = v_s_76_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_dec(v_s_76_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_nat_add(v_startInclusive_79_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v_startInclusive_79_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_str_78_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v_endExclusive_80_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_94_, lean_object* v_n_95_){
_start:
{
lean_object* v_str_96_; lean_object* v_startInclusive_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_str_96_ = lean_ctor_get(v_s_94_, 0);
lean_inc_ref(v_str_96_);
v_startInclusive_97_ = lean_ctor_get(v_s_94_, 1);
lean_inc(v_startInclusive_97_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = l_String_Slice_Pos_nextn(v_s_94_, v___x_98_, v_n_95_);
v_isSharedCheck_107_ = !lean_is_exclusive(v_s_94_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; lean_object* v_unused_110_; 
v_unused_108_ = lean_ctor_get(v_s_94_, 2);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_s_94_, 1);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_s_94_, 0);
lean_dec(v_unused_110_);
v___x_101_ = v_s_94_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_s_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_nat_add(v_startInclusive_97_, v___x_99_);
lean_dec(v___x_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 2, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_str_96_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_startInclusive_97_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_111_, lean_object* v_n_112_){
_start:
{
lean_object* v_str_113_; lean_object* v_startInclusive_114_; lean_object* v_endExclusive_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_str_113_ = lean_ctor_get(v_s_111_, 0);
lean_inc_ref(v_str_113_);
v_startInclusive_114_ = lean_ctor_get(v_s_111_, 1);
lean_inc(v_startInclusive_114_);
v_endExclusive_115_ = lean_ctor_get(v_s_111_, 2);
v___x_116_ = lean_nat_sub(v_endExclusive_115_, v_startInclusive_114_);
v___x_117_ = l_String_Slice_Pos_prevn(v_s_111_, v___x_116_, v_n_112_);
v_isSharedCheck_125_ = !lean_is_exclusive(v_s_111_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; lean_object* v_unused_127_; lean_object* v_unused_128_; 
v_unused_126_ = lean_ctor_get(v_s_111_, 2);
lean_dec(v_unused_126_);
v_unused_127_ = lean_ctor_get(v_s_111_, 1);
lean_dec(v_unused_127_);
v_unused_128_ = lean_ctor_get(v_s_111_, 0);
lean_dec(v_unused_128_);
v___x_119_ = v_s_111_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_dec(v_s_111_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_nat_add(v_startInclusive_114_, v___x_117_);
lean_dec(v___x_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 2, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_str_113_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_startInclusive_114_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_129_, lean_object* v_n_130_){
_start:
{
lean_object* v_str_131_; lean_object* v_startInclusive_132_; lean_object* v_endExclusive_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_143_; 
v_str_131_ = lean_ctor_get(v_s_129_, 0);
lean_inc_ref(v_str_131_);
v_startInclusive_132_ = lean_ctor_get(v_s_129_, 1);
lean_inc(v_startInclusive_132_);
v_endExclusive_133_ = lean_ctor_get(v_s_129_, 2);
lean_inc(v_endExclusive_133_);
v___x_134_ = lean_nat_sub(v_endExclusive_133_, v_startInclusive_132_);
v___x_135_ = l_String_Slice_Pos_prevn(v_s_129_, v___x_134_, v_n_130_);
v_isSharedCheck_143_ = !lean_is_exclusive(v_s_129_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; lean_object* v_unused_145_; lean_object* v_unused_146_; 
v_unused_144_ = lean_ctor_get(v_s_129_, 2);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_s_129_, 1);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_s_129_, 0);
lean_dec(v_unused_146_);
v___x_137_ = v_s_129_;
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
else
{
lean_dec(v_s_129_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_nat_add(v_startInclusive_132_, v___x_135_);
lean_dec(v___x_135_);
lean_dec(v_startInclusive_132_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_139_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_str_131_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_endExclusive_133_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_147_, lean_object* v_s1Curr_148_, lean_object* v_s2_149_, lean_object* v_s2Curr_150_){
_start:
{
lean_object* v_str_151_; lean_object* v_startInclusive_152_; lean_object* v_endExclusive_153_; lean_object* v___x_154_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_str_151_ = lean_ctor_get(v_s1_147_, 0);
v_startInclusive_152_ = lean_ctor_get(v_s1_147_, 1);
v_endExclusive_153_ = lean_ctor_get(v_s1_147_, 2);
v___x_154_ = lean_nat_sub(v_endExclusive_153_, v_startInclusive_152_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_s1Curr_148_, v___x_161_);
v___x_163_ = lean_nat_dec_le(v___x_162_, v___x_154_);
if (v___x_163_ == 0)
{
lean_dec(v___x_162_);
goto v___jp_155_;
}
else
{
lean_object* v_str_164_; lean_object* v_startInclusive_165_; lean_object* v_endExclusive_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_str_164_ = lean_ctor_get(v_s2_149_, 0);
v_startInclusive_165_ = lean_ctor_get(v_s2_149_, 1);
v_endExclusive_166_ = lean_ctor_get(v_s2_149_, 2);
v___x_167_ = lean_nat_sub(v_endExclusive_166_, v_startInclusive_165_);
v___x_168_ = lean_nat_add(v_s2Curr_150_, v___x_161_);
v___x_169_ = lean_nat_dec_le(v___x_168_, v___x_167_);
lean_dec(v___x_167_);
if (v___x_169_ == 0)
{
lean_dec(v___x_168_);
lean_dec(v___x_162_);
goto v___jp_155_;
}
else
{
lean_object* v___x_170_; uint8_t v___x_171_; uint8_t v___x_172_; uint8_t v___x_173_; uint8_t v___x_174_; uint8_t v___x_175_; uint8_t v___x_176_; uint8_t v___x_177_; uint8_t v___x_178_; uint8_t v_c1_179_; lean_object* v___x_180_; uint8_t v___x_181_; uint8_t v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; uint8_t v___x_185_; uint8_t v_c2_186_; uint8_t v___x_187_; 
lean_dec(v___x_154_);
v___x_170_ = lean_nat_add(v_startInclusive_152_, v_s1Curr_148_);
lean_dec(v_s1Curr_148_);
v___x_171_ = lean_string_get_byte_fast(v_str_151_, v___x_170_);
v___x_172_ = 65;
v___x_173_ = lean_uint8_sub(v___x_171_, v___x_172_);
v___x_174_ = 26;
v___x_175_ = lean_uint8_dec_lt(v___x_173_, v___x_174_);
v___x_176_ = lean_bool_to_uint8(v___x_175_);
v___x_177_ = 5;
v___x_178_ = lean_uint8_shift_left(v___x_176_, v___x_177_);
v_c1_179_ = lean_uint8_add(v___x_171_, v___x_178_);
v___x_180_ = lean_nat_add(v_startInclusive_165_, v_s2Curr_150_);
lean_dec(v_s2Curr_150_);
v___x_181_ = lean_string_get_byte_fast(v_str_164_, v___x_180_);
v___x_182_ = lean_uint8_sub(v___x_181_, v___x_172_);
v___x_183_ = lean_uint8_dec_lt(v___x_182_, v___x_174_);
v___x_184_ = lean_bool_to_uint8(v___x_183_);
v___x_185_ = lean_uint8_shift_left(v___x_184_, v___x_177_);
v_c2_186_ = lean_uint8_add(v___x_181_, v___x_185_);
v___x_187_ = lean_uint8_dec_eq(v_c1_179_, v_c2_186_);
if (v___x_187_ == 0)
{
lean_dec(v___x_168_);
lean_dec(v___x_162_);
return v___x_187_;
}
else
{
v_s1Curr_148_ = v___x_162_;
v_s2Curr_150_ = v___x_168_;
goto _start;
}
}
}
v___jp_155_:
{
uint8_t v_decide_156_; 
v_decide_156_ = lean_nat_dec_eq(v_s1Curr_148_, v___x_154_);
lean_dec(v___x_154_);
lean_dec(v_s1Curr_148_);
if (v_decide_156_ == 0)
{
lean_dec(v_s2Curr_150_);
return v_decide_156_;
}
else
{
lean_object* v_startInclusive_157_; lean_object* v_endExclusive_158_; lean_object* v___x_159_; uint8_t v_decide_160_; 
v_startInclusive_157_ = lean_ctor_get(v_s2_149_, 1);
v_endExclusive_158_ = lean_ctor_get(v_s2_149_, 2);
v___x_159_ = lean_nat_sub(v_endExclusive_158_, v_startInclusive_157_);
v_decide_160_ = lean_nat_dec_eq(v_s2Curr_150_, v___x_159_);
lean_dec(v___x_159_);
lean_dec(v_s2Curr_150_);
return v_decide_160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_189_, lean_object* v_s1Curr_190_, lean_object* v_s2_191_, lean_object* v_s2Curr_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_189_, v_s1Curr_190_, v_s2_191_, v_s2Curr_192_);
lean_dec_ref(v_s2_191_);
lean_dec_ref(v_s1_189_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_195_, lean_object* v_s2_196_){
_start:
{
lean_object* v_startInclusive_197_; lean_object* v_endExclusive_198_; lean_object* v_startInclusive_199_; lean_object* v_endExclusive_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_startInclusive_197_ = lean_ctor_get(v_s1_195_, 1);
v_endExclusive_198_ = lean_ctor_get(v_s1_195_, 2);
v_startInclusive_199_ = lean_ctor_get(v_s2_196_, 1);
v_endExclusive_200_ = lean_ctor_get(v_s2_196_, 2);
v___x_201_ = lean_nat_sub(v_endExclusive_198_, v_startInclusive_197_);
v___x_202_ = lean_nat_sub(v_endExclusive_200_, v_startInclusive_199_);
v___x_203_ = lean_nat_dec_eq(v___x_201_, v___x_202_);
lean_dec(v___x_202_);
lean_dec(v___x_201_);
if (v___x_203_ == 0)
{
return v___x_203_;
}
else
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_195_, v___x_204_, v_s2_196_, v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_206_, lean_object* v_s2_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_206_, v_s2_207_);
lean_dec_ref(v_s2_207_);
lean_dec_ref(v_s1_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = l_String_Slice_Pos_get_x3f(v_s_210_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_String_Slice_front_x3f(v_s_213_);
lean_dec_ref(v_s_213_);
return v_res_214_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = l_String_Slice_Pos_get_x3f(v_s_215_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
uint32_t v___x_218_; 
v___x_218_ = 65;
return v___x_218_;
}
else
{
lean_object* v_val_219_; uint32_t v___x_220_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_217_, 1);
v___x_220_ = lean_unbox_uint32(v_val_219_);
lean_dec(v_val_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_221_){
_start:
{
uint32_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_String_Slice_front(v_s_221_);
lean_dec_ref(v_s_221_);
v_r_223_ = lean_box_uint32(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_224_){
_start:
{
lean_object* v_startInclusive_225_; lean_object* v_endExclusive_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_startInclusive_225_ = lean_ctor_get(v_s_224_, 1);
v_endExclusive_226_ = lean_ctor_get(v_s_224_, 2);
v___x_227_ = lean_nat_sub(v_endExclusive_226_, v_startInclusive_225_);
v___x_228_ = l_String_Slice_Pos_prev_x3f(v_s_224_, v___x_227_);
lean_dec(v___x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_box(0);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_228_, 1);
v___x_231_ = l_String_Slice_Pos_get_x3f(v_s_224_, v_val_230_);
lean_dec(v_val_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_String_Slice_back_x3f(v_s_232_);
lean_dec_ref(v_s_232_);
return v_res_233_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_234_){
_start:
{
lean_object* v_startInclusive_235_; lean_object* v_endExclusive_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_startInclusive_235_ = lean_ctor_get(v_s_234_, 1);
v_endExclusive_236_ = lean_ctor_get(v_s_234_, 2);
v___x_237_ = lean_nat_sub(v_endExclusive_236_, v_startInclusive_235_);
v___x_238_ = l_String_Slice_Pos_prev_x3f(v_s_234_, v___x_237_);
lean_dec(v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
uint32_t v___x_239_; 
v___x_239_ = 65;
return v___x_239_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_241_; 
v_val_240_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v___x_238_, 1);
v___x_241_ = l_String_Slice_Pos_get_x3f(v_s_234_, v_val_240_);
lean_dec(v_val_240_);
if (lean_obj_tag(v___x_241_) == 0)
{
uint32_t v___x_242_; 
v___x_242_ = 65;
return v___x_242_;
}
else
{
lean_object* v_val_243_; uint32_t v___x_244_; 
v_val_243_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v___x_241_, 1);
v___x_244_ = lean_unbox_uint32(v_val_243_);
lean_dec(v_val_243_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_245_){
_start:
{
uint32_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_String_Slice_back(v_s_245_);
lean_dec_ref(v_s_245_);
v_r_247_ = lean_box_uint32(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(lean_object* v_acc_248_, lean_object* v_s_249_, lean_object* v_a_250_){
_start:
{
if (lean_obj_tag(v_a_250_) == 0)
{
return v_acc_248_;
}
else
{
lean_object* v_head_251_; lean_object* v_tail_252_; lean_object* v_str_253_; lean_object* v_startInclusive_254_; lean_object* v_endExclusive_255_; lean_object* v_str_256_; lean_object* v_startInclusive_257_; lean_object* v_endExclusive_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_head_251_ = lean_ctor_get(v_a_250_, 0);
v_tail_252_ = lean_ctor_get(v_a_250_, 1);
v_str_253_ = lean_ctor_get(v_s_249_, 0);
v_startInclusive_254_ = lean_ctor_get(v_s_249_, 1);
v_endExclusive_255_ = lean_ctor_get(v_s_249_, 2);
v_str_256_ = lean_ctor_get(v_head_251_, 0);
v_startInclusive_257_ = lean_ctor_get(v_head_251_, 1);
v_endExclusive_258_ = lean_ctor_get(v_head_251_, 2);
v___x_259_ = lean_string_utf8_extract_fast(v_str_253_, v_startInclusive_254_, v_endExclusive_255_);
v___x_260_ = lean_string_append(v_acc_248_, v___x_259_);
lean_dec_ref(v___x_259_);
v___x_261_ = lean_string_utf8_extract_fast(v_str_256_, v_startInclusive_257_, v_endExclusive_258_);
v___x_262_ = lean_string_append(v___x_260_, v___x_261_);
lean_dec_ref(v___x_261_);
v_acc_248_ = v___x_262_;
v_a_250_ = v_tail_252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_264_, lean_object* v_s_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(v_acc_264_, v_s_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_s_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l_String_Slice_intercalate___closed__0));
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v_tail_273_; lean_object* v_str_274_; lean_object* v_startInclusive_275_; lean_object* v_endExclusive_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_head_272_ = lean_ctor_get(v_x_270_, 0);
v_tail_273_ = lean_ctor_get(v_x_270_, 1);
v_str_274_ = lean_ctor_get(v_head_272_, 0);
v_startInclusive_275_ = lean_ctor_get(v_head_272_, 1);
v_endExclusive_276_ = lean_ctor_get(v_head_272_, 2);
v___x_277_ = lean_string_utf8_extract_fast(v_str_274_, v_startInclusive_275_, v_endExclusive_276_);
v___x_278_ = l___private_Init_Data_String_Slice_Basic_0__String_Slice_intercalate_go(v___x_277_, v_s_269_, v_tail_273_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_String_Slice_intercalate(v_s_279_, v_x_280_);
lean_dec(v_x_280_);
lean_dec_ref(v_s_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
return v_x_282_;
}
else
{
lean_object* v_head_284_; lean_object* v_tail_285_; lean_object* v_str_286_; lean_object* v_startInclusive_287_; lean_object* v_endExclusive_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_head_284_ = lean_ctor_get(v_x_283_, 0);
v_tail_285_ = lean_ctor_get(v_x_283_, 1);
v_str_286_ = lean_ctor_get(v_head_284_, 0);
v_startInclusive_287_ = lean_ctor_get(v_head_284_, 1);
v_endExclusive_288_ = lean_ctor_get(v_head_284_, 2);
v___x_289_ = lean_string_utf8_extract_fast(v_str_286_, v_startInclusive_287_, v_endExclusive_288_);
v___x_290_ = lean_string_append(v_x_282_, v___x_289_);
lean_dec_ref(v___x_289_);
v_x_282_ = v___x_290_;
v_x_283_ = v_tail_285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_292_, v_x_293_);
lean_dec(v_x_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object* v_l_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l_String_Slice_intercalate___closed__0));
v___x_297_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_296_, v_l_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object* v_l_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_String_Slice_join(v_l_298_);
lean_dec(v_l_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = l_String_Slice_toString(v_s_300_);
v___x_302_ = l_String_toName(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_String_Slice_toName(v_s_303_);
lean_dec_ref(v_s_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_305_){
_start:
{
lean_object* v_str_306_; lean_object* v_startInclusive_307_; lean_object* v_endExclusive_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_str_306_ = lean_ctor_get(v_s_305_, 0);
v_startInclusive_307_ = lean_ctor_get(v_s_305_, 1);
v_endExclusive_308_ = lean_ctor_get(v_s_305_, 2);
v___x_309_ = lean_string_utf8_extract_fast(v_str_306_, v_startInclusive_307_, v_endExclusive_308_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_String_Slice_instToFormat___lam__0(v_s_311_);
lean_dec_ref(v_s_311_);
return v_res_312_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_instLT = _init_l_String_Slice_instLT();
lean_mark_persistent(l_String_Slice_instLT);
l_String_Slice_instLE = _init_l_String_Slice_instLE();
lean_mark_persistent(l_String_Slice_instLE);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Slice_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
