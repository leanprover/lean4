// Lean compiler output
// Module: Lean.Data.Name
// Imports: public import Init.Data.Ord.Basic import Init.Data.String.TakeDrop import Init.Data.Ord.String import Init.Data.Ord.UInt import Init.Data.String.Search import Init.Data.String.Length
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT uint64_t lean_name_hash_exported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object*);
static const lean_string_object l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Name_getString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Data.Name"};
static const lean_object* l_Lean_Name_getString_x21___closed__0 = (const lean_object*)&l_Lean_Name_getString_x21___closed__0_value;
static const lean_string_object l_Lean_Name_getString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Name.getString!"};
static const lean_object* l_Lean_Name_getString_x21___closed__1 = (const lean_object*)&l_Lean_Name_getString_x21___closed__1_value;
static const lean_string_object l_Lean_Name_getString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Name_getString_x21___closed__2 = (const lean_object*)&l_Lean_Name_getString_x21___closed__2_value;
static lean_once_cell_t l_Lean_Name_getString_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Name_getString_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_eqStr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eqStr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_cmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_cmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Name_isInternalDetail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eq_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__0 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__0_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__1 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__1_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__2 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__2_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "omega_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__3 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__3_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__4 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isImplementationDetail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "__"};
static const lean_object* l_Lean_Name_isImplementationDetail___closed__0 = (const lean_object*)&l_Lean_Name_isImplementationDetail___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isStr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_anyS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0 = (const lean_object*)&l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0_value;
static const lean_string_object l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1 = (const lean_object*)&l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1_value;
static const lean_string_object l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2 = (const lean_object*)&l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2_value;
static const lean_string_object l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3 = (const lean_object*)&l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3_value;
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isMetaprogramming___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__0 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__0_value;
static const lean_ctor_object l_Lean_Name_isMetaprogramming___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Name_isMetaprogramming___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__1 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object*);
uint64_t lean_name_hash_exported(lean_object* v_a_1_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
uint64_t v___x_2_; 
v___x_2_ = 1723ULL;
return v___x_2_;
}
else
{
uint64_t v_hash_3_; 
v_hash_3_ = lean_ctor_get_uint64(v_a_1_, sizeof(void*)*2);
lean_dec(v_a_1_);
return v_hash_3_;
}
}
}
LEAN_EXPORT void lean_name_hash_exported_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
uint64_t v_res_4_;
v_res_4_ = lean_name_hash_exported(v_a_1_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object* v_a_5_){
_start:
{
uint64_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = lean_name_hash_exported(v_a_5_);
v_r_7_ = lean_box_uint64(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
return v_x_8_;
}
else
{
lean_object* v_pre_9_; 
v_pre_9_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_pre_9_);
return v_pre_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Name_getPrefix(v_x_10_);
lean_dec(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object* v_msg_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0));
v___x_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_13_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Name_getString_x21___closed__3(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_19_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__2));
v___x_20_ = lean_unsigned_to_nat(15u);
v___x_21_ = lean_unsigned_to_nat(31u);
v___x_22_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__1));
v___x_23_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__0));
v___x_24_ = l_mkPanicMessageWithDecl(v___x_23_, v___x_22_, v___x_21_, v___x_20_, v___x_19_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 1)
{
lean_object* v_str_26_; 
v_str_26_ = lean_ctor_get(v_x_25_, 1);
lean_inc_ref(v_str_26_);
return v_str_26_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_obj_once(&l_Lean_Name_getString_x21___closed__3, &l_Lean_Name_getString_x21___closed__3_once, _init_l_Lean_Name_getString_x21___closed__3);
v___x_28_ = l_panic___at___00Lean_Name_getString_x21_spec__0(v___x_27_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Name_getString_x21(v_x_29_);
lean_dec(v_x_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object* v_x_31_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v___x_32_; 
v___x_32_ = lean_unsigned_to_nat(0u);
return v___x_32_;
}
else
{
lean_object* v_pre_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_pre_33_ = lean_ctor_get(v_x_31_, 0);
v___x_34_ = l_Lean_Name_getNumParts(v_pre_33_);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v___x_34_, v___x_35_);
lean_dec(v___x_34_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Name_getNumParts(v_x_37_);
lean_dec(v_x_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
switch(lean_obj_tag(v_x_39_))
{
case 0:
{
lean_dec(v_x_40_);
return v_x_39_;
}
case 1:
{
lean_object* v_str_41_; lean_object* v___x_42_; 
v_str_41_ = lean_ctor_get(v_x_39_, 1);
lean_inc_ref(v_str_41_);
lean_dec_ref_known(v_x_39_, 2);
v___x_42_ = l_Lean_Name_str___override(v_x_40_, v_str_41_);
return v___x_42_;
}
default: 
{
lean_object* v_i_43_; lean_object* v___x_44_; 
v_i_43_ = lean_ctor_get(v_x_39_, 1);
lean_inc(v_i_43_);
lean_dec_ref_known(v_x_39_, 2);
v___x_44_ = l_Lean_Name_num___override(v_x_40_, v_i_43_);
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object* v_x_45_){
_start:
{
switch(lean_obj_tag(v_x_45_))
{
case 0:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
case 1:
{
lean_object* v_pre_47_; lean_object* v_str_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_pre_47_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_pre_47_);
v_str_48_ = lean_ctor_get(v_x_45_, 1);
lean_inc_ref(v_str_48_);
lean_dec_ref_known(v_x_45_, 2);
v___x_49_ = lean_box(0);
v___x_50_ = l_Lean_Name_str___override(v___x_49_, v_str_48_);
v___x_51_ = l_Lean_Name_componentsRev(v_pre_47_);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
return v___x_52_;
}
default: 
{
lean_object* v_pre_53_; lean_object* v_i_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_pre_53_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_pre_53_);
v_i_54_ = lean_ctor_get(v_x_45_, 1);
lean_inc(v_i_54_);
lean_dec_ref_known(v_x_45_, 2);
v___x_55_ = lean_box(0);
v___x_56_ = l_Lean_Name_num___override(v___x_55_, v_i_54_);
v___x_57_ = l_Lean_Name_componentsRev(v_pre_53_);
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object* v_n_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = l_Lean_Name_componentsRev(v_n_59_);
v___x_61_ = l_List_reverse___redArg(v___x_60_);
return v___x_61_;
}
}
uint8_t l_Lean_Name_eqStr(lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_62_) == 1)
{
lean_object* v_pre_64_; 
v_pre_64_ = lean_ctor_get(v_x_62_, 0);
if (lean_obj_tag(v_pre_64_) == 0)
{
lean_object* v_str_65_; uint8_t v___x_66_; 
v_str_65_ = lean_ctor_get(v_x_62_, 1);
v___x_66_ = lean_string_dec_eq(v_str_65_, v_x_63_);
return v___x_66_;
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
}
LEAN_EXPORT void l_Lean_Name_eqStr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_62_ = stack[0].m_obj;
lean_object* v_x_63_ = stack[1].m_obj;
uint8_t v_res_69_;
v_res_69_ = l_Lean_Name_eqStr(v_x_62_, v_x_63_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Name_eqStr___boxed(lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_Name_eqStr(v_x_70_, v_x_71_);
lean_dec_ref(v_x_71_);
lean_dec(v_x_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
uint8_t l_Lean_Name_isPrefixOf(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
uint8_t v___x_76_; 
v___x_76_ = lean_name_eq(v_x_74_, v_x_75_);
return v___x_76_;
}
else
{
lean_object* v_pre_77_; uint8_t v___x_78_; 
v_pre_77_ = lean_ctor_get(v_x_75_, 0);
v___x_78_ = lean_name_eq(v_x_74_, v_x_75_);
if (v___x_78_ == 0)
{
v_x_75_ = v_pre_77_;
goto _start;
}
else
{
return v___x_78_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_74_ = stack[0].m_obj;
lean_object* v_x_75_ = stack[1].m_obj;
uint8_t v_res_80_;
v_res_80_ = l_Lean_Name_isPrefixOf(v_x_74_, v_x_75_);
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_Name_isPrefixOf(v_x_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v_x_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
uint8_t l_Lean_Name_isSuffixOf(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
switch(lean_obj_tag(v_x_85_))
{
case 0:
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
case 1:
{
if (lean_obj_tag(v_x_86_) == 1)
{
lean_object* v_pre_88_; lean_object* v_str_89_; lean_object* v_pre_90_; lean_object* v_str_91_; uint8_t v___x_92_; 
v_pre_88_ = lean_ctor_get(v_x_85_, 0);
v_str_89_ = lean_ctor_get(v_x_85_, 1);
v_pre_90_ = lean_ctor_get(v_x_86_, 0);
v_str_91_ = lean_ctor_get(v_x_86_, 1);
v___x_92_ = lean_string_dec_eq(v_str_89_, v_str_91_);
if (v___x_92_ == 0)
{
return v___x_92_;
}
else
{
v_x_85_ = v_pre_88_;
v_x_86_ = v_pre_90_;
goto _start;
}
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
default: 
{
if (lean_obj_tag(v_x_86_) == 2)
{
lean_object* v_pre_95_; lean_object* v_i_96_; lean_object* v_pre_97_; lean_object* v_i_98_; uint8_t v___x_99_; 
v_pre_95_ = lean_ctor_get(v_x_85_, 0);
v_i_96_ = lean_ctor_get(v_x_85_, 1);
v_pre_97_ = lean_ctor_get(v_x_86_, 0);
v_i_98_ = lean_ctor_get(v_x_86_, 1);
v___x_99_ = lean_nat_dec_eq(v_i_96_, v_i_98_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
v_x_85_ = v_pre_95_;
v_x_86_ = v_pre_97_;
goto _start;
}
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isSuffixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_85_ = stack[0].m_obj;
lean_object* v_x_86_ = stack[1].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Lean_Name_isSuffixOf(v_x_85_, v_x_86_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Lean_Name_isSuffixOf(v_x_103_, v_x_104_);
lean_dec(v_x_104_);
lean_dec(v_x_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
uint8_t l_Lean_Name_cmp(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
switch(lean_obj_tag(v_x_107_))
{
case 0:
{
if (lean_obj_tag(v_x_108_) == 0)
{
uint8_t v___x_109_; 
v___x_109_ = 1;
return v___x_109_;
}
else
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
case 1:
{
if (lean_obj_tag(v_x_108_) == 1)
{
lean_object* v_pre_111_; lean_object* v_str_112_; lean_object* v_pre_113_; lean_object* v_str_114_; uint8_t v___x_115_; 
v_pre_111_ = lean_ctor_get(v_x_107_, 0);
v_str_112_ = lean_ctor_get(v_x_107_, 1);
v_pre_113_ = lean_ctor_get(v_x_108_, 0);
v_str_114_ = lean_ctor_get(v_x_108_, 1);
v___x_115_ = l_Lean_Name_cmp(v_pre_111_, v_pre_113_);
if (v___x_115_ == 1)
{
uint8_t v___x_116_; 
v___x_116_ = lean_string_compare(v_str_112_, v_str_114_);
return v___x_116_;
}
else
{
return v___x_115_;
}
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 2;
return v___x_117_;
}
}
default: 
{
switch(lean_obj_tag(v_x_108_))
{
case 0:
{
uint8_t v___x_118_; 
v___x_118_ = 2;
return v___x_118_;
}
case 1:
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
default: 
{
lean_object* v_pre_120_; lean_object* v_i_121_; lean_object* v_pre_122_; lean_object* v_i_123_; uint8_t v___x_124_; 
v_pre_120_ = lean_ctor_get(v_x_107_, 0);
v_i_121_ = lean_ctor_get(v_x_107_, 1);
v_pre_122_ = lean_ctor_get(v_x_108_, 0);
v_i_123_ = lean_ctor_get(v_x_108_, 1);
v___x_124_ = l_Lean_Name_cmp(v_pre_120_, v_pre_122_);
if (v___x_124_ == 1)
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_lt(v_i_121_, v_i_123_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_eq(v_i_121_, v_i_123_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 2;
return v___x_127_;
}
else
{
return v___x_124_;
}
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
else
{
return v___x_124_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Name_cmp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_107_ = stack[0].m_obj;
lean_object* v_x_108_ = stack[1].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Lean_Name_cmp(v_x_107_, v_x_108_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lean_Name_cmp___boxed(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_Name_cmp(v_x_130_, v_x_131_);
lean_dec(v_x_131_);
lean_dec(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
uint8_t l_Lean_Name_lt(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_136_ = l_Lean_Name_cmp(v_x_134_, v_y_135_);
v___x_137_ = lean_box(v___x_136_);
v___x_138_ = lean_obj_tag_nat(v___x_137_);
lean_dec(v___x_137_);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_nat_dec_eq(v___x_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT void l_Lean_Name_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_134_ = stack[0].m_obj;
lean_object* v_y_135_ = stack[1].m_obj;
uint8_t v_res_141_;
v_res_141_ = l_Lean_Name_lt(v_x_134_, v_y_135_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object* v_x_142_, lean_object* v_y_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lean_Name_lt(v_x_142_, v_y_143_);
lean_dec(v_y_143_);
lean_dec(v_x_142_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
uint8_t l_Lean_Name_quickCmpAux(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
switch(lean_obj_tag(v_x_146_))
{
case 0:
{
if (lean_obj_tag(v_x_147_) == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 1;
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
case 1:
{
if (lean_obj_tag(v_x_147_) == 1)
{
lean_object* v_pre_150_; lean_object* v_str_151_; lean_object* v_pre_152_; lean_object* v_str_153_; uint8_t v___x_154_; 
v_pre_150_ = lean_ctor_get(v_x_146_, 0);
v_str_151_ = lean_ctor_get(v_x_146_, 1);
v_pre_152_ = lean_ctor_get(v_x_147_, 0);
v_str_153_ = lean_ctor_get(v_x_147_, 1);
v___x_154_ = lean_string_compare(v_str_151_, v_str_153_);
if (v___x_154_ == 1)
{
v_x_146_ = v_pre_150_;
v_x_147_ = v_pre_152_;
goto _start;
}
else
{
return v___x_154_;
}
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 2;
return v___x_156_;
}
}
default: 
{
switch(lean_obj_tag(v_x_147_))
{
case 0:
{
uint8_t v___x_157_; 
v___x_157_ = 2;
return v___x_157_;
}
case 1:
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
default: 
{
lean_object* v_pre_159_; lean_object* v_i_160_; lean_object* v_pre_161_; lean_object* v_i_162_; uint8_t v___x_163_; 
v_pre_159_ = lean_ctor_get(v_x_146_, 0);
v_i_160_ = lean_ctor_get(v_x_146_, 1);
v_pre_161_ = lean_ctor_get(v_x_147_, 0);
v_i_162_ = lean_ctor_get(v_x_147_, 1);
v___x_163_ = lean_nat_dec_lt(v_i_160_, v_i_162_);
if (v___x_163_ == 0)
{
uint8_t v___x_164_; 
v___x_164_ = lean_nat_dec_eq(v_i_160_, v_i_162_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 2;
return v___x_165_;
}
else
{
v_x_146_ = v_pre_159_;
v_x_147_ = v_pre_161_;
goto _start;
}
}
else
{
uint8_t v___x_167_; 
v___x_167_ = 0;
return v___x_167_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Name_quickCmpAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_146_ = stack[0].m_obj;
lean_object* v_x_147_ = stack[1].m_obj;
uint8_t v_res_168_;
v_res_168_ = l_Lean_Name_quickCmpAux(v_x_146_, v_x_147_);
stack->m_num = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Lean_Name_quickCmpAux(v_x_169_, v_x_170_);
lean_dec(v_x_170_);
lean_dec(v_x_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object* v_n_u2081_173_, lean_object* v_n_u2082_174_){
_start:
{
size_t v___x_175_; size_t v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_ptr_addr(v_n_u2081_173_);
v___x_176_ = lean_ptr_addr(v_n_u2082_174_);
v___x_177_ = lean_usize_dec_eq(v___x_175_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2081_173_ = stack[0].m_obj;
lean_object* v_n_u2082_174_ = stack[1].m_obj;
uint8_t v_res_178_;
v_res_178_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(v_n_u2081_173_, v_n_u2082_174_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object* v_n_u2081_179_, lean_object* v_n_u2082_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(v_n_u2081_179_, v_n_u2082_180_);
lean_dec(v_n_u2082_180_);
lean_dec(v_n_u2081_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object* v_n_u2081_183_, lean_object* v_n_u2082_184_){
_start:
{
uint64_t v___y_186_; uint64_t v___y_187_; uint64_t v___y_194_; size_t v___x_197_; size_t v___x_198_; uint8_t v___x_199_; 
v___x_197_ = lean_ptr_addr(v_n_u2081_183_);
v___x_198_ = lean_ptr_addr(v_n_u2082_184_);
v___x_199_ = lean_usize_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
if (lean_obj_tag(v_n_u2081_183_) == 0)
{
uint64_t v___x_200_; 
v___x_200_ = 1723ULL;
v___y_194_ = v___x_200_;
goto v___jp_193_;
}
else
{
uint64_t v_hash_201_; 
v_hash_201_ = lean_ctor_get_uint64(v_n_u2081_183_, sizeof(void*)*2);
v___y_194_ = v_hash_201_;
goto v___jp_193_;
}
}
else
{
uint8_t v___x_202_; 
v___x_202_ = 1;
return v___x_202_;
}
v___jp_185_:
{
uint8_t v___x_188_; 
v___x_188_ = lean_uint64_dec_lt(v___y_186_, v___y_187_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; 
v___x_189_ = lean_uint64_dec_eq(v___y_186_, v___y_187_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
v___x_190_ = 2;
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = l_Lean_Name_quickCmpAux(v_n_u2081_183_, v_n_u2082_184_);
return v___x_191_;
}
}
else
{
uint8_t v___x_192_; 
v___x_192_ = 0;
return v___x_192_;
}
}
v___jp_193_:
{
if (lean_obj_tag(v_n_u2082_184_) == 0)
{
uint64_t v___x_195_; 
v___x_195_ = 1723ULL;
v___y_186_ = v___y_194_;
v___y_187_ = v___x_195_;
goto v___jp_185_;
}
else
{
uint64_t v_hash_196_; 
v_hash_196_ = lean_ctor_get_uint64(v_n_u2082_184_, sizeof(void*)*2);
v___y_186_ = v___y_194_;
v___y_187_ = v_hash_196_;
goto v___jp_185_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2081_183_ = stack[0].m_obj;
lean_object* v_n_u2082_184_ = stack[1].m_obj;
uint8_t v_res_203_;
v_res_203_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_183_, v_n_u2082_184_);
stack->m_num = v_res_203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object* v_n_u2081_204_, lean_object* v_n_u2082_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_204_, v_n_u2082_205_);
lean_dec(v_n_u2082_205_);
lean_dec(v_n_u2081_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
uint8_t l_Lean_Name_quickLt(lean_object* v_n_u2081_208_, lean_object* v_n_u2082_209_){
_start:
{
uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_210_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_208_, v_n_u2082_209_);
v___x_211_ = lean_box(v___x_210_);
v___x_212_ = lean_obj_tag_nat(v___x_211_);
lean_dec(v___x_211_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_nat_dec_eq(v___x_212_, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT void l_Lean_Name_quickLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2081_208_ = stack[0].m_obj;
lean_object* v_n_u2082_209_ = stack[1].m_obj;
uint8_t v_res_215_;
v_res_215_ = l_Lean_Name_quickLt(v_n_u2081_208_, v_n_u2082_209_);
stack->m_num = v_res_215_;
}
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object* v_n_u2081_216_, lean_object* v_n_u2082_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Name_quickLt(v_n_u2081_216_, v_n_u2082_217_);
lean_dec(v_n_u2082_217_);
lean_dec(v_n_u2081_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
uint8_t l_Lean_Name_hasNum(lean_object* v_x_220_){
_start:
{
switch(lean_obj_tag(v_x_220_))
{
case 0:
{
uint8_t v___x_221_; 
v___x_221_ = 0;
return v___x_221_;
}
case 1:
{
lean_object* v_pre_222_; 
v_pre_222_ = lean_ctor_get(v_x_220_, 0);
v_x_220_ = v_pre_222_;
goto _start;
}
default: 
{
uint8_t v___x_224_; 
v___x_224_ = 1;
return v___x_224_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_hasNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_220_ = stack[0].m_obj;
uint8_t v_res_225_;
v_res_225_ = l_Lean_Name_hasNum(v_x_220_);
stack->m_num = v_res_225_;
}
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object* v_x_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Lean_Name_hasNum(v_x_226_);
lean_dec(v_x_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
uint8_t l_Lean_Name_isInternal(lean_object* v_x_229_){
_start:
{
switch(lean_obj_tag(v_x_229_))
{
case 1:
{
lean_object* v_pre_230_; lean_object* v_str_231_; uint32_t v___y_233_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_pre_230_ = lean_ctor_get(v_x_229_, 0);
v_str_231_ = lean_ctor_get(v_x_229_, 1);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_string_utf8_byte_size(v_str_231_);
lean_inc_ref(v_str_231_);
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v_str_231_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
v___x_240_ = l_String_Slice_Pos_get_x3f(v___x_239_, v___x_237_);
lean_dec_ref_known(v___x_239_, 3);
if (lean_obj_tag(v___x_240_) == 0)
{
uint32_t v___x_241_; 
v___x_241_ = 65;
v___y_233_ = v___x_241_;
goto v___jp_232_;
}
else
{
lean_object* v_val_242_; uint32_t v___x_243_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v___x_240_, 1);
v___x_243_ = lean_unbox_uint32(v_val_242_);
lean_dec(v_val_242_);
v___y_233_ = v___x_243_;
goto v___jp_232_;
}
v___jp_232_:
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 95;
v___x_235_ = lean_uint32_dec_eq(v___y_233_, v___x_234_);
if (v___x_235_ == 0)
{
v_x_229_ = v_pre_230_;
goto _start;
}
else
{
return v___x_235_;
}
}
}
case 2:
{
lean_object* v_pre_244_; 
v_pre_244_ = lean_ctor_get(v_x_229_, 0);
v_x_229_ = v_pre_244_;
goto _start;
}
default: 
{
uint8_t v___x_246_; 
v___x_246_ = 0;
return v___x_246_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isInternal_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_229_ = stack[0].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_Lean_Name_isInternal(v_x_229_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object* v_x_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lean_Name_isInternal(v_x_248_);
lean_dec(v_x_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
uint8_t l_Lean_Name_isInternalOrNum(lean_object* v_x_251_){
_start:
{
switch(lean_obj_tag(v_x_251_))
{
case 1:
{
lean_object* v_pre_252_; lean_object* v_str_253_; uint32_t v___y_255_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_pre_252_ = lean_ctor_get(v_x_251_, 0);
v_str_253_ = lean_ctor_get(v_x_251_, 1);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_string_utf8_byte_size(v_str_253_);
lean_inc_ref(v_str_253_);
v___x_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_261_, 0, v_str_253_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
v___x_262_ = l_String_Slice_Pos_get_x3f(v___x_261_, v___x_259_);
lean_dec_ref_known(v___x_261_, 3);
if (lean_obj_tag(v___x_262_) == 0)
{
uint32_t v___x_263_; 
v___x_263_ = 65;
v___y_255_ = v___x_263_;
goto v___jp_254_;
}
else
{
lean_object* v_val_264_; uint32_t v___x_265_; 
v_val_264_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___x_262_, 1);
v___x_265_ = lean_unbox_uint32(v_val_264_);
lean_dec(v_val_264_);
v___y_255_ = v___x_265_;
goto v___jp_254_;
}
v___jp_254_:
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 95;
v___x_257_ = lean_uint32_dec_eq(v___y_255_, v___x_256_);
if (v___x_257_ == 0)
{
v_x_251_ = v_pre_252_;
goto _start;
}
else
{
return v___x_257_;
}
}
}
case 2:
{
uint8_t v___x_266_; 
v___x_266_ = 1;
return v___x_266_;
}
default: 
{
uint8_t v___x_267_; 
v___x_267_ = 0;
return v___x_267_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isInternalOrNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_251_ = stack[0].m_obj;
uint8_t v_res_268_;
v_res_268_ = l_Lean_Name_isInternalOrNum(v_x_251_);
stack->m_num = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Lean_Name_isInternalOrNum(v_x_269_);
lean_dec(v_x_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(lean_object* v_pre_272_, lean_object* v_s_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = lean_string_utf8_byte_size(v_s_273_);
v___x_275_ = lean_string_utf8_byte_size(v_pre_272_);
v___x_276_ = lean_nat_dec_le(v___x_275_, v___x_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec_ref(v_s_273_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_string_memcmp(v_s_273_, v_pre_272_, v___x_278_, v___x_278_, v___x_275_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_s_273_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc_ref(v_s_273_);
v___x_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_281_, 0, v_s_273_);
lean_ctor_set(v___x_281_, 1, v___x_278_);
lean_ctor_set(v___x_281_, 2, v___x_274_);
v___x_282_ = l_String_Slice_pos_x21(v___x_281_, v___x_275_);
lean_dec_ref_known(v___x_281_, 3);
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v_s_273_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
lean_ctor_set(v___x_283_, 2, v___x_274_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg___boxed(lean_object* v_pre_285_, lean_object* v_s_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_285_, v_s_286_);
lean_dec_ref(v_pre_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object* v_pre_288_, lean_object* v_s_289_, lean_object* v_pat_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_288_, v_s_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object* v_pre_292_, lean_object* v_s_293_, lean_object* v_pat_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(v_pre_292_, v_s_293_, v_pat_294_);
lean_dec_ref(v_pat_294_);
lean_dec_ref(v_pre_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(lean_object* v_s_296_, lean_object* v_pos_297_){
_start:
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v_endExclusive_300_; lean_object* v___x_301_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v_decide_312_; 
v_str_298_ = lean_ctor_get(v_s_296_, 0);
v_startInclusive_299_ = lean_ctor_get(v_s_296_, 1);
v_endExclusive_300_ = lean_ctor_get(v_s_296_, 2);
v___x_301_ = lean_nat_add(v_startInclusive_299_, v_pos_297_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_nat_sub(v_endExclusive_300_, v___x_301_);
v_decide_312_ = lean_nat_dec_eq(v___x_310_, v___x_311_);
lean_dec(v___x_311_);
if (v_decide_312_ == 0)
{
uint32_t v___x_313_; uint32_t v___x_317_; uint8_t v___x_318_; 
v___x_313_ = lean_string_utf8_get_fast(v_str_298_, v___x_301_);
v___x_317_ = 48;
v___x_318_ = lean_uint32_dec_le(v___x_317_, v___x_313_);
if (v___x_318_ == 0)
{
goto v___jp_314_;
}
else
{
uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_319_ = 57;
v___x_320_ = lean_uint32_dec_le(v___x_313_, v___x_319_);
if (v___x_320_ == 0)
{
goto v___jp_314_;
}
else
{
goto v___jp_302_;
}
}
v___jp_314_:
{
uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_315_ = 95;
v___x_316_ = lean_uint32_dec_eq(v___x_313_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v___x_301_);
return v_pos_297_;
}
else
{
goto v___jp_302_;
}
}
}
else
{
lean_dec(v___x_301_);
return v_pos_297_;
}
v___jp_302_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_303_ = lean_string_utf8_next_fast(v_str_298_, v___x_301_);
v___x_304_ = lean_nat_sub(v___x_303_, v___x_301_);
lean_dec(v___x_301_);
v___x_305_ = lean_nat_add(v_pos_297_, v___x_304_);
lean_dec(v___x_304_);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_pos_297_, v___x_306_);
v___x_308_ = lean_nat_dec_le(v___x_307_, v___x_305_);
lean_dec(v___x_307_);
if (v___x_308_ == 0)
{
lean_dec(v___x_305_);
return v_pos_297_;
}
else
{
lean_dec(v_pos_297_);
v_pos_297_ = v___x_305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1___boxed(lean_object* v_s_321_, lean_object* v_pos_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_s_321_, v_pos_322_);
lean_dec_ref(v_s_321_);
return v_res_323_;
}
}
uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object* v_s_324_, lean_object* v_pre_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_325_, v_s_324_);
if (lean_obj_tag(v___x_326_) == 0)
{
uint8_t v___x_327_; 
v___x_327_ = 0;
return v___x_327_;
}
else
{
lean_object* v_val_328_; lean_object* v_startInclusive_329_; lean_object* v_endExclusive_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v_decide_334_; 
v_val_328_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_326_, 1);
v_startInclusive_329_ = lean_ctor_get(v_val_328_, 1);
lean_inc(v_startInclusive_329_);
v_endExclusive_330_ = lean_ctor_get(v_val_328_, 2);
lean_inc(v_endExclusive_330_);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_val_328_, v___x_331_);
lean_dec(v_val_328_);
v___x_333_ = lean_nat_sub(v_endExclusive_330_, v_startInclusive_329_);
lean_dec(v_startInclusive_329_);
lean_dec(v_endExclusive_330_);
v_decide_334_ = lean_nat_dec_eq(v___x_332_, v___x_333_);
lean_dec(v___x_333_);
lean_dec(v___x_332_);
return v_decide_334_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_324_ = stack[0].m_obj;
lean_object* v_pre_325_ = stack[1].m_obj;
uint8_t v_res_335_;
v_res_335_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_s_324_, v_pre_325_);
stack->m_num = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object* v_s_336_, lean_object* v_pre_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_s_336_, v_pre_337_);
lean_dec_ref(v_pre_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
uint8_t l_Lean_Name_isInternalDetail(lean_object* v_x_345_){
_start:
{
switch(lean_obj_tag(v_x_345_))
{
case 1:
{
lean_object* v_pre_346_; lean_object* v_str_347_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_pre_346_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_pre_346_);
v_str_347_ = lean_ctor_get(v_x_345_, 1);
lean_inc_ref(v_str_347_);
lean_dec_ref_known(v_x_345_, 2);
v___x_358_ = lean_string_utf8_byte_size(v_str_347_);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_dec_le(v___x_359_, v___x_358_);
if (v___x_360_ == 0)
{
goto v___jp_348_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_string_memcmp(v_str_347_, v___x_361_, v___x_362_, v___x_362_, v___x_359_);
if (v___x_363_ == 0)
{
goto v___jp_348_;
}
else
{
lean_dec_ref(v_str_347_);
lean_dec(v_pre_346_);
return v___x_363_;
}
}
v___jp_348_:
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__0));
lean_inc_ref(v_str_347_);
v___x_350_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_347_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__1));
lean_inc_ref(v_str_347_);
v___x_352_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_347_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__2));
lean_inc_ref(v_str_347_);
v___x_354_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_347_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__3));
v___x_356_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_347_, v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
v___x_357_ = l_Lean_Name_isInternalOrNum(v_pre_346_);
lean_dec(v_pre_346_);
return v___x_357_;
}
else
{
lean_dec(v_pre_346_);
return v___x_356_;
}
}
else
{
lean_dec_ref(v_str_347_);
lean_dec(v_pre_346_);
return v___x_354_;
}
}
else
{
lean_dec_ref(v_str_347_);
lean_dec(v_pre_346_);
return v___x_352_;
}
}
else
{
lean_dec_ref(v_str_347_);
lean_dec(v_pre_346_);
return v___x_350_;
}
}
}
case 2:
{
uint8_t v___x_364_; 
lean_dec_ref_known(v_x_345_, 2);
v___x_364_ = 1;
return v___x_364_;
}
default: 
{
uint8_t v___x_365_; 
v___x_365_ = l_Lean_Name_isInternalOrNum(v_x_345_);
lean_dec(v_x_345_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isInternalDetail_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_345_ = stack[0].m_obj;
uint8_t v_res_366_;
v_res_366_ = l_Lean_Name_isInternalDetail(v_x_345_);
stack->m_num = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Lean_Name_isInternalDetail(v_x_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
uint8_t l_Lean_Name_isImplementationDetail(lean_object* v_x_371_){
_start:
{
switch(lean_obj_tag(v_x_371_))
{
case 0:
{
uint8_t v___x_372_; 
v___x_372_ = 0;
return v___x_372_;
}
case 1:
{
lean_object* v_pre_373_; 
v_pre_373_ = lean_ctor_get(v_x_371_, 0);
if (lean_obj_tag(v_pre_373_) == 0)
{
lean_object* v_str_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_str_374_ = lean_ctor_get(v_x_371_, 1);
v___x_375_ = lean_string_utf8_byte_size(v_str_374_);
v___x_376_ = lean_unsigned_to_nat(2u);
v___x_377_ = lean_nat_dec_le(v___x_376_, v___x_375_);
if (v___x_377_ == 0)
{
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_string_memcmp(v_str_374_, v___x_378_, v___x_379_, v___x_379_, v___x_376_);
return v___x_380_;
}
}
else
{
v_x_371_ = v_pre_373_;
goto _start;
}
}
default: 
{
lean_object* v_pre_382_; 
v_pre_382_ = lean_ctor_get(v_x_371_, 0);
v_x_371_ = v_pre_382_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isImplementationDetail_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_371_ = stack[0].m_obj;
uint8_t v_res_384_;
v_res_384_ = l_Lean_Name_isImplementationDetail(v_x_371_);
stack->m_num = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object* v_x_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Lean_Name_isImplementationDetail(v_x_385_);
lean_dec(v_x_385_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
uint8_t l_Lean_Name_isAtomic(lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
uint8_t v___x_389_; 
v___x_389_ = 1;
return v___x_389_;
}
else
{
lean_object* v_pre_390_; 
v_pre_390_ = lean_ctor_get(v_x_388_, 0);
if (lean_obj_tag(v_pre_390_) == 0)
{
uint8_t v___x_391_; 
v___x_391_ = 1;
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = 0;
return v___x_392_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isAtomic_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_388_ = stack[0].m_obj;
uint8_t v_res_393_;
v_res_393_ = l_Lean_Name_isAtomic(v_x_388_);
stack->m_num = v_res_393_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lean_Name_isAtomic(v_x_394_);
lean_dec(v_x_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
uint8_t l_Lean_Name_isAnonymous(lean_object* v_x_397_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
uint8_t v___x_398_; 
v___x_398_ = 1;
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
v___x_399_ = 0;
return v___x_399_;
}
}
}
LEAN_EXPORT void l_Lean_Name_isAnonymous_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_397_ = stack[0].m_obj;
uint8_t v_res_400_;
v_res_400_ = l_Lean_Name_isAnonymous(v_x_397_);
stack->m_num = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object* v_x_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Lean_Name_isAnonymous(v_x_401_);
lean_dec(v_x_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
uint8_t l_Lean_Name_isStr(lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 1)
{
uint8_t v___x_405_; 
v___x_405_ = 1;
return v___x_405_;
}
else
{
uint8_t v___x_406_; 
v___x_406_ = 0;
return v___x_406_;
}
}
}
LEAN_EXPORT void l_Lean_Name_isStr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_404_ = stack[0].m_obj;
uint8_t v_res_407_;
v_res_407_ = l_Lean_Name_isStr(v_x_404_);
stack->m_num = v_res_407_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object* v_x_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Lean_Name_isStr(v_x_408_);
lean_dec(v_x_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
uint8_t l_Lean_Name_isNum(lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 2)
{
uint8_t v___x_412_; 
v___x_412_ = 1;
return v___x_412_;
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
}
}
LEAN_EXPORT void l_Lean_Name_isNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_411_ = stack[0].m_obj;
uint8_t v_res_414_;
v_res_414_ = l_Lean_Name_isNum(v_x_411_);
stack->m_num = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object* v_x_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_Name_isNum(v_x_415_);
lean_dec(v_x_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
uint8_t l_Lean_Name_anyS(lean_object* v_n_418_, lean_object* v_f_419_){
_start:
{
switch(lean_obj_tag(v_n_418_))
{
case 1:
{
lean_object* v_pre_420_; lean_object* v_str_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_pre_420_ = lean_ctor_get(v_n_418_, 0);
lean_inc(v_pre_420_);
v_str_421_ = lean_ctor_get(v_n_418_, 1);
lean_inc_ref(v_str_421_);
lean_dec_ref_known(v_n_418_, 2);
lean_inc_ref(v_f_419_);
v___x_422_ = lean_apply_1(v_f_419_, v_str_421_);
v___x_423_ = lean_unbox(v___x_422_);
if (v___x_423_ == 0)
{
v_n_418_ = v_pre_420_;
goto _start;
}
else
{
uint8_t v___x_425_; 
lean_dec(v_pre_420_);
lean_dec_ref(v_f_419_);
v___x_425_ = lean_unbox(v___x_422_);
return v___x_425_;
}
}
case 2:
{
lean_object* v_pre_426_; 
v_pre_426_ = lean_ctor_get(v_n_418_, 0);
lean_inc(v_pre_426_);
lean_dec_ref_known(v_n_418_, 2);
v_n_418_ = v_pre_426_;
goto _start;
}
default: 
{
uint8_t v___x_428_; 
lean_dec_ref(v_f_419_);
lean_dec(v_n_418_);
v___x_428_ = 0;
return v___x_428_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_anyS_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_418_ = stack[0].m_obj;
lean_object* v_f_419_ = stack[1].m_obj;
uint8_t v_res_429_;
v_res_429_ = l_Lean_Name_anyS(v_n_418_, v_f_419_);
stack->m_num = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object* v_n_430_, lean_object* v_f_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lean_Name_anyS(v_n_430_, v_f_431_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
uint8_t l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
else
{
lean_object* v_head_440_; 
v_head_440_ = lean_ctor_get(v_x_438_, 0);
if (lean_obj_tag(v_head_440_) == 1)
{
lean_object* v_pre_441_; 
v_pre_441_ = lean_ctor_get(v_head_440_, 0);
if (lean_obj_tag(v_pre_441_) == 0)
{
lean_object* v_tail_442_; lean_object* v_str_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_tail_442_ = lean_ctor_get(v_x_438_, 1);
v_str_443_ = lean_ctor_get(v_head_440_, 1);
v___x_444_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0));
v___x_445_ = lean_string_dec_eq(v_str_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1));
v___x_447_ = lean_string_dec_eq(v_str_443_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2));
v___x_449_ = lean_string_dec_eq(v_str_443_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3));
v___x_451_ = lean_string_dec_eq(v_str_443_, v___x_450_);
if (v___x_451_ == 0)
{
v_x_438_ = v_tail_442_;
goto _start;
}
else
{
return v___x_451_;
}
}
else
{
return v___x_449_;
}
}
else
{
return v___x_447_;
}
}
else
{
return v___x_445_;
}
}
else
{
lean_object* v_tail_453_; 
v_tail_453_ = lean_ctor_get(v_x_438_, 1);
v_x_438_ = v_tail_453_;
goto _start;
}
}
else
{
lean_object* v_tail_455_; 
v_tail_455_ = lean_ctor_get(v_x_438_, 1);
v_x_438_ = v_tail_455_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Name_isMetaprogramming_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_438_ = stack[0].m_obj;
uint8_t v_res_457_;
v_res_457_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_x_438_);
stack->m_num = v_res_457_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object* v_x_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_x_458_);
lean_dec(v_x_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
uint8_t l_Lean_Name_isMetaprogramming(lean_object* v_n_464_){
_start:
{
lean_object* v_components_465_; lean_object* v___x_466_; 
v_components_465_ = l_Lean_Name_components(v_n_464_);
v___x_466_ = l_List_head_x3f___redArg(v_components_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
uint8_t v___x_467_; 
v___x_467_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_465_);
lean_dec(v_components_465_);
return v___x_467_;
}
else
{
lean_object* v_val_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_val_468_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v___x_466_, 1);
v___x_469_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__1));
v___x_470_ = lean_name_eq(v_val_468_, v___x_469_);
lean_dec(v_val_468_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_465_);
lean_dec(v_components_465_);
return v___x_471_;
}
else
{
lean_dec(v_components_465_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isMetaprogramming_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_464_ = stack[0].m_obj;
uint8_t v_res_472_;
v_res_472_ = l_Lean_Name_isMetaprogramming(v_n_464_);
stack->m_num = v_res_472_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object* v_n_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Lean_Name_isMetaprogramming(v_n_473_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Name(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Name(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Name(builtin);
}
#ifdef __cplusplus
}
#endif
