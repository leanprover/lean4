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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_string_compare(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
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
static lean_once_cell_t l_Lean_Name_isInternalDetail___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Name_isInternalDetail___closed__5;
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isImplementationDetail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "__"};
static const lean_object* l_Lean_Name_isImplementationDetail___closed__0 = (const lean_object*)&l_Lean_Name_isImplementationDetail___closed__0_value;
static lean_once_cell_t l_Lean_Name_isImplementationDetail___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Name_isImplementationDetail___closed__1;
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
LEAN_EXPORT uint64_t lean_name_hash_exported(lean_object* v_a_1_){
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
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object* v_a_4_){
_start:
{
uint64_t v_res_5_; lean_object* v_r_6_; 
v_res_5_ = lean_name_hash_exported(v_a_4_);
v_r_6_ = lean_box_uint64(v_res_5_);
return v_r_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object* v_x_7_){
_start:
{
if (lean_obj_tag(v_x_7_) == 0)
{
return v_x_7_;
}
else
{
lean_object* v_pre_8_; 
v_pre_8_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_pre_8_);
return v_pre_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Name_getPrefix(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object* v_msg_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = ((lean_object*)(l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0));
v___x_14_ = lean_panic_fn_borrowed(v___x_13_, v_msg_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Name_getString_x21___closed__3(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_18_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__2));
v___x_19_ = lean_unsigned_to_nat(15u);
v___x_20_ = lean_unsigned_to_nat(31u);
v___x_21_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__1));
v___x_22_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__0));
v___x_23_ = l_mkPanicMessageWithDecl(v___x_22_, v___x_21_, v___x_20_, v___x_19_, v___x_18_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 1)
{
lean_object* v_str_25_; 
v_str_25_ = lean_ctor_get(v_x_24_, 1);
lean_inc_ref(v_str_25_);
return v_str_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lean_Name_getString_x21___closed__3, &l_Lean_Name_getString_x21___closed__3_once, _init_l_Lean_Name_getString_x21___closed__3);
v___x_27_ = l_panic___at___00Lean_Name_getString_x21_spec__0(v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Name_getString_x21(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v___x_31_; 
v___x_31_ = lean_unsigned_to_nat(0u);
return v___x_31_;
}
else
{
lean_object* v_pre_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_pre_32_ = lean_ctor_get(v_x_30_, 0);
v___x_33_ = l_Lean_Name_getNumParts(v_pre_32_);
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = lean_nat_add(v___x_33_, v___x_34_);
lean_dec(v___x_33_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Name_getNumParts(v_x_36_);
lean_dec(v_x_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
switch(lean_obj_tag(v_x_38_))
{
case 0:
{
lean_dec(v_x_39_);
return v_x_38_;
}
case 1:
{
lean_object* v_str_40_; lean_object* v___x_41_; 
v_str_40_ = lean_ctor_get(v_x_38_, 1);
lean_inc_ref(v_str_40_);
lean_dec_ref_known(v_x_38_, 2);
v___x_41_ = l_Lean_Name_str___override(v_x_39_, v_str_40_);
return v___x_41_;
}
default: 
{
lean_object* v_i_42_; lean_object* v___x_43_; 
v_i_42_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_i_42_);
lean_dec_ref_known(v_x_38_, 2);
v___x_43_ = l_Lean_Name_num___override(v_x_39_, v_i_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object* v_x_44_){
_start:
{
switch(lean_obj_tag(v_x_44_))
{
case 0:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
case 1:
{
lean_object* v_pre_46_; lean_object* v_str_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_pre_46_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_pre_46_);
v_str_47_ = lean_ctor_get(v_x_44_, 1);
lean_inc_ref(v_str_47_);
lean_dec_ref_known(v_x_44_, 2);
v___x_48_ = lean_box(0);
v___x_49_ = l_Lean_Name_str___override(v___x_48_, v_str_47_);
v___x_50_ = l_Lean_Name_componentsRev(v_pre_46_);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
default: 
{
lean_object* v_pre_52_; lean_object* v_i_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_pre_52_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_pre_52_);
v_i_53_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_i_53_);
lean_dec_ref_known(v_x_44_, 2);
v___x_54_ = lean_box(0);
v___x_55_ = l_Lean_Name_num___override(v___x_54_, v_i_53_);
v___x_56_ = l_Lean_Name_componentsRev(v_pre_52_);
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = l_Lean_Name_componentsRev(v_n_58_);
v___x_60_ = l_List_reverse___redArg(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_eqStr(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_61_) == 1)
{
lean_object* v_pre_63_; 
v_pre_63_ = lean_ctor_get(v_x_61_, 0);
if (lean_obj_tag(v_pre_63_) == 0)
{
lean_object* v_str_64_; uint8_t v___x_65_; 
v_str_64_ = lean_ctor_get(v_x_61_, 1);
v___x_65_ = lean_string_dec_eq(v_str_64_, v_x_62_);
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eqStr___boxed(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lean_Name_eqStr(v_x_68_, v_x_69_);
lean_dec_ref(v_x_69_);
lean_dec(v_x_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isPrefixOf(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = lean_name_eq(v_x_72_, v_x_73_);
return v___x_74_;
}
else
{
lean_object* v_pre_75_; uint8_t v___x_76_; 
v_pre_75_ = lean_ctor_get(v_x_73_, 0);
v___x_76_ = lean_name_eq(v_x_72_, v_x_73_);
if (v___x_76_ == 0)
{
v_x_73_ = v_pre_75_;
goto _start;
}
else
{
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Name_isPrefixOf(v_x_78_, v_x_79_);
lean_dec(v_x_79_);
lean_dec(v_x_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isSuffixOf(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
switch(lean_obj_tag(v_x_82_))
{
case 0:
{
uint8_t v___x_84_; 
v___x_84_ = 1;
return v___x_84_;
}
case 1:
{
if (lean_obj_tag(v_x_83_) == 1)
{
lean_object* v_pre_85_; lean_object* v_str_86_; lean_object* v_pre_87_; lean_object* v_str_88_; uint8_t v___x_89_; 
v_pre_85_ = lean_ctor_get(v_x_82_, 0);
v_str_86_ = lean_ctor_get(v_x_82_, 1);
v_pre_87_ = lean_ctor_get(v_x_83_, 0);
v_str_88_ = lean_ctor_get(v_x_83_, 1);
v___x_89_ = lean_string_dec_eq(v_str_86_, v_str_88_);
if (v___x_89_ == 0)
{
return v___x_89_;
}
else
{
v_x_82_ = v_pre_85_;
v_x_83_ = v_pre_87_;
goto _start;
}
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
default: 
{
if (lean_obj_tag(v_x_83_) == 2)
{
lean_object* v_pre_92_; lean_object* v_i_93_; lean_object* v_pre_94_; lean_object* v_i_95_; uint8_t v___x_96_; 
v_pre_92_ = lean_ctor_get(v_x_82_, 0);
v_i_93_ = lean_ctor_get(v_x_82_, 1);
v_pre_94_ = lean_ctor_get(v_x_83_, 0);
v_i_95_ = lean_ctor_get(v_x_83_, 1);
v___x_96_ = lean_nat_dec_eq(v_i_93_, v_i_95_);
if (v___x_96_ == 0)
{
return v___x_96_;
}
else
{
v_x_82_ = v_pre_92_;
v_x_83_ = v_pre_94_;
goto _start;
}
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lean_Name_isSuffixOf(v_x_99_, v_x_100_);
lean_dec(v_x_100_);
lean_dec(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_cmp(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
switch(lean_obj_tag(v_x_103_))
{
case 0:
{
if (lean_obj_tag(v_x_104_) == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 1;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
case 1:
{
if (lean_obj_tag(v_x_104_) == 1)
{
lean_object* v_pre_107_; lean_object* v_str_108_; lean_object* v_pre_109_; lean_object* v_str_110_; uint8_t v___x_111_; 
v_pre_107_ = lean_ctor_get(v_x_103_, 0);
v_str_108_ = lean_ctor_get(v_x_103_, 1);
v_pre_109_ = lean_ctor_get(v_x_104_, 0);
v_str_110_ = lean_ctor_get(v_x_104_, 1);
v___x_111_ = l_Lean_Name_cmp(v_pre_107_, v_pre_109_);
if (v___x_111_ == 1)
{
uint8_t v___x_112_; 
v___x_112_ = lean_string_compare(v_str_108_, v_str_110_);
return v___x_112_;
}
else
{
return v___x_111_;
}
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 2;
return v___x_113_;
}
}
default: 
{
switch(lean_obj_tag(v_x_104_))
{
case 0:
{
uint8_t v___x_114_; 
v___x_114_ = 2;
return v___x_114_;
}
case 1:
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
default: 
{
lean_object* v_pre_116_; lean_object* v_i_117_; lean_object* v_pre_118_; lean_object* v_i_119_; uint8_t v___x_120_; 
v_pre_116_ = lean_ctor_get(v_x_103_, 0);
v_i_117_ = lean_ctor_get(v_x_103_, 1);
v_pre_118_ = lean_ctor_get(v_x_104_, 0);
v_i_119_ = lean_ctor_get(v_x_104_, 1);
v___x_120_ = l_Lean_Name_cmp(v_pre_116_, v_pre_118_);
if (v___x_120_ == 1)
{
uint8_t v___x_121_; 
v___x_121_ = lean_nat_dec_lt(v_i_117_, v_i_119_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_eq(v_i_117_, v_i_119_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
else
{
return v___x_120_;
}
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
else
{
return v___x_120_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_cmp___boxed(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_Name_cmp(v_x_125_, v_x_126_);
lean_dec(v_x_126_);
lean_dec(v_x_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object* v_x_129_, lean_object* v_y_130_){
_start:
{
uint8_t v___x_131_; uint8_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_Name_cmp(v_x_129_, v_y_130_);
v___x_132_ = 0;
v___x_133_ = l_instDecidableEqOrdering(v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Lean_Name_lt(v_x_134_, v_y_135_);
lean_dec(v_y_135_);
lean_dec(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
switch(lean_obj_tag(v_x_138_))
{
case 0:
{
if (lean_obj_tag(v_x_139_) == 0)
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
case 1:
{
if (lean_obj_tag(v_x_139_) == 1)
{
lean_object* v_pre_142_; lean_object* v_str_143_; lean_object* v_pre_144_; lean_object* v_str_145_; uint8_t v___x_146_; 
v_pre_142_ = lean_ctor_get(v_x_138_, 0);
v_str_143_ = lean_ctor_get(v_x_138_, 1);
v_pre_144_ = lean_ctor_get(v_x_139_, 0);
v_str_145_ = lean_ctor_get(v_x_139_, 1);
v___x_146_ = lean_string_compare(v_str_143_, v_str_145_);
if (v___x_146_ == 1)
{
v_x_138_ = v_pre_142_;
v_x_139_ = v_pre_144_;
goto _start;
}
else
{
return v___x_146_;
}
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 2;
return v___x_148_;
}
}
default: 
{
switch(lean_obj_tag(v_x_139_))
{
case 0:
{
uint8_t v___x_149_; 
v___x_149_ = 2;
return v___x_149_;
}
case 1:
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
default: 
{
lean_object* v_pre_151_; lean_object* v_i_152_; lean_object* v_pre_153_; lean_object* v_i_154_; uint8_t v___x_155_; 
v_pre_151_ = lean_ctor_get(v_x_138_, 0);
v_i_152_ = lean_ctor_get(v_x_138_, 1);
v_pre_153_ = lean_ctor_get(v_x_139_, 0);
v_i_154_ = lean_ctor_get(v_x_139_, 1);
v___x_155_ = lean_nat_dec_lt(v_i_152_, v_i_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_eq(v_i_152_, v_i_154_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; 
v___x_157_ = 2;
return v___x_157_;
}
else
{
v_x_138_ = v_pre_151_;
v_x_139_ = v_pre_153_;
goto _start;
}
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Lean_Name_quickCmpAux(v_x_160_, v_x_161_);
lean_dec(v_x_161_);
lean_dec(v_x_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object* v_n_u2081_164_, lean_object* v_n_u2082_165_){
_start:
{
size_t v___x_166_; size_t v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_ptr_addr(v_n_u2081_164_);
v___x_167_ = lean_ptr_addr(v_n_u2082_165_);
v___x_168_ = lean_usize_dec_eq(v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object* v_n_u2081_169_, lean_object* v_n_u2082_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(v_n_u2081_169_, v_n_u2082_170_);
lean_dec(v_n_u2082_170_);
lean_dec(v_n_u2081_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object* v_n_u2081_173_, lean_object* v_n_u2082_174_){
_start:
{
uint64_t v___y_176_; uint64_t v___y_177_; uint64_t v___y_184_; size_t v___x_187_; size_t v___x_188_; uint8_t v___x_189_; 
v___x_187_ = lean_ptr_addr(v_n_u2081_173_);
v___x_188_ = lean_ptr_addr(v_n_u2082_174_);
v___x_189_ = lean_usize_dec_eq(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
if (lean_obj_tag(v_n_u2081_173_) == 0)
{
uint64_t v___x_190_; 
v___x_190_ = 1723ULL;
v___y_184_ = v___x_190_;
goto v___jp_183_;
}
else
{
uint64_t v_hash_191_; 
v_hash_191_ = lean_ctor_get_uint64(v_n_u2081_173_, sizeof(void*)*2);
v___y_184_ = v_hash_191_;
goto v___jp_183_;
}
}
else
{
uint8_t v___x_192_; 
v___x_192_ = 1;
return v___x_192_;
}
v___jp_175_:
{
uint8_t v___x_178_; 
v___x_178_ = lean_uint64_dec_lt(v___y_176_, v___y_177_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; 
v___x_179_ = lean_uint64_dec_eq(v___y_176_, v___y_177_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 2;
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = l_Lean_Name_quickCmpAux(v_n_u2081_173_, v_n_u2082_174_);
return v___x_181_;
}
}
else
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
v___jp_183_:
{
if (lean_obj_tag(v_n_u2082_174_) == 0)
{
uint64_t v___x_185_; 
v___x_185_ = 1723ULL;
v___y_176_ = v___y_184_;
v___y_177_ = v___x_185_;
goto v___jp_175_;
}
else
{
uint64_t v_hash_186_; 
v_hash_186_ = lean_ctor_get_uint64(v_n_u2082_174_, sizeof(void*)*2);
v___y_176_ = v___y_184_;
v___y_177_ = v_hash_186_;
goto v___jp_175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object* v_n_u2081_193_, lean_object* v_n_u2082_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_193_, v_n_u2082_194_);
lean_dec(v_n_u2082_194_);
lean_dec(v_n_u2081_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object* v_n_u2081_197_, lean_object* v_n_u2082_198_){
_start:
{
uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_199_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_197_, v_n_u2082_198_);
v___x_200_ = 0;
v___x_201_ = l_instDecidableEqOrdering(v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object* v_n_u2081_202_, lean_object* v_n_u2082_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Lean_Name_quickLt(v_n_u2081_202_, v_n_u2082_203_);
lean_dec(v_n_u2082_203_);
lean_dec(v_n_u2081_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object* v_x_206_){
_start:
{
switch(lean_obj_tag(v_x_206_))
{
case 0:
{
uint8_t v___x_207_; 
v___x_207_ = 0;
return v___x_207_;
}
case 1:
{
lean_object* v_pre_208_; 
v_pre_208_ = lean_ctor_get(v_x_206_, 0);
v_x_206_ = v_pre_208_;
goto _start;
}
default: 
{
uint8_t v___x_210_; 
v___x_210_ = 1;
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object* v_x_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Lean_Name_hasNum(v_x_211_);
lean_dec(v_x_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object* v_x_214_){
_start:
{
switch(lean_obj_tag(v_x_214_))
{
case 1:
{
lean_object* v_pre_215_; lean_object* v_str_216_; uint32_t v___y_218_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_pre_215_ = lean_ctor_get(v_x_214_, 0);
v_str_216_ = lean_ctor_get(v_x_214_, 1);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_string_utf8_byte_size(v_str_216_);
lean_inc_ref(v_str_216_);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v_str_216_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set(v___x_224_, 2, v___x_223_);
v___x_225_ = l_String_Slice_Pos_get_x3f(v___x_224_, v___x_222_);
lean_dec_ref_known(v___x_224_, 3);
if (lean_obj_tag(v___x_225_) == 0)
{
uint32_t v___x_226_; 
v___x_226_ = 65;
v___y_218_ = v___x_226_;
goto v___jp_217_;
}
else
{
lean_object* v_val_227_; uint32_t v___x_228_; 
v_val_227_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_225_, 1);
v___x_228_ = lean_unbox_uint32(v_val_227_);
lean_dec(v_val_227_);
v___y_218_ = v___x_228_;
goto v___jp_217_;
}
v___jp_217_:
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 95;
v___x_220_ = lean_uint32_dec_eq(v___y_218_, v___x_219_);
if (v___x_220_ == 0)
{
v_x_214_ = v_pre_215_;
goto _start;
}
else
{
return v___x_220_;
}
}
}
case 2:
{
lean_object* v_pre_229_; 
v_pre_229_ = lean_ctor_get(v_x_214_, 0);
v_x_214_ = v_pre_229_;
goto _start;
}
default: 
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object* v_x_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Lean_Name_isInternal(v_x_232_);
lean_dec(v_x_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object* v_x_235_){
_start:
{
switch(lean_obj_tag(v_x_235_))
{
case 1:
{
lean_object* v_pre_236_; lean_object* v_str_237_; uint32_t v___y_239_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_pre_236_ = lean_ctor_get(v_x_235_, 0);
v_str_237_ = lean_ctor_get(v_x_235_, 1);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_string_utf8_byte_size(v_str_237_);
lean_inc_ref(v_str_237_);
v___x_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_245_, 0, v_str_237_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
v___x_246_ = l_String_Slice_Pos_get_x3f(v___x_245_, v___x_243_);
lean_dec_ref_known(v___x_245_, 3);
if (lean_obj_tag(v___x_246_) == 0)
{
uint32_t v___x_247_; 
v___x_247_ = 65;
v___y_239_ = v___x_247_;
goto v___jp_238_;
}
else
{
lean_object* v_val_248_; uint32_t v___x_249_; 
v_val_248_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v___x_246_, 1);
v___x_249_ = lean_unbox_uint32(v_val_248_);
lean_dec(v_val_248_);
v___y_239_ = v___x_249_;
goto v___jp_238_;
}
v___jp_238_:
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 95;
v___x_241_ = lean_uint32_dec_eq(v___y_239_, v___x_240_);
if (v___x_241_ == 0)
{
v_x_235_ = v_pre_236_;
goto _start;
}
else
{
return v___x_241_;
}
}
}
case 2:
{
uint8_t v___x_250_; 
v___x_250_ = 1;
return v___x_250_;
}
default: 
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object* v_x_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Lean_Name_isInternalOrNum(v_x_252_);
lean_dec(v_x_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(lean_object* v_pre_255_, lean_object* v_s_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_string_utf8_byte_size(v_s_256_);
v___x_258_ = lean_string_utf8_byte_size(v_pre_255_);
v___x_259_ = lean_nat_dec_le(v___x_258_, v___x_257_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec_ref(v_s_256_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_string_memcmp(v_s_256_, v_pre_255_, v___x_261_, v___x_261_, v___x_258_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec_ref(v_s_256_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc_ref(v_s_256_);
v___x_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_264_, 0, v_s_256_);
lean_ctor_set(v___x_264_, 1, v___x_261_);
lean_ctor_set(v___x_264_, 2, v___x_257_);
v___x_265_ = l_String_Slice_pos_x21(v___x_264_, v___x_258_);
lean_dec_ref_known(v___x_264_, 3);
v___x_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_266_, 0, v_s_256_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_ctor_set(v___x_266_, 2, v___x_257_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg___boxed(lean_object* v_pre_268_, lean_object* v_s_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_268_, v_s_269_);
lean_dec_ref(v_pre_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object* v_pre_271_, lean_object* v_s_272_, lean_object* v_pat_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_271_, v_s_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object* v_pre_275_, lean_object* v_s_276_, lean_object* v_pat_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(v_pre_275_, v_s_276_, v_pat_277_);
lean_dec_ref(v_pat_277_);
lean_dec_ref(v_pre_275_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(lean_object* v_s_279_, lean_object* v_pos_280_){
_start:
{
lean_object* v_str_281_; lean_object* v_startInclusive_282_; lean_object* v_endExclusive_283_; lean_object* v___x_284_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_str_281_ = lean_ctor_get(v_s_279_, 0);
v_startInclusive_282_ = lean_ctor_get(v_s_279_, 1);
v_endExclusive_283_ = lean_ctor_get(v_s_279_, 2);
v___x_284_ = lean_nat_add(v_startInclusive_282_, v_pos_280_);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_nat_sub(v_endExclusive_283_, v___x_284_);
v___x_293_ = lean_nat_dec_eq(v___x_291_, v___x_292_);
lean_dec(v___x_292_);
if (v___x_293_ == 0)
{
uint32_t v___x_294_; uint8_t v___y_296_; uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_294_ = lean_string_utf8_get_fast(v_str_281_, v___x_284_);
v___x_299_ = 48;
v___x_300_ = lean_uint32_dec_le(v___x_299_, v___x_294_);
if (v___x_300_ == 0)
{
v___y_296_ = v___x_300_;
goto v___jp_295_;
}
else
{
uint32_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = 57;
v___x_302_ = lean_uint32_dec_le(v___x_294_, v___x_301_);
v___y_296_ = v___x_302_;
goto v___jp_295_;
}
v___jp_295_:
{
if (v___y_296_ == 0)
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 95;
v___x_298_ = lean_uint32_dec_eq(v___x_294_, v___x_297_);
if (v___x_298_ == 0)
{
lean_dec(v___x_284_);
return v_pos_280_;
}
else
{
goto v___jp_285_;
}
}
else
{
goto v___jp_285_;
}
}
}
else
{
lean_dec(v___x_284_);
return v_pos_280_;
}
v___jp_285_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_286_ = lean_string_utf8_next_fast(v_str_281_, v___x_284_);
v___x_287_ = lean_nat_sub(v___x_286_, v___x_284_);
lean_dec(v___x_284_);
v___x_288_ = lean_nat_add(v_pos_280_, v___x_287_);
lean_dec(v___x_287_);
v___x_289_ = lean_nat_dec_lt(v_pos_280_, v___x_288_);
if (v___x_289_ == 0)
{
lean_dec(v___x_288_);
return v_pos_280_;
}
else
{
lean_dec(v_pos_280_);
v_pos_280_ = v___x_288_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1___boxed(lean_object* v_s_303_, lean_object* v_pos_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_s_303_, v_pos_304_);
lean_dec_ref(v_s_303_);
return v_res_305_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object* v_s_306_, lean_object* v_pre_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_307_, v_s_306_);
if (lean_obj_tag(v___x_308_) == 0)
{
uint8_t v___x_309_; 
v___x_309_ = 0;
return v___x_309_;
}
else
{
lean_object* v_val_310_; lean_object* v_startInclusive_311_; lean_object* v_endExclusive_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_val_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v___x_308_, 1);
v_startInclusive_311_ = lean_ctor_get(v_val_310_, 1);
lean_inc(v_startInclusive_311_);
v_endExclusive_312_ = lean_ctor_get(v_val_310_, 2);
lean_inc(v_endExclusive_312_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_val_310_, v___x_313_);
lean_dec(v_val_310_);
v___x_315_ = lean_nat_sub(v_endExclusive_312_, v_startInclusive_311_);
lean_dec(v_startInclusive_311_);
lean_dec(v_endExclusive_312_);
v___x_316_ = lean_nat_dec_eq(v___x_314_, v___x_315_);
lean_dec(v___x_315_);
lean_dec(v___x_314_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object* v_s_317_, lean_object* v_pre_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_s_317_, v_pre_318_);
lean_dec_ref(v_pre_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
static lean_object* _init_l_Lean_Name_isInternalDetail___closed__5(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_327_ = lean_string_utf8_byte_size(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object* v_x_328_){
_start:
{
switch(lean_obj_tag(v_x_328_))
{
case 1:
{
lean_object* v_pre_329_; lean_object* v_str_330_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_pre_329_ = lean_ctor_get(v_x_328_, 0);
lean_inc(v_pre_329_);
v_str_330_ = lean_ctor_get(v_x_328_, 1);
lean_inc_ref(v_str_330_);
lean_dec_ref_known(v_x_328_, 2);
v___x_341_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_342_ = lean_string_utf8_byte_size(v_str_330_);
v___x_343_ = lean_obj_once(&l_Lean_Name_isInternalDetail___closed__5, &l_Lean_Name_isInternalDetail___closed__5_once, _init_l_Lean_Name_isInternalDetail___closed__5);
v___x_344_ = lean_nat_dec_le(v___x_343_, v___x_342_);
if (v___x_344_ == 0)
{
goto v___jp_331_;
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_string_memcmp(v_str_330_, v___x_341_, v___x_345_, v___x_345_, v___x_343_);
if (v___x_346_ == 0)
{
goto v___jp_331_;
}
else
{
lean_dec_ref(v_str_330_);
lean_dec(v_pre_329_);
return v___x_346_;
}
}
v___jp_331_:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__0));
lean_inc_ref(v_str_330_);
v___x_333_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_330_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__1));
lean_inc_ref(v_str_330_);
v___x_335_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_330_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__2));
lean_inc_ref(v_str_330_);
v___x_337_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_330_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__3));
v___x_339_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_330_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_Name_isInternalOrNum(v_pre_329_);
lean_dec(v_pre_329_);
return v___x_340_;
}
else
{
lean_dec(v_pre_329_);
return v___x_339_;
}
}
else
{
lean_dec_ref(v_str_330_);
lean_dec(v_pre_329_);
return v___x_337_;
}
}
else
{
lean_dec_ref(v_str_330_);
lean_dec(v_pre_329_);
return v___x_335_;
}
}
else
{
lean_dec_ref(v_str_330_);
lean_dec(v_pre_329_);
return v___x_333_;
}
}
}
case 2:
{
uint8_t v___x_347_; 
lean_dec_ref_known(v_x_328_, 2);
v___x_347_ = 1;
return v___x_347_;
}
default: 
{
uint8_t v___x_348_; 
v___x_348_ = l_Lean_Name_isInternalOrNum(v_x_328_);
lean_dec(v_x_328_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object* v_x_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Lean_Name_isInternalDetail(v_x_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
static lean_object* _init_l_Lean_Name_isImplementationDetail___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_354_ = lean_string_utf8_byte_size(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isImplementationDetail(lean_object* v_x_355_){
_start:
{
switch(lean_obj_tag(v_x_355_))
{
case 0:
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
case 1:
{
lean_object* v_pre_357_; 
v_pre_357_ = lean_ctor_get(v_x_355_, 0);
if (lean_obj_tag(v_pre_357_) == 0)
{
lean_object* v_str_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_str_358_ = lean_ctor_get(v_x_355_, 1);
v___x_359_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_360_ = lean_string_utf8_byte_size(v_str_358_);
v___x_361_ = lean_obj_once(&l_Lean_Name_isImplementationDetail___closed__1, &l_Lean_Name_isImplementationDetail___closed__1_once, _init_l_Lean_Name_isImplementationDetail___closed__1);
v___x_362_ = lean_nat_dec_le(v___x_361_, v___x_360_);
if (v___x_362_ == 0)
{
return v___x_362_;
}
else
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_string_memcmp(v_str_358_, v___x_359_, v___x_363_, v___x_363_, v___x_361_);
return v___x_364_;
}
}
else
{
v_x_355_ = v_pre_357_;
goto _start;
}
}
default: 
{
lean_object* v_pre_366_; 
v_pre_366_ = lean_ctor_get(v_x_355_, 0);
v_x_355_ = v_pre_366_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object* v_x_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Lean_Name_isImplementationDetail(v_x_368_);
lean_dec(v_x_368_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAtomic(lean_object* v_x_371_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
uint8_t v___x_372_; 
v___x_372_ = 1;
return v___x_372_;
}
else
{
lean_object* v_pre_373_; 
v_pre_373_ = lean_ctor_get(v_x_371_, 0);
if (lean_obj_tag(v_pre_373_) == 0)
{
uint8_t v___x_374_; 
v___x_374_ = 1;
return v___x_374_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object* v_x_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lean_Name_isAtomic(v_x_376_);
lean_dec(v_x_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAnonymous(lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
uint8_t v___x_380_; 
v___x_380_ = 1;
return v___x_380_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = 0;
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object* v_x_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Lean_Name_isAnonymous(v_x_382_);
lean_dec(v_x_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isStr(lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 1)
{
uint8_t v___x_386_; 
v___x_386_ = 1;
return v___x_386_;
}
else
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object* v_x_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_Name_isStr(v_x_388_);
lean_dec(v_x_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isNum(lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_391_) == 2)
{
uint8_t v___x_392_; 
v___x_392_ = 1;
return v___x_392_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lean_Name_isNum(v_x_394_);
lean_dec(v_x_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_anyS(lean_object* v_n_397_, lean_object* v_f_398_){
_start:
{
switch(lean_obj_tag(v_n_397_))
{
case 1:
{
lean_object* v_pre_399_; lean_object* v_str_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_pre_399_ = lean_ctor_get(v_n_397_, 0);
lean_inc(v_pre_399_);
v_str_400_ = lean_ctor_get(v_n_397_, 1);
lean_inc_ref(v_str_400_);
lean_dec_ref_known(v_n_397_, 2);
lean_inc_ref(v_f_398_);
v___x_401_ = lean_apply_1(v_f_398_, v_str_400_);
v___x_402_ = lean_unbox(v___x_401_);
if (v___x_402_ == 0)
{
v_n_397_ = v_pre_399_;
goto _start;
}
else
{
uint8_t v___x_404_; 
lean_dec(v_pre_399_);
lean_dec_ref(v_f_398_);
v___x_404_ = lean_unbox(v___x_401_);
return v___x_404_;
}
}
case 2:
{
lean_object* v_pre_405_; 
v_pre_405_ = lean_ctor_get(v_n_397_, 0);
lean_inc(v_pre_405_);
lean_dec_ref_known(v_n_397_, 2);
v_n_397_ = v_pre_405_;
goto _start;
}
default: 
{
uint8_t v___x_407_; 
lean_dec_ref(v_f_398_);
lean_dec(v_n_397_);
v___x_407_ = 0;
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object* v_n_408_, lean_object* v_f_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Lean_Name_anyS(v_n_408_, v_f_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
else
{
lean_object* v_head_418_; 
v_head_418_ = lean_ctor_get(v_x_416_, 0);
if (lean_obj_tag(v_head_418_) == 1)
{
lean_object* v_pre_419_; 
v_pre_419_ = lean_ctor_get(v_head_418_, 0);
if (lean_obj_tag(v_pre_419_) == 0)
{
lean_object* v_tail_420_; lean_object* v_str_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_tail_420_ = lean_ctor_get(v_x_416_, 1);
v_str_421_ = lean_ctor_get(v_head_418_, 1);
v___x_422_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0));
v___x_423_ = lean_string_dec_eq(v_str_421_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1));
v___x_425_ = lean_string_dec_eq(v_str_421_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2));
v___x_427_ = lean_string_dec_eq(v_str_421_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3));
v___x_429_ = lean_string_dec_eq(v_str_421_, v___x_428_);
if (v___x_429_ == 0)
{
v_x_416_ = v_tail_420_;
goto _start;
}
else
{
return v___x_429_;
}
}
else
{
return v___x_427_;
}
}
else
{
return v___x_425_;
}
}
else
{
return v___x_423_;
}
}
else
{
lean_object* v_tail_431_; 
v_tail_431_ = lean_ctor_get(v_x_416_, 1);
v_x_416_ = v_tail_431_;
goto _start;
}
}
else
{
lean_object* v_tail_433_; 
v_tail_433_ = lean_ctor_get(v_x_416_, 1);
v_x_416_ = v_tail_433_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object* v_x_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_x_435_);
lean_dec(v_x_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object* v_n_441_){
_start:
{
lean_object* v_components_442_; lean_object* v___x_443_; 
v_components_442_ = l_Lean_Name_components(v_n_441_);
v___x_443_ = l_List_head_x3f___redArg(v_components_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
uint8_t v___x_444_; 
v___x_444_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_442_);
lean_dec(v_components_442_);
return v___x_444_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_val_445_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v___x_443_, 1);
v___x_446_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__1));
v___x_447_ = lean_name_eq(v_val_445_, v___x_446_);
lean_dec(v_val_445_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
v___x_448_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_442_);
lean_dec(v_components_442_);
return v___x_448_;
}
else
{
lean_dec(v_components_442_);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object* v_n_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Lean_Name_isMetaprogramming(v_n_449_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
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
