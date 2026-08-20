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
lean_object* l_Ordering_ctorIdx(uint8_t);
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
static lean_once_cell_t l_Lean_Name_lt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Name_lt___closed__0;
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
static lean_object* _init_l_Lean_Name_lt___closed__0(void){
_start:
{
uint8_t v___x_129_; lean_object* v___x_130_; 
v___x_129_ = 0;
v___x_130_ = l_Ordering_ctorIdx(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object* v_x_131_, lean_object* v_y_132_){
_start:
{
uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = l_Lean_Name_cmp(v_x_131_, v_y_132_);
v___x_134_ = l_Ordering_ctorIdx(v___x_133_);
v___x_135_ = lean_obj_once(&l_Lean_Name_lt___closed__0, &l_Lean_Name_lt___closed__0_once, _init_l_Lean_Name_lt___closed__0);
v___x_136_ = lean_nat_dec_eq(v___x_134_, v___x_135_);
lean_dec(v___x_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object* v_x_137_, lean_object* v_y_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Name_lt(v_x_137_, v_y_138_);
lean_dec(v_y_138_);
lean_dec(v_x_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
if (lean_obj_tag(v_x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 1;
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
case 1:
{
if (lean_obj_tag(v_x_142_) == 1)
{
lean_object* v_pre_145_; lean_object* v_str_146_; lean_object* v_pre_147_; lean_object* v_str_148_; uint8_t v___x_149_; 
v_pre_145_ = lean_ctor_get(v_x_141_, 0);
v_str_146_ = lean_ctor_get(v_x_141_, 1);
v_pre_147_ = lean_ctor_get(v_x_142_, 0);
v_str_148_ = lean_ctor_get(v_x_142_, 1);
v___x_149_ = lean_string_compare(v_str_146_, v_str_148_);
if (v___x_149_ == 1)
{
v_x_141_ = v_pre_145_;
v_x_142_ = v_pre_147_;
goto _start;
}
else
{
return v___x_149_;
}
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 2;
return v___x_151_;
}
}
default: 
{
switch(lean_obj_tag(v_x_142_))
{
case 0:
{
uint8_t v___x_152_; 
v___x_152_ = 2;
return v___x_152_;
}
case 1:
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
default: 
{
lean_object* v_pre_154_; lean_object* v_i_155_; lean_object* v_pre_156_; lean_object* v_i_157_; uint8_t v___x_158_; 
v_pre_154_ = lean_ctor_get(v_x_141_, 0);
v_i_155_ = lean_ctor_get(v_x_141_, 1);
v_pre_156_ = lean_ctor_get(v_x_142_, 0);
v_i_157_ = lean_ctor_get(v_x_142_, 1);
v___x_158_ = lean_nat_dec_lt(v_i_155_, v_i_157_);
if (v___x_158_ == 0)
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_eq(v_i_155_, v_i_157_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = 2;
return v___x_160_;
}
else
{
v_x_141_ = v_pre_154_;
v_x_142_ = v_pre_156_;
goto _start;
}
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_Name_quickCmpAux(v_x_163_, v_x_164_);
lean_dec(v_x_164_);
lean_dec(v_x_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object* v_n_u2081_167_, lean_object* v_n_u2082_168_){
_start:
{
size_t v___x_169_; size_t v___x_170_; uint8_t v___x_171_; 
v___x_169_ = lean_ptr_addr(v_n_u2081_167_);
v___x_170_ = lean_ptr_addr(v_n_u2082_168_);
v___x_171_ = lean_usize_dec_eq(v___x_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object* v_n_u2081_172_, lean_object* v_n_u2082_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(v_n_u2081_172_, v_n_u2082_173_);
lean_dec(v_n_u2082_173_);
lean_dec(v_n_u2081_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object* v_n_u2081_176_, lean_object* v_n_u2082_177_){
_start:
{
uint64_t v___y_179_; uint64_t v___y_180_; uint64_t v___y_187_; size_t v___x_190_; size_t v___x_191_; uint8_t v___x_192_; 
v___x_190_ = lean_ptr_addr(v_n_u2081_176_);
v___x_191_ = lean_ptr_addr(v_n_u2082_177_);
v___x_192_ = lean_usize_dec_eq(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
if (lean_obj_tag(v_n_u2081_176_) == 0)
{
uint64_t v___x_193_; 
v___x_193_ = 1723ULL;
v___y_187_ = v___x_193_;
goto v___jp_186_;
}
else
{
uint64_t v_hash_194_; 
v_hash_194_ = lean_ctor_get_uint64(v_n_u2081_176_, sizeof(void*)*2);
v___y_187_ = v_hash_194_;
goto v___jp_186_;
}
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 1;
return v___x_195_;
}
v___jp_178_:
{
uint8_t v___x_181_; 
v___x_181_ = lean_uint64_dec_lt(v___y_179_, v___y_180_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; 
v___x_182_ = lean_uint64_dec_eq(v___y_179_, v___y_180_);
if (v___x_182_ == 0)
{
uint8_t v___x_183_; 
v___x_183_ = 2;
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = l_Lean_Name_quickCmpAux(v_n_u2081_176_, v_n_u2082_177_);
return v___x_184_;
}
}
else
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
v___jp_186_:
{
if (lean_obj_tag(v_n_u2082_177_) == 0)
{
uint64_t v___x_188_; 
v___x_188_ = 1723ULL;
v___y_179_ = v___y_187_;
v___y_180_ = v___x_188_;
goto v___jp_178_;
}
else
{
uint64_t v_hash_189_; 
v_hash_189_ = lean_ctor_get_uint64(v_n_u2082_177_, sizeof(void*)*2);
v___y_179_ = v___y_187_;
v___y_180_ = v_hash_189_;
goto v___jp_178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object* v_n_u2081_196_, lean_object* v_n_u2082_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_196_, v_n_u2082_197_);
lean_dec(v_n_u2082_197_);
lean_dec(v_n_u2081_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object* v_n_u2081_200_, lean_object* v_n_u2082_201_){
_start:
{
uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_202_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_200_, v_n_u2082_201_);
v___x_203_ = l_Ordering_ctorIdx(v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_Name_lt___closed__0, &l_Lean_Name_lt___closed__0_once, _init_l_Lean_Name_lt___closed__0);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object* v_n_u2081_206_, lean_object* v_n_u2082_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_Name_quickLt(v_n_u2081_206_, v_n_u2082_207_);
lean_dec(v_n_u2082_207_);
lean_dec(v_n_u2081_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object* v_x_210_){
_start:
{
switch(lean_obj_tag(v_x_210_))
{
case 0:
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
case 1:
{
lean_object* v_pre_212_; 
v_pre_212_ = lean_ctor_get(v_x_210_, 0);
v_x_210_ = v_pre_212_;
goto _start;
}
default: 
{
uint8_t v___x_214_; 
v___x_214_ = 1;
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object* v_x_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Lean_Name_hasNum(v_x_215_);
lean_dec(v_x_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object* v_x_218_){
_start:
{
switch(lean_obj_tag(v_x_218_))
{
case 1:
{
lean_object* v_pre_219_; lean_object* v_str_220_; uint32_t v___y_222_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_pre_219_ = lean_ctor_get(v_x_218_, 0);
v_str_220_ = lean_ctor_get(v_x_218_, 1);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_string_utf8_byte_size(v_str_220_);
lean_inc_ref(v_str_220_);
v___x_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_228_, 0, v_str_220_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_227_);
v___x_229_ = l_String_Slice_Pos_get_x3f(v___x_228_, v___x_226_);
lean_dec_ref_known(v___x_228_, 3);
if (lean_obj_tag(v___x_229_) == 0)
{
uint32_t v___x_230_; 
v___x_230_ = 65;
v___y_222_ = v___x_230_;
goto v___jp_221_;
}
else
{
lean_object* v_val_231_; uint32_t v___x_232_; 
v_val_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_229_, 1);
v___x_232_ = lean_unbox_uint32(v_val_231_);
lean_dec(v_val_231_);
v___y_222_ = v___x_232_;
goto v___jp_221_;
}
v___jp_221_:
{
uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 95;
v___x_224_ = lean_uint32_dec_eq(v___y_222_, v___x_223_);
if (v___x_224_ == 0)
{
v_x_218_ = v_pre_219_;
goto _start;
}
else
{
return v___x_224_;
}
}
}
case 2:
{
lean_object* v_pre_233_; 
v_pre_233_ = lean_ctor_get(v_x_218_, 0);
v_x_218_ = v_pre_233_;
goto _start;
}
default: 
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object* v_x_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Lean_Name_isInternal(v_x_236_);
lean_dec(v_x_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object* v_x_239_){
_start:
{
switch(lean_obj_tag(v_x_239_))
{
case 1:
{
lean_object* v_pre_240_; lean_object* v_str_241_; uint32_t v___y_243_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_pre_240_ = lean_ctor_get(v_x_239_, 0);
v_str_241_ = lean_ctor_get(v_x_239_, 1);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_string_utf8_byte_size(v_str_241_);
lean_inc_ref(v_str_241_);
v___x_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_249_, 0, v_str_241_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_248_);
v___x_250_ = l_String_Slice_Pos_get_x3f(v___x_249_, v___x_247_);
lean_dec_ref_known(v___x_249_, 3);
if (lean_obj_tag(v___x_250_) == 0)
{
uint32_t v___x_251_; 
v___x_251_ = 65;
v___y_243_ = v___x_251_;
goto v___jp_242_;
}
else
{
lean_object* v_val_252_; uint32_t v___x_253_; 
v_val_252_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_val_252_);
lean_dec_ref_known(v___x_250_, 1);
v___x_253_ = lean_unbox_uint32(v_val_252_);
lean_dec(v_val_252_);
v___y_243_ = v___x_253_;
goto v___jp_242_;
}
v___jp_242_:
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 95;
v___x_245_ = lean_uint32_dec_eq(v___y_243_, v___x_244_);
if (v___x_245_ == 0)
{
v_x_239_ = v_pre_240_;
goto _start;
}
else
{
return v___x_245_;
}
}
}
case 2:
{
uint8_t v___x_254_; 
v___x_254_ = 1;
return v___x_254_;
}
default: 
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object* v_x_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Lean_Name_isInternalOrNum(v_x_256_);
lean_dec(v_x_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(lean_object* v_pre_259_, lean_object* v_s_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_string_utf8_byte_size(v_s_260_);
v___x_262_ = lean_string_utf8_byte_size(v_pre_259_);
v___x_263_ = lean_nat_dec_le(v___x_262_, v___x_261_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v_s_260_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_string_memcmp(v_s_260_, v_pre_259_, v___x_265_, v___x_265_, v___x_262_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_dec_ref(v_s_260_);
v___x_267_ = lean_box(0);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_inc_ref(v_s_260_);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v_s_260_);
lean_ctor_set(v___x_268_, 1, v___x_265_);
lean_ctor_set(v___x_268_, 2, v___x_261_);
v___x_269_ = l_String_Slice_pos_x21(v___x_268_, v___x_262_);
lean_dec_ref_known(v___x_268_, 3);
v___x_270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_270_, 0, v_s_260_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_ctor_set(v___x_270_, 2, v___x_261_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg___boxed(lean_object* v_pre_272_, lean_object* v_s_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_272_, v_s_273_);
lean_dec_ref(v_pre_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object* v_pre_275_, lean_object* v_s_276_, lean_object* v_pat_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_275_, v_s_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object* v_pre_279_, lean_object* v_s_280_, lean_object* v_pat_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(v_pre_279_, v_s_280_, v_pat_281_);
lean_dec_ref(v_pat_281_);
lean_dec_ref(v_pre_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(lean_object* v_s_283_, lean_object* v_pos_284_){
_start:
{
lean_object* v_str_285_; lean_object* v_startInclusive_286_; lean_object* v_endExclusive_287_; lean_object* v___x_288_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v_decide_299_; 
v_str_285_ = lean_ctor_get(v_s_283_, 0);
v_startInclusive_286_ = lean_ctor_get(v_s_283_, 1);
v_endExclusive_287_ = lean_ctor_get(v_s_283_, 2);
v___x_288_ = lean_nat_add(v_startInclusive_286_, v_pos_284_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_nat_sub(v_endExclusive_287_, v___x_288_);
v_decide_299_ = lean_nat_dec_eq(v___x_297_, v___x_298_);
lean_dec(v___x_298_);
if (v_decide_299_ == 0)
{
uint32_t v___x_300_; uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_300_ = lean_string_utf8_get_fast(v_str_285_, v___x_288_);
v___x_304_ = 48;
v___x_305_ = lean_uint32_dec_le(v___x_304_, v___x_300_);
if (v___x_305_ == 0)
{
goto v___jp_301_;
}
else
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 57;
v___x_307_ = lean_uint32_dec_le(v___x_300_, v___x_306_);
if (v___x_307_ == 0)
{
goto v___jp_301_;
}
else
{
goto v___jp_289_;
}
}
v___jp_301_:
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 95;
v___x_303_ = lean_uint32_dec_eq(v___x_300_, v___x_302_);
if (v___x_303_ == 0)
{
lean_dec(v___x_288_);
return v_pos_284_;
}
else
{
goto v___jp_289_;
}
}
}
else
{
lean_dec(v___x_288_);
return v_pos_284_;
}
v___jp_289_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_290_ = lean_string_utf8_next_fast(v_str_285_, v___x_288_);
v___x_291_ = lean_nat_sub(v___x_290_, v___x_288_);
lean_dec(v___x_288_);
v___x_292_ = lean_nat_add(v_pos_284_, v___x_291_);
lean_dec(v___x_291_);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_pos_284_, v___x_293_);
v___x_295_ = lean_nat_dec_le(v___x_294_, v___x_292_);
lean_dec(v___x_294_);
if (v___x_295_ == 0)
{
lean_dec(v___x_292_);
return v_pos_284_;
}
else
{
lean_dec(v_pos_284_);
v_pos_284_ = v___x_292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1___boxed(lean_object* v_s_308_, lean_object* v_pos_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_s_308_, v_pos_309_);
lean_dec_ref(v_s_308_);
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object* v_s_311_, lean_object* v_pre_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_312_, v_s_311_);
if (lean_obj_tag(v___x_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
else
{
lean_object* v_val_315_; lean_object* v_startInclusive_316_; lean_object* v_endExclusive_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v_decide_321_; 
v_val_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___x_313_, 1);
v_startInclusive_316_ = lean_ctor_get(v_val_315_, 1);
lean_inc(v_startInclusive_316_);
v_endExclusive_317_ = lean_ctor_get(v_val_315_, 2);
lean_inc(v_endExclusive_317_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_val_315_, v___x_318_);
lean_dec(v_val_315_);
v___x_320_ = lean_nat_sub(v_endExclusive_317_, v_startInclusive_316_);
lean_dec(v_startInclusive_316_);
lean_dec(v_endExclusive_317_);
v_decide_321_ = lean_nat_dec_eq(v___x_319_, v___x_320_);
lean_dec(v___x_320_);
lean_dec(v___x_319_);
return v_decide_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object* v_s_322_, lean_object* v_pre_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_s_322_, v_pre_323_);
lean_dec_ref(v_pre_323_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
static lean_object* _init_l_Lean_Name_isInternalDetail___closed__5(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_332_ = lean_string_utf8_byte_size(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object* v_x_333_){
_start:
{
switch(lean_obj_tag(v_x_333_))
{
case 1:
{
lean_object* v_pre_334_; lean_object* v_str_335_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_pre_334_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_pre_334_);
v_str_335_ = lean_ctor_get(v_x_333_, 1);
lean_inc_ref(v_str_335_);
lean_dec_ref_known(v_x_333_, 2);
v___x_346_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_347_ = lean_string_utf8_byte_size(v_str_335_);
v___x_348_ = lean_obj_once(&l_Lean_Name_isInternalDetail___closed__5, &l_Lean_Name_isInternalDetail___closed__5_once, _init_l_Lean_Name_isInternalDetail___closed__5);
v___x_349_ = lean_nat_dec_le(v___x_348_, v___x_347_);
if (v___x_349_ == 0)
{
goto v___jp_336_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_string_memcmp(v_str_335_, v___x_346_, v___x_350_, v___x_350_, v___x_348_);
if (v___x_351_ == 0)
{
goto v___jp_336_;
}
else
{
lean_dec_ref(v_str_335_);
lean_dec(v_pre_334_);
return v___x_351_;
}
}
v___jp_336_:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__0));
lean_inc_ref(v_str_335_);
v___x_338_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_335_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__1));
lean_inc_ref(v_str_335_);
v___x_340_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_335_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__2));
lean_inc_ref(v_str_335_);
v___x_342_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_335_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__3));
v___x_344_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_335_, v___x_343_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = l_Lean_Name_isInternalOrNum(v_pre_334_);
lean_dec(v_pre_334_);
return v___x_345_;
}
else
{
lean_dec(v_pre_334_);
return v___x_344_;
}
}
else
{
lean_dec_ref(v_str_335_);
lean_dec(v_pre_334_);
return v___x_342_;
}
}
else
{
lean_dec_ref(v_str_335_);
lean_dec(v_pre_334_);
return v___x_340_;
}
}
else
{
lean_dec_ref(v_str_335_);
lean_dec(v_pre_334_);
return v___x_338_;
}
}
}
case 2:
{
uint8_t v___x_352_; 
lean_dec_ref_known(v_x_333_, 2);
v___x_352_ = 1;
return v___x_352_;
}
default: 
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_Name_isInternalOrNum(v_x_333_);
lean_dec(v_x_333_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object* v_x_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_Name_isInternalDetail(v_x_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
static lean_object* _init_l_Lean_Name_isImplementationDetail___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_359_ = lean_string_utf8_byte_size(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isImplementationDetail(lean_object* v_x_360_){
_start:
{
switch(lean_obj_tag(v_x_360_))
{
case 0:
{
uint8_t v___x_361_; 
v___x_361_ = 0;
return v___x_361_;
}
case 1:
{
lean_object* v_pre_362_; 
v_pre_362_ = lean_ctor_get(v_x_360_, 0);
if (lean_obj_tag(v_pre_362_) == 0)
{
lean_object* v_str_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_str_363_ = lean_ctor_get(v_x_360_, 1);
v___x_364_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_365_ = lean_string_utf8_byte_size(v_str_363_);
v___x_366_ = lean_obj_once(&l_Lean_Name_isImplementationDetail___closed__1, &l_Lean_Name_isImplementationDetail___closed__1_once, _init_l_Lean_Name_isImplementationDetail___closed__1);
v___x_367_ = lean_nat_dec_le(v___x_366_, v___x_365_);
if (v___x_367_ == 0)
{
return v___x_367_;
}
else
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_string_memcmp(v_str_363_, v___x_364_, v___x_368_, v___x_368_, v___x_366_);
return v___x_369_;
}
}
else
{
v_x_360_ = v_pre_362_;
goto _start;
}
}
default: 
{
lean_object* v_pre_371_; 
v_pre_371_ = lean_ctor_get(v_x_360_, 0);
v_x_360_ = v_pre_371_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object* v_x_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Lean_Name_isImplementationDetail(v_x_373_);
lean_dec(v_x_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAtomic(lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
uint8_t v___x_377_; 
v___x_377_ = 1;
return v___x_377_;
}
else
{
lean_object* v_pre_378_; 
v_pre_378_ = lean_ctor_get(v_x_376_, 0);
if (lean_obj_tag(v_pre_378_) == 0)
{
uint8_t v___x_379_; 
v___x_379_ = 1;
return v___x_379_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 0;
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Lean_Name_isAtomic(v_x_381_);
lean_dec(v_x_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAnonymous(lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
uint8_t v___x_385_; 
v___x_385_ = 1;
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object* v_x_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Name_isAnonymous(v_x_387_);
lean_dec(v_x_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isStr(lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object* v_x_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Lean_Name_isStr(v_x_393_);
lean_dec(v_x_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isNum(lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_396_) == 2)
{
uint8_t v___x_397_; 
v___x_397_ = 1;
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lean_Name_isNum(v_x_399_);
lean_dec(v_x_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_anyS(lean_object* v_n_402_, lean_object* v_f_403_){
_start:
{
switch(lean_obj_tag(v_n_402_))
{
case 1:
{
lean_object* v_pre_404_; lean_object* v_str_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_pre_404_ = lean_ctor_get(v_n_402_, 0);
lean_inc(v_pre_404_);
v_str_405_ = lean_ctor_get(v_n_402_, 1);
lean_inc_ref(v_str_405_);
lean_dec_ref_known(v_n_402_, 2);
lean_inc_ref(v_f_403_);
v___x_406_ = lean_apply_1(v_f_403_, v_str_405_);
v___x_407_ = lean_unbox(v___x_406_);
if (v___x_407_ == 0)
{
v_n_402_ = v_pre_404_;
goto _start;
}
else
{
uint8_t v___x_409_; 
lean_dec(v_pre_404_);
lean_dec_ref(v_f_403_);
v___x_409_ = lean_unbox(v___x_406_);
return v___x_409_;
}
}
case 2:
{
lean_object* v_pre_410_; 
v_pre_410_ = lean_ctor_get(v_n_402_, 0);
lean_inc(v_pre_410_);
lean_dec_ref_known(v_n_402_, 2);
v_n_402_ = v_pre_410_;
goto _start;
}
default: 
{
uint8_t v___x_412_; 
lean_dec_ref(v_f_403_);
lean_dec(v_n_402_);
v___x_412_ = 0;
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object* v_n_413_, lean_object* v_f_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Lean_Name_anyS(v_n_413_, v_f_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(lean_object* v_x_421_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
else
{
lean_object* v_head_423_; 
v_head_423_ = lean_ctor_get(v_x_421_, 0);
if (lean_obj_tag(v_head_423_) == 1)
{
lean_object* v_pre_424_; 
v_pre_424_ = lean_ctor_get(v_head_423_, 0);
if (lean_obj_tag(v_pre_424_) == 0)
{
lean_object* v_tail_425_; lean_object* v_str_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_tail_425_ = lean_ctor_get(v_x_421_, 1);
v_str_426_ = lean_ctor_get(v_head_423_, 1);
v___x_427_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0));
v___x_428_ = lean_string_dec_eq(v_str_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1));
v___x_430_ = lean_string_dec_eq(v_str_426_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2));
v___x_432_ = lean_string_dec_eq(v_str_426_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = ((lean_object*)(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3));
v___x_434_ = lean_string_dec_eq(v_str_426_, v___x_433_);
if (v___x_434_ == 0)
{
v_x_421_ = v_tail_425_;
goto _start;
}
else
{
return v___x_434_;
}
}
else
{
return v___x_432_;
}
}
else
{
return v___x_430_;
}
}
else
{
return v___x_428_;
}
}
else
{
lean_object* v_tail_436_; 
v_tail_436_ = lean_ctor_get(v_x_421_, 1);
v_x_421_ = v_tail_436_;
goto _start;
}
}
else
{
lean_object* v_tail_438_; 
v_tail_438_ = lean_ctor_get(v_x_421_, 1);
v_x_421_ = v_tail_438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object* v_x_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_x_440_);
lean_dec(v_x_440_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object* v_n_446_){
_start:
{
lean_object* v_components_447_; lean_object* v___x_448_; 
v_components_447_ = l_Lean_Name_components(v_n_446_);
v___x_448_ = l_List_head_x3f___redArg(v_components_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
uint8_t v___x_449_; 
v___x_449_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_447_);
lean_dec(v_components_447_);
return v___x_449_;
}
else
{
lean_object* v_val_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_val_450_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_448_, 1);
v___x_451_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__1));
v___x_452_ = lean_name_eq(v_val_450_, v___x_451_);
lean_dec(v_val_450_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; 
v___x_453_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_447_);
lean_dec(v_components_447_);
return v___x_453_;
}
else
{
lean_dec(v_components_447_);
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object* v_n_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Lean_Name_isMetaprogramming(v_n_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
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
