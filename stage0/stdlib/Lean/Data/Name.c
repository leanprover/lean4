// Lean compiler output
// Module: Lean.Data.Name
// Imports: public import Init.Data.Ord.Basic import Init.Data.String.TakeDrop import Init.Data.Ord.String import Init.Data.Ord.UInt import Init.Data.String.Search
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
static lean_once_cell_t l_Lean_Name_hashEx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Name_hashEx___closed__0;
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Name_isMetaprogramming___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__0 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__0_value;
static const lean_string_object l_Lean_Name_isMetaprogramming___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__1 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__1_value;
static const lean_string_object l_Lean_Name_isMetaprogramming___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__2 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__2_value;
static const lean_string_object l_Lean_Name_isMetaprogramming___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__3 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__3_value;
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Name_isMetaprogramming___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_isMetaprogramming___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_isMetaprogramming___closed__0 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__0_value;
static const lean_string_object l_Lean_Name_isMetaprogramming___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__1 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__1_value;
static const lean_ctor_object l_Lean_Name_isMetaprogramming___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Name_isMetaprogramming___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__2 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object*);
static uint64_t _init_l_Lean_Name_hashEx___closed__0(void){
_start:
{
lean_object* v___x_1_; uint64_t v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1723u);
v___x_2_ = lean_uint64_of_nat(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint64_t lean_name_hash_exported(lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_3_) == 0)
{
uint64_t v___x_4_; 
v___x_4_ = lean_uint64_once(&l_Lean_Name_hashEx___closed__0, &l_Lean_Name_hashEx___closed__0_once, _init_l_Lean_Name_hashEx___closed__0);
return v___x_4_;
}
else
{
uint64_t v_hash_5_; 
v_hash_5_ = lean_ctor_get_uint64(v_a_3_, sizeof(void*)*2);
lean_dec(v_a_3_);
return v_hash_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object* v_a_6_){
_start:
{
uint64_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lean_name_hash_exported(v_a_6_);
v_r_8_ = lean_box_uint64(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
return v_x_9_;
}
else
{
lean_object* v_pre_10_; 
v_pre_10_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_pre_10_);
return v_pre_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Name_getPrefix(v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object* v_msg_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = ((lean_object*)(l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0));
v___x_16_ = lean_panic_fn_borrowed(v___x_15_, v_msg_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Name_getString_x21___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_20_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__2));
v___x_21_ = lean_unsigned_to_nat(15u);
v___x_22_ = lean_unsigned_to_nat(30u);
v___x_23_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__1));
v___x_24_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__0));
v___x_25_ = l_mkPanicMessageWithDecl(v___x_24_, v___x_23_, v___x_22_, v___x_21_, v___x_20_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_26_) == 1)
{
lean_object* v_str_27_; 
v_str_27_ = lean_ctor_get(v_x_26_, 1);
lean_inc_ref(v_str_27_);
return v_str_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l_Lean_Name_getString_x21___closed__3, &l_Lean_Name_getString_x21___closed__3_once, _init_l_Lean_Name_getString_x21___closed__3);
v___x_29_ = l_panic___at___00Lean_Name_getString_x21_spec__0(v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object* v_x_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Name_getString_x21(v_x_30_);
lean_dec(v_x_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_unsigned_to_nat(0u);
return v___x_33_;
}
else
{
lean_object* v_pre_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_pre_34_ = lean_ctor_get(v_x_32_, 0);
v___x_35_ = l_Lean_Name_getNumParts(v_pre_34_);
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_nat_add(v___x_35_, v___x_36_);
lean_dec(v___x_35_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Name_getNumParts(v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
switch(lean_obj_tag(v_x_40_))
{
case 0:
{
lean_dec(v_x_41_);
return v_x_40_;
}
case 1:
{
lean_object* v_str_42_; lean_object* v___x_43_; 
v_str_42_ = lean_ctor_get(v_x_40_, 1);
lean_inc_ref(v_str_42_);
lean_dec_ref(v_x_40_);
v___x_43_ = l_Lean_Name_str___override(v_x_41_, v_str_42_);
return v___x_43_;
}
default: 
{
lean_object* v_i_44_; lean_object* v___x_45_; 
v_i_44_ = lean_ctor_get(v_x_40_, 1);
lean_inc(v_i_44_);
lean_dec_ref(v_x_40_);
v___x_45_ = l_Lean_Name_num___override(v_x_41_, v_i_44_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object* v_x_46_){
_start:
{
switch(lean_obj_tag(v_x_46_))
{
case 0:
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
case 1:
{
lean_object* v_pre_48_; lean_object* v_str_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_pre_48_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_pre_48_);
v_str_49_ = lean_ctor_get(v_x_46_, 1);
lean_inc_ref(v_str_49_);
lean_dec_ref(v_x_46_);
v___x_50_ = lean_box(0);
v___x_51_ = l_Lean_Name_str___override(v___x_50_, v_str_49_);
v___x_52_ = l_Lean_Name_componentsRev(v_pre_48_);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
return v___x_53_;
}
default: 
{
lean_object* v_pre_54_; lean_object* v_i_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_pre_54_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_pre_54_);
v_i_55_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_i_55_);
lean_dec_ref(v_x_46_);
v___x_56_ = lean_box(0);
v___x_57_ = l_Lean_Name_num___override(v___x_56_, v_i_55_);
v___x_58_ = l_Lean_Name_componentsRev(v_pre_54_);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object* v_n_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = l_Lean_Name_componentsRev(v_n_60_);
v___x_62_ = l_List_reverse___redArg(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_eqStr(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_63_) == 1)
{
lean_object* v_pre_65_; 
v_pre_65_ = lean_ctor_get(v_x_63_, 0);
if (lean_obj_tag(v_pre_65_) == 0)
{
lean_object* v_str_66_; uint8_t v___x_67_; 
v_str_66_ = lean_ctor_get(v_x_63_, 1);
v___x_67_ = lean_string_dec_eq(v_str_66_, v_x_64_);
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
}
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
LEAN_EXPORT uint8_t l_Lean_Name_isPrefixOf(lean_object* v_x_74_, lean_object* v_x_75_){
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
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lean_Name_isPrefixOf(v_x_80_, v_x_81_);
lean_dec(v_x_81_);
lean_dec(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isSuffixOf(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
uint8_t v___x_86_; 
v___x_86_ = 1;
return v___x_86_;
}
case 1:
{
if (lean_obj_tag(v_x_85_) == 1)
{
lean_object* v_pre_87_; lean_object* v_str_88_; lean_object* v_pre_89_; lean_object* v_str_90_; uint8_t v___x_91_; 
v_pre_87_ = lean_ctor_get(v_x_84_, 0);
v_str_88_ = lean_ctor_get(v_x_84_, 1);
v_pre_89_ = lean_ctor_get(v_x_85_, 0);
v_str_90_ = lean_ctor_get(v_x_85_, 1);
v___x_91_ = lean_string_dec_eq(v_str_88_, v_str_90_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
v_x_84_ = v_pre_87_;
v_x_85_ = v_pre_89_;
goto _start;
}
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
default: 
{
if (lean_obj_tag(v_x_85_) == 2)
{
lean_object* v_pre_94_; lean_object* v_i_95_; lean_object* v_pre_96_; lean_object* v_i_97_; uint8_t v___x_98_; 
v_pre_94_ = lean_ctor_get(v_x_84_, 0);
v_i_95_ = lean_ctor_get(v_x_84_, 1);
v_pre_96_ = lean_ctor_get(v_x_85_, 0);
v_i_97_ = lean_ctor_get(v_x_85_, 1);
v___x_98_ = lean_nat_dec_eq(v_i_95_, v_i_97_);
if (v___x_98_ == 0)
{
return v___x_98_;
}
else
{
v_x_84_ = v_pre_94_;
v_x_85_ = v_pre_96_;
goto _start;
}
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_Name_isSuffixOf(v_x_101_, v_x_102_);
lean_dec(v_x_102_);
lean_dec(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_cmp(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
switch(lean_obj_tag(v_x_105_))
{
case 0:
{
if (lean_obj_tag(v_x_106_) == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
case 1:
{
if (lean_obj_tag(v_x_106_) == 1)
{
lean_object* v_pre_109_; lean_object* v_str_110_; lean_object* v_pre_111_; lean_object* v_str_112_; uint8_t v___x_113_; 
v_pre_109_ = lean_ctor_get(v_x_105_, 0);
v_str_110_ = lean_ctor_get(v_x_105_, 1);
v_pre_111_ = lean_ctor_get(v_x_106_, 0);
v_str_112_ = lean_ctor_get(v_x_106_, 1);
v___x_113_ = l_Lean_Name_cmp(v_pre_109_, v_pre_111_);
if (v___x_113_ == 1)
{
uint8_t v___x_114_; 
v___x_114_ = lean_string_dec_lt(v_str_110_, v_str_112_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = lean_string_dec_eq(v_str_110_, v_str_112_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; 
v___x_116_ = 2;
return v___x_116_;
}
else
{
return v___x_113_;
}
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
else
{
return v___x_113_;
}
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 2;
return v___x_118_;
}
}
default: 
{
switch(lean_obj_tag(v_x_106_))
{
case 0:
{
uint8_t v___x_119_; 
v___x_119_ = 2;
return v___x_119_;
}
case 1:
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
default: 
{
lean_object* v_pre_121_; lean_object* v_i_122_; lean_object* v_pre_123_; lean_object* v_i_124_; uint8_t v___x_125_; 
v_pre_121_ = lean_ctor_get(v_x_105_, 0);
v_i_122_ = lean_ctor_get(v_x_105_, 1);
v_pre_123_ = lean_ctor_get(v_x_106_, 0);
v_i_124_ = lean_ctor_get(v_x_106_, 1);
v___x_125_ = l_Lean_Name_cmp(v_pre_121_, v_pre_123_);
if (v___x_125_ == 1)
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_lt(v_i_122_, v_i_124_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_eq(v_i_122_, v_i_124_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 2;
return v___x_128_;
}
else
{
return v___x_125_;
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
else
{
return v___x_125_;
}
}
}
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v___x_136_; uint8_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = l_Lean_Name_cmp(v_x_134_, v_y_135_);
v___x_137_ = 0;
v___x_138_ = l_instDecidableEqOrdering(v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object* v_x_139_, lean_object* v_y_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Lean_Name_lt(v_x_139_, v_y_140_);
lean_dec(v_y_140_);
lean_dec(v_x_139_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
switch(lean_obj_tag(v_x_143_))
{
case 0:
{
if (lean_obj_tag(v_x_144_) == 0)
{
uint8_t v___x_145_; 
v___x_145_ = 1;
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
case 1:
{
if (lean_obj_tag(v_x_144_) == 1)
{
lean_object* v_pre_147_; lean_object* v_str_148_; lean_object* v_pre_149_; lean_object* v_str_150_; uint8_t v___x_151_; 
v_pre_147_ = lean_ctor_get(v_x_143_, 0);
v_str_148_ = lean_ctor_get(v_x_143_, 1);
v_pre_149_ = lean_ctor_get(v_x_144_, 0);
v_str_150_ = lean_ctor_get(v_x_144_, 1);
v___x_151_ = lean_string_dec_lt(v_str_148_, v_str_150_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; 
v___x_152_ = lean_string_dec_eq(v_str_148_, v_str_150_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 2;
return v___x_153_;
}
else
{
v_x_143_ = v_pre_147_;
v_x_144_ = v_pre_149_;
goto _start;
}
}
else
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
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
switch(lean_obj_tag(v_x_144_))
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
v_pre_159_ = lean_ctor_get(v_x_143_, 0);
v_i_160_ = lean_ctor_get(v_x_143_, 1);
v_pre_161_ = lean_ctor_get(v_x_144_, 0);
v_i_162_ = lean_ctor_get(v_x_144_, 1);
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
v_x_143_ = v_pre_159_;
v_x_144_ = v_pre_161_;
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
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Lean_Name_quickCmpAux(v_x_168_, v_x_169_);
lean_dec(v_x_169_);
lean_dec(v_x_168_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object* v_n_u2081_172_, lean_object* v_n_u2082_173_){
_start:
{
size_t v___x_174_; size_t v___x_175_; uint8_t v___x_176_; 
v___x_174_ = lean_ptr_addr(v_n_u2081_172_);
v___x_175_ = lean_ptr_addr(v_n_u2082_173_);
v___x_176_ = lean_usize_dec_eq(v___x_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object* v_n_u2081_177_, lean_object* v_n_u2082_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(v_n_u2081_177_, v_n_u2082_178_);
lean_dec(v_n_u2082_178_);
lean_dec(v_n_u2081_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object* v_n_u2081_181_, lean_object* v_n_u2082_182_){
_start:
{
uint64_t v___y_184_; uint64_t v___y_185_; uint64_t v___y_192_; uint8_t v___x_195_; 
v___x_195_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(v_n_u2081_181_, v_n_u2082_182_);
if (v___x_195_ == 0)
{
if (lean_obj_tag(v_n_u2081_181_) == 0)
{
uint64_t v___x_196_; 
v___x_196_ = lean_uint64_once(&l_Lean_Name_hashEx___closed__0, &l_Lean_Name_hashEx___closed__0_once, _init_l_Lean_Name_hashEx___closed__0);
v___y_192_ = v___x_196_;
goto v___jp_191_;
}
else
{
uint64_t v_hash_197_; 
v_hash_197_ = lean_ctor_get_uint64(v_n_u2081_181_, sizeof(void*)*2);
v___y_192_ = v_hash_197_;
goto v___jp_191_;
}
}
else
{
uint8_t v___x_198_; 
v___x_198_ = 1;
return v___x_198_;
}
v___jp_183_:
{
uint8_t v___x_186_; 
v___x_186_ = lean_uint64_dec_lt(v___y_184_, v___y_185_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
v___x_187_ = lean_uint64_dec_eq(v___y_184_, v___y_185_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 2;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = l_Lean_Name_quickCmpAux(v_n_u2081_181_, v_n_u2082_182_);
return v___x_189_;
}
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
v___jp_191_:
{
if (lean_obj_tag(v_n_u2082_182_) == 0)
{
uint64_t v___x_193_; 
v___x_193_ = lean_uint64_once(&l_Lean_Name_hashEx___closed__0, &l_Lean_Name_hashEx___closed__0_once, _init_l_Lean_Name_hashEx___closed__0);
v___y_184_ = v___y_192_;
v___y_185_ = v___x_193_;
goto v___jp_183_;
}
else
{
uint64_t v_hash_194_; 
v_hash_194_ = lean_ctor_get_uint64(v_n_u2082_182_, sizeof(void*)*2);
v___y_184_ = v___y_192_;
v___y_185_ = v_hash_194_;
goto v___jp_183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object* v_n_u2081_199_, lean_object* v_n_u2082_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_199_, v_n_u2082_200_);
lean_dec(v_n_u2082_200_);
lean_dec(v_n_u2081_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object* v_n_u2081_203_, lean_object* v_n_u2082_204_){
_start:
{
uint8_t v___x_205_; uint8_t v___x_206_; uint8_t v___x_207_; 
v___x_205_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_203_, v_n_u2082_204_);
v___x_206_ = 0;
v___x_207_ = l_instDecidableEqOrdering(v___x_205_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object* v_n_u2081_208_, lean_object* v_n_u2082_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_Name_quickLt(v_n_u2081_208_, v_n_u2082_209_);
lean_dec(v_n_u2082_209_);
lean_dec(v_n_u2081_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object* v_x_212_){
_start:
{
switch(lean_obj_tag(v_x_212_))
{
case 0:
{
uint8_t v___x_213_; 
v___x_213_ = 0;
return v___x_213_;
}
case 1:
{
lean_object* v_pre_214_; 
v_pre_214_ = lean_ctor_get(v_x_212_, 0);
v_x_212_ = v_pre_214_;
goto _start;
}
default: 
{
uint8_t v___x_216_; 
v___x_216_ = 1;
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Name_hasNum(v_x_217_);
lean_dec(v_x_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object* v_x_220_){
_start:
{
switch(lean_obj_tag(v_x_220_))
{
case 1:
{
lean_object* v_pre_221_; lean_object* v_str_222_; uint32_t v___y_224_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_pre_221_ = lean_ctor_get(v_x_220_, 0);
v_str_222_ = lean_ctor_get(v_x_220_, 1);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_string_utf8_byte_size(v_str_222_);
lean_inc_ref(v_str_222_);
v___x_230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_230_, 0, v_str_222_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
v___x_231_ = l_String_Slice_Pos_get_x3f(v___x_230_, v___x_228_);
lean_dec_ref(v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
uint32_t v___x_232_; 
v___x_232_ = 65;
v___y_224_ = v___x_232_;
goto v___jp_223_;
}
else
{
lean_object* v_val_233_; uint32_t v___x_234_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_233_);
lean_dec_ref(v___x_231_);
v___x_234_ = lean_unbox_uint32(v_val_233_);
lean_dec(v_val_233_);
v___y_224_ = v___x_234_;
goto v___jp_223_;
}
v___jp_223_:
{
uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 95;
v___x_226_ = lean_uint32_dec_eq(v___y_224_, v___x_225_);
if (v___x_226_ == 0)
{
v_x_220_ = v_pre_221_;
goto _start;
}
else
{
return v___x_226_;
}
}
}
case 2:
{
lean_object* v_pre_235_; 
v_pre_235_ = lean_ctor_get(v_x_220_, 0);
v_x_220_ = v_pre_235_;
goto _start;
}
default: 
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object* v_x_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Lean_Name_isInternal(v_x_238_);
lean_dec(v_x_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object* v_x_241_){
_start:
{
switch(lean_obj_tag(v_x_241_))
{
case 1:
{
lean_object* v_pre_242_; lean_object* v_str_243_; uint32_t v___y_245_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_pre_242_ = lean_ctor_get(v_x_241_, 0);
v_str_243_ = lean_ctor_get(v_x_241_, 1);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_string_utf8_byte_size(v_str_243_);
lean_inc_ref(v_str_243_);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v_str_243_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
lean_ctor_set(v___x_251_, 2, v___x_250_);
v___x_252_ = l_String_Slice_Pos_get_x3f(v___x_251_, v___x_249_);
lean_dec_ref(v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
uint32_t v___x_253_; 
v___x_253_ = 65;
v___y_245_ = v___x_253_;
goto v___jp_244_;
}
else
{
lean_object* v_val_254_; uint32_t v___x_255_; 
v_val_254_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_val_254_);
lean_dec_ref(v___x_252_);
v___x_255_ = lean_unbox_uint32(v_val_254_);
lean_dec(v_val_254_);
v___y_245_ = v___x_255_;
goto v___jp_244_;
}
v___jp_244_:
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 95;
v___x_247_ = lean_uint32_dec_eq(v___y_245_, v___x_246_);
if (v___x_247_ == 0)
{
v_x_241_ = v_pre_242_;
goto _start;
}
else
{
return v___x_247_;
}
}
}
case 2:
{
uint8_t v___x_256_; 
v___x_256_ = 1;
return v___x_256_;
}
default: 
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_Name_isInternalOrNum(v_x_258_);
lean_dec(v_x_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object* v_s_261_, lean_object* v_pos_262_){
_start:
{
lean_object* v_str_263_; lean_object* v_startInclusive_264_; lean_object* v_endExclusive_265_; lean_object* v___x_266_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_str_263_ = lean_ctor_get(v_s_261_, 0);
v_startInclusive_264_ = lean_ctor_get(v_s_261_, 1);
v_endExclusive_265_ = lean_ctor_get(v_s_261_, 2);
v___x_266_ = lean_nat_add(v_startInclusive_264_, v_pos_262_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_nat_sub(v_endExclusive_265_, v___x_266_);
v___x_275_ = lean_nat_dec_eq(v___x_273_, v___x_274_);
lean_dec(v___x_274_);
if (v___x_275_ == 0)
{
uint32_t v___x_276_; uint8_t v___y_278_; uint32_t v___x_281_; uint8_t v___x_282_; 
v___x_276_ = lean_string_utf8_get_fast(v_str_263_, v___x_266_);
v___x_281_ = 48;
v___x_282_ = lean_uint32_dec_le(v___x_281_, v___x_276_);
if (v___x_282_ == 0)
{
v___y_278_ = v___x_282_;
goto v___jp_277_;
}
else
{
uint32_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 57;
v___x_284_ = lean_uint32_dec_le(v___x_276_, v___x_283_);
v___y_278_ = v___x_284_;
goto v___jp_277_;
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = 95;
v___x_280_ = lean_uint32_dec_eq(v___x_276_, v___x_279_);
if (v___x_280_ == 0)
{
lean_dec(v___x_266_);
return v_pos_262_;
}
else
{
goto v___jp_267_;
}
}
else
{
goto v___jp_267_;
}
}
}
else
{
lean_dec(v___x_266_);
return v_pos_262_;
}
v___jp_267_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_268_ = lean_string_utf8_next_fast(v_str_263_, v___x_266_);
v___x_269_ = lean_nat_sub(v___x_268_, v___x_266_);
lean_dec(v___x_266_);
v___x_270_ = lean_nat_add(v_pos_262_, v___x_269_);
lean_dec(v___x_269_);
v___x_271_ = lean_nat_dec_lt(v_pos_262_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v___x_270_);
return v_pos_262_;
}
else
{
lean_dec(v_pos_262_);
v_pos_262_ = v___x_270_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object* v_s_285_, lean_object* v_pos_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(v_s_285_, v_pos_286_);
lean_dec_ref(v_s_285_);
return v_res_287_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object* v_s_288_, lean_object* v_pre_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_string_utf8_byte_size(v_s_288_);
v___x_291_ = lean_string_utf8_byte_size(v_pre_289_);
v___x_292_ = lean_nat_dec_le(v___x_291_, v___x_290_);
if (v___x_292_ == 0)
{
lean_dec_ref(v_s_288_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_string_memcmp(v_s_288_, v_pre_289_, v___x_293_, v___x_293_, v___x_291_);
if (v___x_294_ == 0)
{
lean_dec_ref(v_s_288_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_295_ = lean_string_length(v_pre_289_);
lean_inc_ref(v_s_288_);
v___x_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_296_, 0, v_s_288_);
lean_ctor_set(v___x_296_, 1, v___x_293_);
lean_ctor_set(v___x_296_, 2, v___x_290_);
v___x_297_ = l_String_Slice_Pos_nextn(v___x_296_, v___x_293_, v___x_295_);
lean_dec_ref(v___x_296_);
lean_inc(v___x_297_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v_s_288_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_ctor_set(v___x_298_, 2, v___x_290_);
v___x_299_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(v___x_298_, v___x_293_);
lean_dec_ref(v___x_298_);
v___x_300_ = lean_nat_sub(v___x_290_, v___x_297_);
lean_dec(v___x_297_);
v___x_301_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
lean_dec(v___x_300_);
lean_dec(v___x_299_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object* v_s_302_, lean_object* v_pre_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_s_302_, v_pre_303_);
lean_dec_ref(v_pre_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
static lean_object* _init_l_Lean_Name_isInternalDetail___closed__5(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_312_ = lean_string_utf8_byte_size(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object* v_x_313_){
_start:
{
switch(lean_obj_tag(v_x_313_))
{
case 1:
{
lean_object* v_pre_314_; lean_object* v_str_315_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_pre_314_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_pre_314_);
v_str_315_ = lean_ctor_get(v_x_313_, 1);
lean_inc_ref(v_str_315_);
lean_dec_ref(v_x_313_);
v___x_326_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_327_ = lean_string_utf8_byte_size(v_str_315_);
v___x_328_ = lean_obj_once(&l_Lean_Name_isInternalDetail___closed__5, &l_Lean_Name_isInternalDetail___closed__5_once, _init_l_Lean_Name_isInternalDetail___closed__5);
v___x_329_ = lean_nat_dec_le(v___x_328_, v___x_327_);
if (v___x_329_ == 0)
{
goto v___jp_316_;
}
else
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_string_memcmp(v_str_315_, v___x_326_, v___x_330_, v___x_330_, v___x_328_);
if (v___x_331_ == 0)
{
goto v___jp_316_;
}
else
{
lean_dec_ref(v_str_315_);
lean_dec(v_pre_314_);
return v___x_331_;
}
}
v___jp_316_:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__0));
lean_inc_ref(v_str_315_);
v___x_318_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_315_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__1));
lean_inc_ref(v_str_315_);
v___x_320_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_315_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__2));
lean_inc_ref(v_str_315_);
v___x_322_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_315_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__3));
v___x_324_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_315_, v___x_323_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = l_Lean_Name_isInternalOrNum(v_pre_314_);
lean_dec(v_pre_314_);
return v___x_325_;
}
else
{
lean_dec(v_pre_314_);
return v___x_324_;
}
}
else
{
lean_dec_ref(v_str_315_);
lean_dec(v_pre_314_);
return v___x_322_;
}
}
else
{
lean_dec_ref(v_str_315_);
lean_dec(v_pre_314_);
return v___x_320_;
}
}
else
{
lean_dec_ref(v_str_315_);
lean_dec(v_pre_314_);
return v___x_318_;
}
}
}
case 2:
{
uint8_t v___x_332_; 
lean_dec_ref(v_x_313_);
v___x_332_ = 1;
return v___x_332_;
}
default: 
{
uint8_t v___x_333_; 
v___x_333_ = l_Lean_Name_isInternalOrNum(v_x_313_);
lean_dec(v_x_313_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_Name_isInternalDetail(v_x_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
static lean_object* _init_l_Lean_Name_isImplementationDetail___closed__1(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_339_ = lean_string_utf8_byte_size(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isImplementationDetail(lean_object* v_x_340_){
_start:
{
switch(lean_obj_tag(v_x_340_))
{
case 0:
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
case 1:
{
lean_object* v_pre_342_; 
v_pre_342_ = lean_ctor_get(v_x_340_, 0);
if (lean_obj_tag(v_pre_342_) == 0)
{
lean_object* v_str_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_str_343_ = lean_ctor_get(v_x_340_, 1);
v___x_344_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_345_ = lean_string_utf8_byte_size(v_str_343_);
v___x_346_ = lean_obj_once(&l_Lean_Name_isImplementationDetail___closed__1, &l_Lean_Name_isImplementationDetail___closed__1_once, _init_l_Lean_Name_isImplementationDetail___closed__1);
v___x_347_ = lean_nat_dec_le(v___x_346_, v___x_345_);
if (v___x_347_ == 0)
{
return v___x_347_;
}
else
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_string_memcmp(v_str_343_, v___x_344_, v___x_348_, v___x_348_, v___x_346_);
return v___x_349_;
}
}
else
{
v_x_340_ = v_pre_342_;
goto _start;
}
}
default: 
{
lean_object* v_pre_351_; 
v_pre_351_ = lean_ctor_get(v_x_340_, 0);
v_x_340_ = v_pre_351_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object* v_x_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l_Lean_Name_isImplementationDetail(v_x_353_);
lean_dec(v_x_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAtomic(lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
uint8_t v___x_357_; 
v___x_357_ = 1;
return v___x_357_;
}
else
{
lean_object* v_pre_358_; 
v_pre_358_ = lean_ctor_get(v_x_356_, 0);
if (lean_obj_tag(v_pre_358_) == 0)
{
uint8_t v___x_359_; 
v___x_359_ = 1;
return v___x_359_;
}
else
{
uint8_t v___x_360_; 
v___x_360_ = 0;
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_Name_isAtomic(v_x_361_);
lean_dec(v_x_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAnonymous(lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
uint8_t v___x_365_; 
v___x_365_ = 1;
return v___x_365_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = 0;
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Lean_Name_isAnonymous(v_x_367_);
lean_dec(v_x_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isStr(lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 1)
{
uint8_t v___x_371_; 
v___x_371_ = 1;
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = 0;
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object* v_x_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Lean_Name_isStr(v_x_373_);
lean_dec(v_x_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isNum(lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 2)
{
uint8_t v___x_377_; 
v___x_377_ = 1;
return v___x_377_;
}
else
{
uint8_t v___x_378_; 
v___x_378_ = 0;
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object* v_x_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Lean_Name_isNum(v_x_379_);
lean_dec(v_x_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_anyS(lean_object* v_n_382_, lean_object* v_f_383_){
_start:
{
switch(lean_obj_tag(v_n_382_))
{
case 1:
{
lean_object* v_pre_384_; lean_object* v_str_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_pre_384_ = lean_ctor_get(v_n_382_, 0);
lean_inc(v_pre_384_);
v_str_385_ = lean_ctor_get(v_n_382_, 1);
lean_inc_ref(v_str_385_);
lean_dec_ref(v_n_382_);
lean_inc_ref(v_f_383_);
v___x_386_ = lean_apply_1(v_f_383_, v_str_385_);
v___x_387_ = lean_unbox(v___x_386_);
if (v___x_387_ == 0)
{
v_n_382_ = v_pre_384_;
goto _start;
}
else
{
uint8_t v___x_389_; 
lean_dec(v_pre_384_);
lean_dec_ref(v_f_383_);
v___x_389_ = lean_unbox(v___x_386_);
return v___x_389_;
}
}
case 2:
{
lean_object* v_pre_390_; 
v_pre_390_ = lean_ctor_get(v_n_382_, 0);
lean_inc(v_pre_390_);
lean_dec_ref(v_n_382_);
v_n_382_ = v_pre_390_;
goto _start;
}
default: 
{
uint8_t v___x_392_; 
lean_dec_ref(v_f_383_);
lean_dec(v_n_382_);
v___x_392_ = 0;
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object* v_n_393_, lean_object* v_f_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lean_Name_anyS(v_n_393_, v_f_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming___lam__0(lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_401_) == 1)
{
lean_object* v_pre_402_; 
v_pre_402_ = lean_ctor_get(v_x_401_, 0);
if (lean_obj_tag(v_pre_402_) == 0)
{
lean_object* v_str_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_str_403_ = lean_ctor_get(v_x_401_, 1);
v___x_404_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___lam__0___closed__0));
v___x_405_ = lean_string_dec_eq(v_str_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___lam__0___closed__1));
v___x_407_ = lean_string_dec_eq(v_str_403_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___lam__0___closed__2));
v___x_409_ = lean_string_dec_eq(v_str_403_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___lam__0___closed__3));
v___x_411_ = lean_string_dec_eq(v_str_403_, v___x_410_);
return v___x_411_;
}
else
{
return v___x_409_;
}
}
else
{
return v___x_407_;
}
}
else
{
return v___x_405_;
}
}
else
{
uint8_t v___x_412_; 
v___x_412_ = 0;
return v___x_412_;
}
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___lam__0___boxed(lean_object* v_x_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Lean_Name_isMetaprogramming___lam__0(v_x_414_);
lean_dec(v_x_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object* v_n_421_){
_start:
{
lean_object* v___f_422_; lean_object* v_components_423_; lean_object* v___x_424_; 
v___f_422_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__0));
v_components_423_ = l_Lean_Name_components(v_n_421_);
v___x_424_ = l_List_head_x3f___redArg(v_components_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
uint8_t v___x_425_; 
v___x_425_ = l_List_any___redArg(v_components_423_, v___f_422_);
return v___x_425_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_val_426_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_426_);
lean_dec_ref(v___x_424_);
v___x_427_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__2));
v___x_428_ = lean_name_eq(v_val_426_, v___x_427_);
lean_dec(v_val_426_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = l_List_any___redArg(v_components_423_, v___f_422_);
return v___x_429_;
}
else
{
lean_dec(v_components_423_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object* v_n_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Lean_Name_isMetaprogramming(v_n_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
