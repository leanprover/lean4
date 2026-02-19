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
uint64_t lean_uint64_of_nat(lean_object*);
static uint64_t l_Lean_Name_hashEx___closed__0;
LEAN_EXPORT uint64_t lean_name_hash_exported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object*);
static const lean_string_object l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Name_getString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Data.Name"};
static const lean_object* l_Lean_Name_getString_x21___closed__0 = (const lean_object*)&l_Lean_Name_getString_x21___closed__0_value;
static const lean_string_object l_Lean_Name_getString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Name.getString!"};
static const lean_object* l_Lean_Name_getString_x21___closed__1 = (const lean_object*)&l_Lean_Name_getString_x21___closed__1_value;
static const lean_string_object l_Lean_Name_getString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Name_getString_x21___closed__2 = (const lean_object*)&l_Lean_Name_getString_x21___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Name_getString_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_eqStr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eqStr___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_cmp(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_cmp___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Name_isInternalDetail___closed__5;
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isImplementationDetail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "__"};
static const lean_object* l_Lean_Name_isImplementationDetail___closed__0 = (const lean_object*)&l_Lean_Name_isImplementationDetail___closed__0_value;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Name_isMetaprogramming_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Name_isMetaprogramming___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__0 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Name_isMetaprogramming___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__1 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__1_value;
static const lean_string_object l_Lean_Name_isMetaprogramming___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__2 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Name_isMetaprogramming___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 50, 177, 192, 218, 101, 157, 15)}};
static const lean_object* l_Lean_Name_isMetaprogramming___lam__0___closed__3 = (const lean_object*)&l_Lean_Name_isMetaprogramming___lam__0___closed__3_value;
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isMetaprogramming___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__0 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__0_value;
static const lean_ctor_object l_Lean_Name_isMetaprogramming___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Name_isMetaprogramming___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__1 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__1_value;
static const lean_ctor_object l_Lean_Name_isMetaprogramming___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Name_isMetaprogramming___closed__1_value)}};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__2 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__2_value;
static const lean_closure_object l_Lean_Name_isMetaprogramming___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_isMetaprogramming___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_isMetaprogramming___closed__3 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__3_value;
lean_object* l_List_head_x3f___redArg(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object*);
static uint64_t _init_l_Lean_Name_hashEx___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t lean_name_hash_exported(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint64_t x_2; 
x_2 = l_Lean_Name_hashEx___closed__0;
return x_2;
}
else
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_name_hash_exported(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Name_getPrefix(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Name_getString_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Name_getString_x21___closed__2));
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(30u);
x_4 = ((lean_object*)(l_Lean_Name_getString_x21___closed__1));
x_5 = ((lean_object*)(l_Lean_Name_getString_x21___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Name_getString_x21___closed__3;
x_4 = l_panic___at___00Lean_Name_getString_x21_spec__0(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_getNumParts(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Name_getNumParts(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_2);
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Name_str___override(x_2, x_3);
return x_4;
}
default: 
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_Name_num___override(x_2, x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(0);
x_6 = l_Lean_Name_str___override(x_5, x_4);
x_7 = l_Lean_Name_componentsRev(x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_Name_num___override(x_11, x_10);
x_13 = l_Lean_Name_componentsRev(x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Name_componentsRev(x_1);
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_eqStr(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_dec_eq(x_4, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eqStr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_eqStr(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isPrefixOf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_1, x_2);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_isPrefixOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isSuffixOf(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_string_dec_eq(x_5, x_7);
if (x_8 == 0)
{
return x_8;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_nat_dec_eq(x_12, x_14);
if (x_15 == 0)
{
return x_15;
}
else
{
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_isSuffixOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_cmp(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Name_cmp(x_5, x_7);
if (x_9 == 1)
{
uint8_t x_10; 
x_10 = lean_string_dec_lt(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_6, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 2;
return x_12;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
else
{
return x_9;
}
}
else
{
uint8_t x_14; 
x_14 = 2;
return x_14;
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_15; 
x_15 = 2;
return x_15;
}
case 1:
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = l_Lean_Name_cmp(x_17, x_19);
if (x_21 == 1)
{
uint8_t x_22; 
x_22 = lean_nat_dec_lt(x_18, x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_18, x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 2;
return x_24;
}
else
{
return x_21;
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
else
{
return x_21;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_cmp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_cmp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_cmp(x_1, x_2);
x_4 = 0;
x_5 = l_instDecidableEqOrdering(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_string_dec_lt(x_6, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_string_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 2;
return x_11;
}
else
{
x_1 = x_5;
x_2 = x_7;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 2;
return x_14;
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_15; 
x_15 = 2;
return x_15;
}
case 1:
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_nat_dec_lt(x_18, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_18, x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 2;
return x_23;
}
else
{
x_1 = x_17;
x_2 = x_19;
goto _start;
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_quickCmpAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_11; uint8_t x_15; 
x_15 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(x_1, x_2);
if (x_15 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
uint64_t x_16; 
x_16 = l_Lean_Name_hashEx___closed__0;
x_11 = x_16;
goto block_14;
}
else
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = x_17;
goto block_14;
}
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
block_10:
{
uint8_t x_5; 
x_5 = lean_uint64_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_uint64_dec_eq(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_Name_quickCmpAux(x_1, x_2);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
block_14:
{
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_12; 
x_12 = l_Lean_Name_hashEx___closed__0;
x_3 = x_11;
x_4 = x_12;
goto block_10;
}
else
{
uint64_t x_13; 
x_13 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_3 = x_11;
x_4 = x_13;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_2);
x_4 = 0;
x_5 = l_instDecidableEqOrdering(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_quickLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
x_1 = x_3;
goto _start;
}
default: 
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_hasNum(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_byte_size(x_3);
lean_inc_ref(x_3);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_String_Slice_Pos_get_x3f(x_11, x_9);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint32_t x_13; 
x_13 = 65;
x_4 = x_13;
goto block_8;
}
else
{
lean_object* x_14; uint32_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unbox_uint32(x_14);
lean_dec(x_14);
x_4 = x_15;
goto block_8;
}
block_8:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 95;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
return x_6;
}
}
}
case 2:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
x_1 = x_16;
goto _start;
}
default: 
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isInternal(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_byte_size(x_3);
lean_inc_ref(x_3);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_String_Slice_Pos_get_x3f(x_11, x_9);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint32_t x_13; 
x_13 = 65;
x_4 = x_13;
goto block_8;
}
else
{
lean_object* x_14; uint32_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unbox_uint32(x_14);
lean_dec(x_14);
x_4 = x_15;
goto block_8;
}
block_8:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 95;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
return x_6;
}
}
}
case 2:
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
default: 
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isInternalOrNum(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
lean_inc(x_5);
lean_inc(x_6);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_sub(x_5, x_6);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; uint32_t x_22; uint8_t x_23; 
x_17 = lean_string_utf8_get_fast(x_3, x_6);
x_22 = 48;
x_23 = lean_uint32_dec_le(x_22, x_17);
if (x_23 == 0)
{
x_18 = x_23;
goto block_21;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 57;
x_25 = lean_uint32_dec_le(x_17, x_24);
x_18 = x_25;
goto block_21;
}
block_21:
{
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 95;
x_20 = lean_uint32_dec_eq(x_17, x_19);
if (x_20 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
goto block_13;
}
}
else
{
goto block_13;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_next_fast(x_3, x_6);
x_9 = lean_nat_sub(x_8, x_6);
lean_dec(x_6);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_2);
if (x_11 == 0)
{
lean_dec(x_10);
return x_7;
}
else
{
lean_dec_ref(x_7);
x_2 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_string_memcmp(x_1, x_2, x_6, x_6, x_4);
if (x_7 == 0)
{
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_string_length(x_2);
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_3);
x_10 = l_String_Slice_Pos_nextn(x_9, x_6, x_8);
lean_dec_ref(x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_3);
x_12 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(x_11, x_6);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_nat_sub(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
x_16 = lean_nat_dec_eq(x_15, x_6);
lean_dec(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Name_isInternalDetail___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_14 = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
x_15 = lean_string_utf8_byte_size(x_3);
x_16 = l_Lean_Name_isInternalDetail___closed__5;
x_17 = lean_nat_dec_le(x_16, x_15);
if (x_17 == 0)
{
goto block_13;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_string_memcmp(x_3, x_14, x_18, x_18, x_16);
if (x_19 == 0)
{
goto block_13;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_2);
return x_19;
}
}
block_13:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__0));
lean_inc_ref(x_3);
x_5 = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__1));
lean_inc_ref(x_3);
x_7 = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__2));
lean_inc_ref(x_3);
x_9 = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__3));
x_11 = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(x_3, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Name_isInternalOrNum(x_2);
lean_dec(x_2);
return x_12;
}
else
{
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
}
case 2:
{
uint8_t x_20; 
lean_dec_ref(x_1);
x_20 = 1;
return x_20;
}
default: 
{
uint8_t x_21; 
x_21 = l_Lean_Name_isInternalOrNum(x_1);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isInternalDetail(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Name_isImplementationDetail___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isImplementationDetail(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = l_Lean_Name_isImplementationDetail___closed__1;
x_8 = lean_nat_dec_le(x_7, x_6);
if (x_8 == 0)
{
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_memcmp(x_4, x_5, x_9, x_9, x_7);
return x_10;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
default: 
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 0);
x_1 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isImplementationDetail(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAtomic(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isAtomic(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAnonymous(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isAnonymous(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isStr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isStr(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isNum(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isNum(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_anyS(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_unbox(x_5);
return x_8;
}
}
case 2:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_1 = x_9;
goto _start;
}
default: 
{
uint8_t x_11; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_anyS(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Name_isMetaprogramming_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_name_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Name_isMetaprogramming_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Name_isMetaprogramming___lam__0___closed__1));
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Name_isMetaprogramming___lam__0___closed__3));
x_5 = lean_name_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isMetaprogramming___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Name_components(x_1);
x_3 = l_List_head_x3f___redArg(x_2);
x_4 = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__2));
x_5 = l_Option_instBEq_beq___at___00Lean_Name_isMetaprogramming_spec__0(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__3));
x_7 = l_List_any___redArg(x_2, x_6);
return x_7;
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_isMetaprogramming(x_1);
x_3 = lean_box(x_2);
return x_3;
}
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
l_Lean_Name_hashEx___closed__0 = _init_l_Lean_Name_hashEx___closed__0();
l_Lean_Name_getString_x21___closed__3 = _init_l_Lean_Name_getString_x21___closed__3();
lean_mark_persistent(l_Lean_Name_getString_x21___closed__3);
l_Lean_Name_isInternalDetail___closed__5 = _init_l_Lean_Name_isInternalDetail___closed__5();
lean_mark_persistent(l_Lean_Name_isInternalDetail___closed__5);
l_Lean_Name_isImplementationDetail___closed__1 = _init_l_Lean_Name_isImplementationDetail___closed__1();
lean_mark_persistent(l_Lean_Name_isImplementationDetail___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
