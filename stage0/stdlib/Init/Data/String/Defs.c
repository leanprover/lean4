// Lean compiler output
// Module: Init.Data.String.Defs
// Imports: public import Init.Data.String.PosRaw import Init.Data.ByteArray.Lemmas import Init.Omega
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedUInt8;
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___boxed(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instAppendString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_append___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAppendString___closed__0 = (const lean_object*)&l_instAppendString___closed__0_value;
LEAN_EXPORT const lean_object* l_instAppendString = (const lean_object*)&l_instAppendString___closed__0_value;
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object*);
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_string_isempty(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object*);
static const lean_string_object l_String_join___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_join___closed__0 = (const lean_object*)&l_String_join___closed__0_value;
LEAN_EXPORT lean_object* l_String_join(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startPos(lean_object*);
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_endPos(lean_object*);
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_instInhabitedSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_join___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_instInhabitedSlice___closed__0 = (const lean_object*)&l_String_instInhabitedSlice___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instInhabitedSlice = (const lean_object*)&l_String_instInhabitedSlice___closed__0_value;
LEAN_EXPORT lean_object* l_String_toSlice(lean_object*);
static const lean_closure_object l_String_instCoeSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_toSlice, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instCoeSlice___closed__0 = (const lean_object*)&l_String_instCoeSlice___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instCoeSlice = (const lean_object*)&l_String_instCoeSlice___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddRawSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddRawSlice___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddRawSlice___closed__0 = (const lean_object*)&l_String_instHAddRawSlice___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddRawSlice = (const lean_object*)&l_String_instHAddRawSlice___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddSliceRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddSliceRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddSliceRaw___closed__0 = (const lean_object*)&l_String_instHAddSliceRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddSliceRaw = (const lean_object*)&l_String_instHAddSliceRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHSubRawSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHSubRawSlice___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHSubRawSlice___closed__0 = (const lean_object*)&l_String_instHSubRawSlice___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHSubRawSlice = (const lean_object*)&l_String_instHSubRawSlice___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_String_Slice_getUTF8Byte_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Init.Data.String.Defs"};
static const lean_object* l_String_Slice_getUTF8Byte_x21___closed__0 = (const lean_object*)&l_String_Slice_getUTF8Byte_x21___closed__0_value;
static const lean_string_object l_String_Slice_getUTF8Byte_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "String.Slice.getUTF8Byte!"};
static const lean_object* l_String_Slice_getUTF8Byte_x21___closed__1 = (const lean_object*)&l_String_Slice_getUTF8Byte_x21___closed__1_value;
static const lean_string_object l_String_Slice_getUTF8Byte_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "String slice access is out of bounds."};
static const lean_object* l_String_Slice_getUTF8Byte_x21___closed__2 = (const lean_object*)&l_String_Slice_getUTF8Byte_x21___closed__2_value;
static lean_once_cell_t l_String_Slice_getUTF8Byte_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__3;
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object*);
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object*);
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object*);
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_String_bytes(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
lean_inc_ref(v_a_1_);
v___x_2_ = lean_string_from_utf8_unchecked(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg___boxed(lean_object* v_a_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_String_fromUTF8___redArg(v_a_3_);
lean_dec_ref(v_a_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object* v_a_5_, lean_object* v_h_6_){
_start:
{
lean_object* v___x_7_; 
lean_inc_ref(v_a_5_);
v___x_7_ = lean_string_from_utf8_unchecked(v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8___boxed(lean_object* v_a_8_, lean_object* v_h_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_String_fromUTF8(v_a_8_, v_h_9_);
lean_dec_ref(v_a_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lean_string_to_utf8(v_a_12_);
lean_dec_ref(v_a_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object* v_s_16_, lean_object* v_t_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lean_string_append(v_s_16_, v_t_17_);
lean_dec_ref(v_t_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(0u);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_String_rawStartPos(v___s_23_);
lean_dec_ref(v___s_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t v_c_25_, lean_object* v_s_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_string_push(v_s_26_, v_c_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_28_, lean_object* v_s_29_){
_start:
{
uint32_t v_c_boxed_30_; lean_object* v_res_31_; 
v_c_boxed_30_ = lean_unbox_uint32(v_c_28_);
lean_dec(v_c_28_);
v_res_31_ = l_String_pushn___lam__0(v_c_boxed_30_, v_s_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* v_s_32_, uint32_t v_c_33_, lean_object* v_n_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___x_37_; 
v___x_35_ = lean_box_uint32(v_c_33_);
v___f_36_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_36_, 0, v___x_35_);
v___x_37_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_36_, v_n_34_, v_s_32_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_38_, lean_object* v_c_39_, lean_object* v_n_40_){
_start:
{
uint32_t v_c_boxed_41_; lean_object* v_res_42_; 
v_c_boxed_41_ = lean_unbox_uint32(v_c_39_);
lean_dec(v_c_39_);
v_res_42_ = l_String_pushn(v_s_38_, v_c_boxed_41_, v_n_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_43_, lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
lean_object* v_zero_46_; uint8_t v_isZero_47_; 
v_zero_46_ = lean_unsigned_to_nat(0u);
v_isZero_47_ = lean_nat_dec_eq(v_x_44_, v_zero_46_);
if (v_isZero_47_ == 1)
{
lean_dec(v_x_44_);
return v_x_45_;
}
else
{
lean_object* v_one_48_; lean_object* v_n_49_; lean_object* v___x_50_; 
v_one_48_ = lean_unsigned_to_nat(1u);
v_n_49_ = lean_nat_sub(v_x_44_, v_one_48_);
lean_dec(v_x_44_);
v___x_50_ = lean_string_push(v_x_45_, v_c_43_);
v_x_44_ = v_n_49_;
v_x_45_ = v___x_50_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
uint32_t v_c_boxed_55_; lean_object* v_res_56_; 
v_c_boxed_55_ = lean_unbox_uint32(v_c_52_);
lean_dec(v_c_52_);
v_res_56_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_55_, v_x_53_, v_x_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* v_s_57_, uint32_t v_c_58_, lean_object* v_n_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_58_, v_n_59_, v_s_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_61_, lean_object* v_c_62_, lean_object* v_n_63_){
_start:
{
uint32_t v_c_boxed_64_; lean_object* v_res_65_; 
v_c_boxed_64_ = lean_unbox_uint32(v_c_62_);
lean_dec(v_c_62_);
v_res_65_ = lean_string_pushn(v_s_61_, v_c_boxed_64_, v_n_63_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* v_s_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_string_utf8_byte_size(v_s_66_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_dec_eq(v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_String_isEmpty(v_s_70_);
lean_dec_ref(v_s_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* v_s_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_string_utf8_byte_size(v_s_73_);
lean_dec_ref(v_s_73_);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_nat_dec_eq(v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = lean_string_isempty(v_s_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_81_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___f_82_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_83_ = ((lean_object*)(l_String_join___closed__0));
v___x_84_ = l_List_foldl___redArg(v___f_82_, v___x_83_, v_l_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_85_, lean_object* v_s_86_, lean_object* v_a_87_){
_start:
{
if (lean_obj_tag(v_a_87_) == 0)
{
return v_acc_85_;
}
else
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_head_88_ = lean_ctor_get(v_a_87_, 0);
v_tail_89_ = lean_ctor_get(v_a_87_, 1);
v___x_90_ = lean_string_append(v_acc_85_, v_s_86_);
v___x_91_ = lean_string_append(v___x_90_, v_head_88_);
v_acc_85_ = v___x_91_;
v_a_87_ = v_tail_89_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_93_, lean_object* v_s_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_93_, v_s_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_s_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l_String_join___closed__0));
return v___x_99_;
}
else
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_102_; 
v_head_100_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_head_100_);
v_tail_101_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_tail_101_);
lean_dec_ref(v_x_98_);
v___x_102_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_100_, v_s_97_, v_tail_101_);
lean_dec(v_tail_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_103_, lean_object* v_x_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_String_intercalate(v_s_103_, v_x_104_);
lean_dec_ref(v_s_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_String_intercalate(v_s_106_, v_a_107_);
lean_dec_ref(v_s_106_);
return v___x_108_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lean_nat_dec_eq(v_x_109_, v_x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_String_instDecidableEqPos_decEq___redArg(v_x_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec(v_x_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_eq(v_x_117_, v_x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_String_instDecidableEqPos_decEq(v_s_120_, v_x_121_, v_x_122_);
lean_dec(v_x_122_);
lean_dec(v_x_121_);
lean_dec_ref(v_s_120_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_eq(v_x_125_, v_x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_String_instDecidableEqPos___redArg(v_x_128_, v_x_129_);
lean_dec(v_x_129_);
lean_dec(v_x_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* v_s_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_eq(v_x_133_, v_x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_String_instDecidableEqPos(v_s_136_, v_x_137_, v_x_138_);
lean_dec(v_x_138_);
lean_dec(v_x_137_);
lean_dec_ref(v_s_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* v_s_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(0u);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* v_s_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_String_startPos(v_s_143_);
lean_dec_ref(v_s_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(0u);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_String_instInhabitedPos(v_s_147_);
lean_dec_ref(v_s_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_string_utf8_byte_size(v_s_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_String_endPos(v_s_151_);
lean_dec_ref(v_s_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* v_s_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* v_s_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_String_instLEPos(v_s_155_);
lean_dec_ref(v_s_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(0);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_String_instLTPos(v_s_159_);
lean_dec_ref(v_s_159_);
return v_res_160_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_161_, lean_object* v_r_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = lean_nat_dec_le(v_l_161_, v_r_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_164_, lean_object* v_r_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_String_instDecidableLePos___redArg(v_l_164_, v_r_165_);
lean_dec(v_r_165_);
lean_dec(v_l_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* v_s_168_, lean_object* v_l_169_, lean_object* v_r_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_le(v_l_169_, v_r_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_172_, lean_object* v_l_173_, lean_object* v_r_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_String_instDecidableLePos(v_s_172_, v_l_173_, v_r_174_);
lean_dec(v_r_174_);
lean_dec(v_l_173_);
lean_dec_ref(v_s_172_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_177_, lean_object* v_r_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_String_instDecidableLtRaw___aux__1(v_l_177_, v_r_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_180_, lean_object* v_r_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_String_instDecidableLtPos___redArg(v_l_180_, v_r_181_);
lean_dec(v_r_181_);
lean_dec(v_l_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* v_s_184_, lean_object* v_l_185_, lean_object* v_r_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_String_instDecidableLtRaw___aux__1(v_l_185_, v_r_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_188_, lean_object* v_l_189_, lean_object* v_r_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_String_instDecidableLtPos(v_s_188_, v_l_189_, v_r_190_);
lean_dec(v_r_190_);
lean_dec(v_l_189_);
lean_dec_ref(v_s_188_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_string_utf8_byte_size(v_s_197_);
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v_s_197_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
lean_ctor_set(v___x_200_, 2, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_203_){
_start:
{
lean_object* v_startInclusive_204_; lean_object* v_endExclusive_205_; lean_object* v___x_206_; 
v_startInclusive_204_ = lean_ctor_get(v_s_203_, 1);
v_endExclusive_205_ = lean_ctor_get(v_s_203_, 2);
v___x_206_ = lean_nat_sub(v_endExclusive_205_, v_startInclusive_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_String_Slice_utf8ByteSize(v_s_207_);
lean_dec_ref(v_s_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_209_, lean_object* v_s_210_){
_start:
{
lean_object* v_startInclusive_211_; lean_object* v_endExclusive_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_startInclusive_211_ = lean_ctor_get(v_s_210_, 1);
v_endExclusive_212_ = lean_ctor_get(v_s_210_, 2);
v___x_213_ = lean_nat_sub(v_endExclusive_212_, v_startInclusive_211_);
v___x_214_ = lean_nat_add(v_p_209_, v___x_213_);
lean_dec(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_215_, lean_object* v_s_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_instHAddRawSlice___lam__0(v_p_215_, v_s_216_);
lean_dec_ref(v_s_216_);
lean_dec(v_p_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_220_, lean_object* v_p_221_){
_start:
{
lean_object* v_startInclusive_222_; lean_object* v_endExclusive_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_startInclusive_222_ = lean_ctor_get(v_s_220_, 1);
v_endExclusive_223_ = lean_ctor_get(v_s_220_, 2);
v___x_224_ = lean_nat_sub(v_endExclusive_223_, v_startInclusive_222_);
v___x_225_ = lean_nat_add(v___x_224_, v_p_221_);
lean_dec(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_226_, lean_object* v_p_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_String_instHAddSliceRaw___lam__0(v_s_226_, v_p_227_);
lean_dec(v_p_227_);
lean_dec_ref(v_s_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_231_, lean_object* v_s_232_){
_start:
{
lean_object* v_startInclusive_233_; lean_object* v_endExclusive_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_startInclusive_233_ = lean_ctor_get(v_s_232_, 1);
v_endExclusive_234_ = lean_ctor_get(v_s_232_, 2);
v___x_235_ = lean_nat_sub(v_endExclusive_234_, v_startInclusive_233_);
v___x_236_ = lean_nat_sub(v_p_231_, v___x_235_);
lean_dec(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_237_, lean_object* v_s_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_String_instHSubRawSlice___lam__0(v_p_237_, v_s_238_);
lean_dec_ref(v_s_238_);
lean_dec(v_p_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_242_){
_start:
{
lean_object* v_startInclusive_243_; lean_object* v_endExclusive_244_; lean_object* v___x_245_; 
v_startInclusive_243_ = lean_ctor_get(v_s_242_, 1);
v_endExclusive_244_ = lean_ctor_get(v_s_242_, 2);
v___x_245_ = lean_nat_sub(v_endExclusive_244_, v_startInclusive_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_String_Slice_rawEndPos(v_s_246_);
lean_dec_ref(v_s_246_);
return v_res_247_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_248_, lean_object* v_p_249_){
_start:
{
lean_object* v_str_250_; lean_object* v_startInclusive_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_str_250_ = lean_ctor_get(v_s_248_, 0);
v_startInclusive_251_ = lean_ctor_get(v_s_248_, 1);
v___x_252_ = lean_nat_add(v_startInclusive_251_, v_p_249_);
v___x_253_ = lean_string_get_byte_fast(v_str_250_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* v_s_254_, lean_object* v_p_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_String_Slice_getUTF8Byte___redArg(v_s_254_, v_p_255_);
lean_dec(v_p_255_);
lean_dec_ref(v_s_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_258_, lean_object* v_p_259_, lean_object* v_h_260_){
_start:
{
lean_object* v_str_261_; lean_object* v_startInclusive_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_str_261_ = lean_ctor_get(v_s_258_, 0);
v_startInclusive_262_ = lean_ctor_get(v_s_258_, 1);
v___x_263_ = lean_nat_add(v_startInclusive_262_, v_p_259_);
v___x_264_ = lean_string_get_byte_fast(v_str_261_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_265_, lean_object* v_p_266_, lean_object* v_h_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_String_Slice_getUTF8Byte(v_s_265_, v_p_266_, v_h_267_);
lean_dec(v_p_266_);
lean_dec_ref(v_s_265_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_270_){
_start:
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_271_ = l_instInhabitedUInt8;
v___x_272_ = lean_box(v___x_271_);
v___x_273_ = lean_panic_fn(v___x_272_, v_msg_270_);
v___x_274_ = lean_unbox(v___x_273_);
lean_dec(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_281_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_282_ = lean_unsigned_to_nat(4u);
v___x_283_ = lean_unsigned_to_nat(509u);
v___x_284_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_285_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_286_ = l_mkPanicMessageWithDecl(v___x_285_, v___x_284_, v___x_283_, v___x_282_, v___x_281_);
return v___x_286_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_287_, lean_object* v_p_288_){
_start:
{
lean_object* v_str_289_; lean_object* v_startInclusive_290_; lean_object* v_endExclusive_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_str_289_ = lean_ctor_get(v_s_287_, 0);
v_startInclusive_290_ = lean_ctor_get(v_s_287_, 1);
v_endExclusive_291_ = lean_ctor_get(v_s_287_, 2);
v___x_292_ = lean_nat_sub(v_endExclusive_291_, v_startInclusive_290_);
v___x_293_ = l_String_instDecidableLtRaw___aux__1(v_p_288_, v___x_292_);
lean_dec(v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_295_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_294_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_nat_add(v_startInclusive_290_, v_p_288_);
v___x_297_ = lean_string_get_byte_fast(v_str_289_, v___x_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_298_, lean_object* v_p_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_String_Slice_getUTF8Byte_x21(v_s_298_, v_p_299_);
lean_dec(v_p_299_);
lean_dec_ref(v_s_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_nat_dec_eq(v_x_302_, v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec(v_x_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_nat_dec_eq(v_x_310_, v_x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_String_Slice_instDecidableEqPos_decEq(v_s_313_, v_x_314_, v_x_315_);
lean_dec(v_x_315_);
lean_dec(v_x_314_);
lean_dec_ref(v_s_313_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_eq(v_x_318_, v_x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_String_Slice_instDecidableEqPos___redArg(v_x_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec(v_x_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_nat_dec_eq(v_x_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_String_Slice_instDecidableEqPos(v_s_329_, v_x_330_, v_x_331_);
lean_dec(v_x_331_);
lean_dec(v_x_330_);
lean_dec_ref(v_s_329_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(0u);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_String_Slice_startPos(v_s_336_);
lean_dec_ref(v_s_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_unsigned_to_nat(0u);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_String_instInhabitedPos__1(v_s_340_);
lean_dec_ref(v_s_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_342_){
_start:
{
lean_object* v_startInclusive_343_; lean_object* v_endExclusive_344_; lean_object* v___x_345_; 
v_startInclusive_343_ = lean_ctor_get(v_s_342_, 1);
v_endExclusive_344_ = lean_ctor_get(v_s_342_, 2);
v___x_345_ = lean_nat_sub(v_endExclusive_344_, v_startInclusive_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_String_Slice_endPos(v_s_346_);
lean_dec_ref(v_s_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_box(0);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_String_instLEPos__1(v_s_350_);
lean_dec_ref(v_s_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_box(0);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_String_instLTPos__1(v_s_354_);
lean_dec_ref(v_s_354_);
return v_res_355_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_356_, lean_object* v_r_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_le(v_l_356_, v_r_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_359_, lean_object* v_r_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_String_instDecidableLePos__1___redArg(v_l_359_, v_r_360_);
lean_dec(v_r_360_);
lean_dec(v_l_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_363_, lean_object* v_l_364_, lean_object* v_r_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_le(v_l_364_, v_r_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_367_, lean_object* v_l_368_, lean_object* v_r_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_String_instDecidableLePos__1(v_s_367_, v_l_368_, v_r_369_);
lean_dec(v_r_369_);
lean_dec(v_l_368_);
lean_dec_ref(v_s_367_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_372_, lean_object* v_r_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = l_String_instDecidableLtRaw___aux__1(v_l_372_, v_r_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_375_, lean_object* v_r_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_String_instDecidableLtPos__1___redArg(v_l_375_, v_r_376_);
lean_dec(v_r_376_);
lean_dec(v_l_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_379_, lean_object* v_l_380_, lean_object* v_r_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = l_String_instDecidableLtRaw___aux__1(v_l_380_, v_r_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_383_, lean_object* v_l_384_, lean_object* v_r_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_String_instDecidableLtPos__1(v_s_383_, v_l_384_, v_r_385_);
lean_dec(v_r_385_);
lean_dec(v_l_384_);
lean_dec_ref(v_s_383_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_388_, lean_object* v_pos_389_){
_start:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_string_utf8_byte_size(v_s_388_);
v___x_391_ = lean_nat_dec_eq(v_pos_389_, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_392_, lean_object* v_pos_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_String_instDecidableIsAtEnd(v_s_392_, v_pos_393_);
lean_dec(v_pos_393_);
lean_dec_ref(v_s_392_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_396_, lean_object* v_pos_397_){
_start:
{
lean_object* v_startInclusive_398_; lean_object* v_endExclusive_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_startInclusive_398_ = lean_ctor_get(v_s_396_, 1);
v_endExclusive_399_ = lean_ctor_get(v_s_396_, 2);
v___x_400_ = lean_nat_sub(v_endExclusive_399_, v_startInclusive_398_);
v___x_401_ = lean_nat_dec_eq(v_pos_397_, v___x_400_);
lean_dec(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_402_, lean_object* v_pos_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_String_instDecidableIsAtEnd__1(v_s_402_, v_pos_403_);
lean_dec(v_pos_403_);
lean_dec_ref(v_s_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_406_, lean_object* v_pos_407_){
_start:
{
lean_object* v_str_408_; lean_object* v_startInclusive_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_str_408_ = lean_ctor_get(v_s_406_, 0);
v_startInclusive_409_ = lean_ctor_get(v_s_406_, 1);
v___x_410_ = lean_nat_add(v_startInclusive_409_, v_pos_407_);
v___x_411_ = lean_string_get_byte_fast(v_str_408_, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_412_, lean_object* v_pos_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_String_Slice_Pos_byte___redArg(v_s_412_, v_pos_413_);
lean_dec(v_pos_413_);
lean_dec_ref(v_s_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_416_, lean_object* v_pos_417_, lean_object* v_h_418_){
_start:
{
lean_object* v_str_419_; lean_object* v_startInclusive_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_str_419_ = lean_ctor_get(v_s_416_, 0);
v_startInclusive_420_ = lean_ctor_get(v_s_416_, 1);
v___x_421_ = lean_nat_add(v_startInclusive_420_, v_pos_417_);
v___x_422_ = lean_string_get_byte_fast(v_str_419_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_423_, lean_object* v_pos_424_, lean_object* v_h_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_String_Slice_Pos_byte(v_s_423_, v_pos_424_, v_h_425_);
lean_dec(v_pos_424_);
lean_dec_ref(v_s_423_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_428_){
_start:
{
lean_object* v_startInclusive_429_; lean_object* v_endExclusive_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_startInclusive_429_ = lean_ctor_get(v_s_428_, 1);
v_endExclusive_430_ = lean_ctor_get(v_s_428_, 2);
v___x_431_ = lean_nat_sub(v_endExclusive_430_, v_startInclusive_429_);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_nat_dec_eq(v___x_431_, v___x_432_);
lean_dec(v___x_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_String_Slice_isEmpty(v_s_434_);
lean_dec_ref(v_s_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_string_utf8_byte_size(v_s_437_);
v___x_440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_440_, 0, v_s_437_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_String_toRawSubstring_x27(v_s_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_unsigned_to_nat(0u);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_String_startValidPos(v_s_445_);
lean_dec_ref(v_s_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_string_utf8_byte_size(v_s_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_String_endValidPos(v_s_449_);
lean_dec_ref(v_s_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_String_String_bytes(lean_object* v_s_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_string_to_utf8(v_s_451_);
return v___x_452_;
}
}
lean_object* runtime_initialize_Init_Data_String_PosRaw(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Defs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_PosRaw(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Defs(builtin);
}
#ifdef __cplusplus
}
#endif
