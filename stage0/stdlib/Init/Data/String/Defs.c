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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_bytes(lean_object*);
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii(lean_object*);
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(lean_object* v_x_21_, uint32_t v_x_22_, lean_object* v_h__1_23_){
_start:
{
lean_object* v_toByteArray_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_toByteArray_24_ = lean_string_to_utf8(v_x_21_);
v___x_25_ = lean_box_uint32(v_x_22_);
v___x_26_ = lean_apply_3(v_h__1_23_, v_toByteArray_24_, lean_box(0), v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg___boxed(lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_h__1_29_){
_start:
{
uint32_t v_x_18__boxed_30_; lean_object* v_res_31_; 
v_x_18__boxed_30_ = lean_unbox_uint32(v_x_28_);
lean_dec(v_x_28_);
v_res_31_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(v_x_27_, v_x_18__boxed_30_, v_h__1_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(lean_object* v_motive_32_, lean_object* v_x_33_, uint32_t v_x_34_, lean_object* v_h__1_35_){
_start:
{
lean_object* v_toByteArray_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_toByteArray_36_ = lean_string_to_utf8(v_x_33_);
v___x_37_ = lean_box_uint32(v_x_34_);
v___x_38_ = lean_apply_3(v_h__1_35_, v_toByteArray_36_, lean_box(0), v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___boxed(lean_object* v_motive_39_, lean_object* v_x_40_, lean_object* v_x_41_, lean_object* v_h__1_42_){
_start:
{
uint32_t v_x_30__boxed_43_; lean_object* v_res_44_; 
v_x_30__boxed_43_ = lean_unbox_uint32(v_x_41_);
lean_dec(v_x_41_);
v_res_44_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(v_motive_39_, v_x_40_, v_x_30__boxed_43_, v_h__1_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_unsigned_to_nat(0u);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_String_rawStartPos(v___s_47_);
lean_dec_ref(v___s_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t v_c_49_, lean_object* v_s_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_string_push(v_s_50_, v_c_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_52_, lean_object* v_s_53_){
_start:
{
uint32_t v_c_boxed_54_; lean_object* v_res_55_; 
v_c_boxed_54_ = lean_unbox_uint32(v_c_52_);
lean_dec(v_c_52_);
v_res_55_ = l_String_pushn___lam__0(v_c_boxed_54_, v_s_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* v_s_56_, uint32_t v_c_57_, lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___x_61_; 
v___x_59_ = lean_box_uint32(v_c_57_);
v___f_60_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_60_, 0, v___x_59_);
v___x_61_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_60_, v_n_58_, v_s_56_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_62_, lean_object* v_c_63_, lean_object* v_n_64_){
_start:
{
uint32_t v_c_boxed_65_; lean_object* v_res_66_; 
v_c_boxed_65_ = lean_unbox_uint32(v_c_63_);
lean_dec(v_c_63_);
v_res_66_ = l_String_pushn(v_s_62_, v_c_boxed_65_, v_n_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_67_, lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_zero_70_; uint8_t v_isZero_71_; 
v_zero_70_ = lean_unsigned_to_nat(0u);
v_isZero_71_ = lean_nat_dec_eq(v_x_68_, v_zero_70_);
if (v_isZero_71_ == 1)
{
lean_dec(v_x_68_);
return v_x_69_;
}
else
{
lean_object* v_one_72_; lean_object* v_n_73_; lean_object* v___x_74_; 
v_one_72_ = lean_unsigned_to_nat(1u);
v_n_73_ = lean_nat_sub(v_x_68_, v_one_72_);
lean_dec(v_x_68_);
v___x_74_ = lean_string_push(v_x_69_, v_c_67_);
v_x_68_ = v_n_73_;
v_x_69_ = v___x_74_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
uint32_t v_c_boxed_79_; lean_object* v_res_80_; 
v_c_boxed_79_ = lean_unbox_uint32(v_c_76_);
lean_dec(v_c_76_);
v_res_80_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_79_, v_x_77_, v_x_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* v_s_81_, uint32_t v_c_82_, lean_object* v_n_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_82_, v_n_83_, v_s_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_85_, lean_object* v_c_86_, lean_object* v_n_87_){
_start:
{
uint32_t v_c_boxed_88_; lean_object* v_res_89_; 
v_c_boxed_88_ = lean_unbox_uint32(v_c_86_);
lean_dec(v_c_86_);
v_res_89_ = lean_string_pushn(v_s_85_, v_c_boxed_88_, v_n_87_);
return v_res_89_;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* v_s_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_91_ = lean_string_utf8_byte_size(v_s_90_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_nat_dec_eq(v___x_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_String_isEmpty(v_s_94_);
lean_dec_ref(v_s_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* v_s_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = lean_string_utf8_byte_size(v_s_97_);
lean_dec_ref(v_s_97_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_nat_dec_eq(v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = lean_string_isempty(v_s_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___f_106_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_107_ = ((lean_object*)(l_String_join___closed__0));
v___x_108_ = l_List_foldl___redArg(v___f_106_, v___x_107_, v_l_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_109_, lean_object* v_s_110_, lean_object* v_a_111_){
_start:
{
if (lean_obj_tag(v_a_111_) == 0)
{
return v_acc_109_;
}
else
{
lean_object* v_head_112_; lean_object* v_tail_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_head_112_ = lean_ctor_get(v_a_111_, 0);
v_tail_113_ = lean_ctor_get(v_a_111_, 1);
v___x_114_ = lean_string_append(v_acc_109_, v_s_110_);
v___x_115_ = lean_string_append(v___x_114_, v_head_112_);
v_acc_109_ = v___x_115_;
v_a_111_ = v_tail_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_117_, lean_object* v_s_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_117_, v_s_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_s_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_String_join___closed__0));
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_126_; 
v_head_124_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_head_124_);
v_tail_125_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_tail_125_);
lean_dec_ref_known(v_x_122_, 2);
v___x_126_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_124_, v_s_121_, v_tail_125_);
lean_dec(v_tail_125_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_127_, lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_String_intercalate(v_s_127_, v_x_128_);
lean_dec_ref(v_s_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_String_intercalate(v_s_130_, v_a_131_);
lean_dec_ref(v_s_130_);
return v___x_132_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_decide_135_; 
v_decide_135_ = lean_nat_dec_eq(v_x_133_, v_x_134_);
return v_decide_135_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_String_instDecidableEqPos_decEq___redArg(v_x_136_, v_x_137_);
lean_dec(v_x_137_);
lean_dec(v_x_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
uint8_t v_decide_143_; 
v_decide_143_ = lean_nat_dec_eq(v_x_141_, v_x_142_);
return v_decide_143_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_String_instDecidableEqPos_decEq(v_s_144_, v_x_145_, v_x_146_);
lean_dec(v_x_146_);
lean_dec(v_x_145_);
lean_dec_ref(v_s_144_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_decide_151_; 
v_decide_151_ = lean_nat_dec_eq(v_x_149_, v_x_150_);
return v_decide_151_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_String_instDecidableEqPos___redArg(v_x_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec(v_x_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* v_s_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_decide_159_; 
v_decide_159_ = lean_nat_dec_eq(v_x_157_, v_x_158_);
return v_decide_159_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_String_instDecidableEqPos(v_s_160_, v_x_161_, v_x_162_);
lean_dec(v_x_162_);
lean_dec(v_x_161_);
lean_dec_ref(v_s_160_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* v_s_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_unsigned_to_nat(0u);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* v_s_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_String_startPos(v_s_167_);
lean_dec_ref(v_s_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_unsigned_to_nat(0u);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_String_instInhabitedPos(v_s_171_);
lean_dec_ref(v_s_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_string_utf8_byte_size(v_s_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_String_endPos(v_s_175_);
lean_dec_ref(v_s_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* v_s_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* v_s_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_String_instLEPos(v_s_179_);
lean_dec_ref(v_s_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(0);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_String_instLTPos(v_s_183_);
lean_dec_ref(v_s_183_);
return v_res_184_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_185_, lean_object* v_r_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_le(v_l_185_, v_r_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_188_, lean_object* v_r_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_String_instDecidableLePos___redArg(v_l_188_, v_r_189_);
lean_dec(v_r_189_);
lean_dec(v_l_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* v_s_192_, lean_object* v_l_193_, lean_object* v_r_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_le(v_l_193_, v_r_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_196_, lean_object* v_l_197_, lean_object* v_r_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_String_instDecidableLePos(v_s_196_, v_l_197_, v_r_198_);
lean_dec(v_r_198_);
lean_dec(v_l_197_);
lean_dec_ref(v_s_196_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_201_, lean_object* v_r_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_l_201_, v___x_203_);
v___x_205_ = lean_nat_dec_le(v___x_204_, v_r_202_);
lean_dec(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_206_, lean_object* v_r_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_String_instDecidableLtPos___redArg(v_l_206_, v_r_207_);
lean_dec(v_r_207_);
lean_dec(v_l_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* v_s_210_, lean_object* v_l_211_, lean_object* v_r_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = l_String_instDecidableLtPos___redArg(v_l_211_, v_r_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_214_, lean_object* v_l_215_, lean_object* v_r_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_String_instDecidableLtPos(v_s_214_, v_l_215_, v_r_216_);
lean_dec(v_r_216_);
lean_dec(v_l_215_);
lean_dec_ref(v_s_214_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_string_utf8_byte_size(v_s_223_);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v_s_223_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_229_){
_start:
{
lean_object* v_startInclusive_230_; lean_object* v_endExclusive_231_; lean_object* v___x_232_; 
v_startInclusive_230_ = lean_ctor_get(v_s_229_, 1);
v_endExclusive_231_ = lean_ctor_get(v_s_229_, 2);
v___x_232_ = lean_nat_sub(v_endExclusive_231_, v_startInclusive_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_String_Slice_utf8ByteSize(v_s_233_);
lean_dec_ref(v_s_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_235_, lean_object* v_s_236_){
_start:
{
lean_object* v_startInclusive_237_; lean_object* v_endExclusive_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_startInclusive_237_ = lean_ctor_get(v_s_236_, 1);
v_endExclusive_238_ = lean_ctor_get(v_s_236_, 2);
v___x_239_ = lean_nat_sub(v_endExclusive_238_, v_startInclusive_237_);
v___x_240_ = lean_nat_add(v_p_235_, v___x_239_);
lean_dec(v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_241_, lean_object* v_s_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_String_instHAddRawSlice___lam__0(v_p_241_, v_s_242_);
lean_dec_ref(v_s_242_);
lean_dec(v_p_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_246_, lean_object* v_p_247_){
_start:
{
lean_object* v_startInclusive_248_; lean_object* v_endExclusive_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_startInclusive_248_ = lean_ctor_get(v_s_246_, 1);
v_endExclusive_249_ = lean_ctor_get(v_s_246_, 2);
v___x_250_ = lean_nat_sub(v_endExclusive_249_, v_startInclusive_248_);
v___x_251_ = lean_nat_add(v___x_250_, v_p_247_);
lean_dec(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_252_, lean_object* v_p_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_String_instHAddSliceRaw___lam__0(v_s_252_, v_p_253_);
lean_dec(v_p_253_);
lean_dec_ref(v_s_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_startInclusive_259_; lean_object* v_endExclusive_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_startInclusive_259_ = lean_ctor_get(v_s_258_, 1);
v_endExclusive_260_ = lean_ctor_get(v_s_258_, 2);
v___x_261_ = lean_nat_sub(v_endExclusive_260_, v_startInclusive_259_);
v___x_262_ = lean_nat_sub(v_p_257_, v___x_261_);
lean_dec(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_263_, lean_object* v_s_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_String_instHSubRawSlice___lam__0(v_p_263_, v_s_264_);
lean_dec_ref(v_s_264_);
lean_dec(v_p_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_268_){
_start:
{
lean_object* v_startInclusive_269_; lean_object* v_endExclusive_270_; lean_object* v___x_271_; 
v_startInclusive_269_ = lean_ctor_get(v_s_268_, 1);
v_endExclusive_270_ = lean_ctor_get(v_s_268_, 2);
v___x_271_ = lean_nat_sub(v_endExclusive_270_, v_startInclusive_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_String_Slice_rawEndPos(v_s_272_);
lean_dec_ref(v_s_272_);
return v_res_273_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_274_, lean_object* v_p_275_){
_start:
{
lean_object* v_str_276_; lean_object* v_startInclusive_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_str_276_ = lean_ctor_get(v_s_274_, 0);
v_startInclusive_277_ = lean_ctor_get(v_s_274_, 1);
v___x_278_ = lean_nat_add(v_startInclusive_277_, v_p_275_);
v___x_279_ = lean_string_get_byte_fast(v_str_276_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* v_s_280_, lean_object* v_p_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_String_Slice_getUTF8Byte___redArg(v_s_280_, v_p_281_);
lean_dec(v_p_281_);
lean_dec_ref(v_s_280_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_284_, lean_object* v_p_285_, lean_object* v_h_286_){
_start:
{
lean_object* v_str_287_; lean_object* v_startInclusive_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_str_287_ = lean_ctor_get(v_s_284_, 0);
v_startInclusive_288_ = lean_ctor_get(v_s_284_, 1);
v___x_289_ = lean_nat_add(v_startInclusive_288_, v_p_285_);
v___x_290_ = lean_string_get_byte_fast(v_str_287_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_291_, lean_object* v_p_292_, lean_object* v_h_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_String_Slice_getUTF8Byte(v_s_291_, v_p_292_, v_h_293_);
lean_dec(v_p_292_);
lean_dec_ref(v_s_291_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_296_){
_start:
{
uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_297_ = 0;
v___x_298_ = lean_box(v___x_297_);
v___x_299_ = lean_panic_fn_borrowed(v___x_298_, v_msg_296_);
lean_dec(v___x_298_);
v___x_300_ = lean_unbox(v___x_299_);
lean_dec(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_307_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_unsigned_to_nat(512u);
v___x_310_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_311_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_312_ = l_mkPanicMessageWithDecl(v___x_311_, v___x_310_, v___x_309_, v___x_308_, v___x_307_);
return v___x_312_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_313_, lean_object* v_p_314_){
_start:
{
lean_object* v_str_315_; lean_object* v_startInclusive_316_; lean_object* v_endExclusive_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_str_315_ = lean_ctor_get(v_s_313_, 0);
v_startInclusive_316_ = lean_ctor_get(v_s_313_, 1);
v_endExclusive_317_ = lean_ctor_get(v_s_313_, 2);
v___x_318_ = lean_nat_sub(v_endExclusive_317_, v_startInclusive_316_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_add(v_p_314_, v___x_319_);
v___x_321_ = lean_nat_dec_le(v___x_320_, v___x_318_);
lean_dec(v___x_318_);
lean_dec(v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_323_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_nat_add(v_startInclusive_316_, v_p_314_);
v___x_325_ = lean_string_get_byte_fast(v_str_315_, v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_326_, lean_object* v_p_327_){
_start:
{
uint8_t v_res_328_; lean_object* v_r_329_; 
v_res_328_ = l_String_Slice_getUTF8Byte_x21(v_s_326_, v_p_327_);
lean_dec(v_p_327_);
lean_dec_ref(v_s_326_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
uint8_t v_decide_332_; 
v_decide_332_ = lean_nat_dec_eq(v_x_330_, v_x_331_);
return v_decide_332_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_333_, v_x_334_);
lean_dec(v_x_334_);
lean_dec(v_x_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_decide_340_; 
v_decide_340_ = lean_nat_dec_eq(v_x_338_, v_x_339_);
return v_decide_340_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_String_Slice_instDecidableEqPos_decEq(v_s_341_, v_x_342_, v_x_343_);
lean_dec(v_x_343_);
lean_dec(v_x_342_);
lean_dec_ref(v_s_341_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
uint8_t v_decide_348_; 
v_decide_348_ = lean_nat_dec_eq(v_x_346_, v_x_347_);
return v_decide_348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_String_Slice_instDecidableEqPos___redArg(v_x_349_, v_x_350_);
lean_dec(v_x_350_);
lean_dec(v_x_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v_decide_356_; 
v_decide_356_ = lean_nat_dec_eq(v_x_354_, v_x_355_);
return v_decide_356_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_String_Slice_instDecidableEqPos(v_s_357_, v_x_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec(v_x_358_);
lean_dec_ref(v_s_357_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_unsigned_to_nat(0u);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_String_Slice_startPos(v_s_364_);
lean_dec_ref(v_s_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_unsigned_to_nat(0u);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_String_instInhabitedPos__1(v_s_368_);
lean_dec_ref(v_s_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_370_){
_start:
{
lean_object* v_startInclusive_371_; lean_object* v_endExclusive_372_; lean_object* v___x_373_; 
v_startInclusive_371_ = lean_ctor_get(v_s_370_, 1);
v_endExclusive_372_ = lean_ctor_get(v_s_370_, 2);
v___x_373_ = lean_nat_sub(v_endExclusive_372_, v_startInclusive_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_String_Slice_endPos(v_s_374_);
lean_dec_ref(v_s_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_instLEPos__1(v_s_378_);
lean_dec_ref(v_s_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_String_instLTPos__1(v_s_382_);
lean_dec_ref(v_s_382_);
return v_res_383_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_384_, lean_object* v_r_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_le(v_l_384_, v_r_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_387_, lean_object* v_r_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_String_instDecidableLePos__1___redArg(v_l_387_, v_r_388_);
lean_dec(v_r_388_);
lean_dec(v_l_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_391_, lean_object* v_l_392_, lean_object* v_r_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_nat_dec_le(v_l_392_, v_r_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_395_, lean_object* v_l_396_, lean_object* v_r_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_String_instDecidableLePos__1(v_s_395_, v_l_396_, v_r_397_);
lean_dec(v_r_397_);
lean_dec(v_l_396_);
lean_dec_ref(v_s_395_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_400_, lean_object* v_r_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_add(v_l_400_, v___x_402_);
v___x_404_ = lean_nat_dec_le(v___x_403_, v_r_401_);
lean_dec(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_405_, lean_object* v_r_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_String_instDecidableLtPos__1___redArg(v_l_405_, v_r_406_);
lean_dec(v_r_406_);
lean_dec(v_l_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_409_, lean_object* v_l_410_, lean_object* v_r_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = l_String_instDecidableLtPos__1___redArg(v_l_410_, v_r_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_413_, lean_object* v_l_414_, lean_object* v_r_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_String_instDecidableLtPos__1(v_s_413_, v_l_414_, v_r_415_);
lean_dec(v_r_415_);
lean_dec(v_l_414_);
lean_dec_ref(v_s_413_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_418_, lean_object* v_pos_419_){
_start:
{
lean_object* v___x_420_; uint8_t v_decide_421_; 
v___x_420_ = lean_string_utf8_byte_size(v_s_418_);
v_decide_421_ = lean_nat_dec_eq(v_pos_419_, v___x_420_);
return v_decide_421_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_422_, lean_object* v_pos_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_String_instDecidableIsAtEnd(v_s_422_, v_pos_423_);
lean_dec(v_pos_423_);
lean_dec_ref(v_s_422_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_426_, lean_object* v_pos_427_){
_start:
{
lean_object* v_startInclusive_428_; lean_object* v_endExclusive_429_; lean_object* v___x_430_; uint8_t v_decide_431_; 
v_startInclusive_428_ = lean_ctor_get(v_s_426_, 1);
v_endExclusive_429_ = lean_ctor_get(v_s_426_, 2);
v___x_430_ = lean_nat_sub(v_endExclusive_429_, v_startInclusive_428_);
v_decide_431_ = lean_nat_dec_eq(v_pos_427_, v___x_430_);
lean_dec(v___x_430_);
return v_decide_431_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_432_, lean_object* v_pos_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_String_instDecidableIsAtEnd__1(v_s_432_, v_pos_433_);
lean_dec(v_pos_433_);
lean_dec_ref(v_s_432_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_436_, lean_object* v_pos_437_){
_start:
{
lean_object* v_str_438_; lean_object* v_startInclusive_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_str_438_ = lean_ctor_get(v_s_436_, 0);
v_startInclusive_439_ = lean_ctor_get(v_s_436_, 1);
v___x_440_ = lean_nat_add(v_startInclusive_439_, v_pos_437_);
v___x_441_ = lean_string_get_byte_fast(v_str_438_, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_442_, lean_object* v_pos_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_String_Slice_Pos_byte___redArg(v_s_442_, v_pos_443_);
lean_dec(v_pos_443_);
lean_dec_ref(v_s_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_446_, lean_object* v_pos_447_, lean_object* v_h_448_){
_start:
{
lean_object* v_str_449_; lean_object* v_startInclusive_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_str_449_ = lean_ctor_get(v_s_446_, 0);
v_startInclusive_450_ = lean_ctor_get(v_s_446_, 1);
v___x_451_ = lean_nat_add(v_startInclusive_450_, v_pos_447_);
v___x_452_ = lean_string_get_byte_fast(v_str_449_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_453_, lean_object* v_pos_454_, lean_object* v_h_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_String_Slice_Pos_byte(v_s_453_, v_pos_454_, v_h_455_);
lean_dec(v_pos_454_);
lean_dec_ref(v_s_453_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_458_){
_start:
{
lean_object* v_startInclusive_459_; lean_object* v_endExclusive_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_startInclusive_459_ = lean_ctor_get(v_s_458_, 1);
v_endExclusive_460_ = lean_ctor_get(v_s_458_, 2);
v___x_461_ = lean_nat_sub(v_endExclusive_460_, v_startInclusive_459_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_nat_dec_eq(v___x_461_, v___x_462_);
lean_dec(v___x_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_String_Slice_isEmpty(v_s_464_);
lean_dec_ref(v_s_464_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_string_utf8_byte_size(v_s_467_);
v___x_470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_470_, 0, v_s_467_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_String_toRawSubstring_x27(v_s_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_unsigned_to_nat(0u);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_String_startValidPos(v_s_475_);
lean_dec_ref(v_s_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = lean_string_utf8_byte_size(v_s_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_String_endValidPos(v_s_479_);
lean_dec_ref(v_s_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_String_bytes(lean_object* v_s_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_string_to_utf8(v_s_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii(lean_object* v_s_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_string_utf8_byte_size(v_s_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii___boxed(lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_String_lengthAssumingAscii(v_s_485_);
lean_dec_ref(v_s_485_);
return v_res_486_;
}
}
lean_object* runtime_initialize_Init_Data_String_PosRaw(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
