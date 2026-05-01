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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedUInt8;
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
lean_dec_ref(v_x_122_);
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
uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_eq(v_x_133_, v_x_134_);
return v___x_135_;
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
uint8_t v___x_143_; 
v___x_143_ = lean_nat_dec_eq(v_x_141_, v_x_142_);
return v___x_143_;
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
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_eq(v_x_149_, v_x_150_);
return v___x_151_;
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
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_eq(v_x_157_, v_x_158_);
return v___x_159_;
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
uint8_t v___x_203_; 
v___x_203_ = lean_nat_dec_lt(v_l_201_, v_r_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_204_, lean_object* v_r_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_String_instDecidableLtPos___redArg(v_l_204_, v_r_205_);
lean_dec(v_r_205_);
lean_dec(v_l_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* v_s_208_, lean_object* v_l_209_, lean_object* v_r_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = lean_nat_dec_lt(v_l_209_, v_r_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_212_, lean_object* v_l_213_, lean_object* v_r_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_String_instDecidableLtPos(v_s_212_, v_l_213_, v_r_214_);
lean_dec(v_r_214_);
lean_dec(v_l_213_);
lean_dec_ref(v_s_212_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_string_utf8_byte_size(v_s_221_);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v_s_221_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set(v___x_224_, 2, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_227_){
_start:
{
lean_object* v_startInclusive_228_; lean_object* v_endExclusive_229_; lean_object* v___x_230_; 
v_startInclusive_228_ = lean_ctor_get(v_s_227_, 1);
v_endExclusive_229_ = lean_ctor_get(v_s_227_, 2);
v___x_230_ = lean_nat_sub(v_endExclusive_229_, v_startInclusive_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_String_Slice_utf8ByteSize(v_s_231_);
lean_dec_ref(v_s_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_233_, lean_object* v_s_234_){
_start:
{
lean_object* v_startInclusive_235_; lean_object* v_endExclusive_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_startInclusive_235_ = lean_ctor_get(v_s_234_, 1);
v_endExclusive_236_ = lean_ctor_get(v_s_234_, 2);
v___x_237_ = lean_nat_sub(v_endExclusive_236_, v_startInclusive_235_);
v___x_238_ = lean_nat_add(v_p_233_, v___x_237_);
lean_dec(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_239_, lean_object* v_s_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_String_instHAddRawSlice___lam__0(v_p_239_, v_s_240_);
lean_dec_ref(v_s_240_);
lean_dec(v_p_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_244_, lean_object* v_p_245_){
_start:
{
lean_object* v_startInclusive_246_; lean_object* v_endExclusive_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_startInclusive_246_ = lean_ctor_get(v_s_244_, 1);
v_endExclusive_247_ = lean_ctor_get(v_s_244_, 2);
v___x_248_ = lean_nat_sub(v_endExclusive_247_, v_startInclusive_246_);
v___x_249_ = lean_nat_add(v___x_248_, v_p_245_);
lean_dec(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_250_, lean_object* v_p_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_String_instHAddSliceRaw___lam__0(v_s_250_, v_p_251_);
lean_dec(v_p_251_);
lean_dec_ref(v_s_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_255_, lean_object* v_s_256_){
_start:
{
lean_object* v_startInclusive_257_; lean_object* v_endExclusive_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_startInclusive_257_ = lean_ctor_get(v_s_256_, 1);
v_endExclusive_258_ = lean_ctor_get(v_s_256_, 2);
v___x_259_ = lean_nat_sub(v_endExclusive_258_, v_startInclusive_257_);
v___x_260_ = lean_nat_sub(v_p_255_, v___x_259_);
lean_dec(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_261_, lean_object* v_s_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_String_instHSubRawSlice___lam__0(v_p_261_, v_s_262_);
lean_dec_ref(v_s_262_);
lean_dec(v_p_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_266_){
_start:
{
lean_object* v_startInclusive_267_; lean_object* v_endExclusive_268_; lean_object* v___x_269_; 
v_startInclusive_267_ = lean_ctor_get(v_s_266_, 1);
v_endExclusive_268_ = lean_ctor_get(v_s_266_, 2);
v___x_269_ = lean_nat_sub(v_endExclusive_268_, v_startInclusive_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_String_Slice_rawEndPos(v_s_270_);
lean_dec_ref(v_s_270_);
return v_res_271_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_272_, lean_object* v_p_273_){
_start:
{
lean_object* v_str_274_; lean_object* v_startInclusive_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_str_274_ = lean_ctor_get(v_s_272_, 0);
v_startInclusive_275_ = lean_ctor_get(v_s_272_, 1);
v___x_276_ = lean_nat_add(v_startInclusive_275_, v_p_273_);
v___x_277_ = lean_string_get_byte_fast(v_str_274_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* v_s_278_, lean_object* v_p_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_String_Slice_getUTF8Byte___redArg(v_s_278_, v_p_279_);
lean_dec(v_p_279_);
lean_dec_ref(v_s_278_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_282_, lean_object* v_p_283_, lean_object* v_h_284_){
_start:
{
lean_object* v_str_285_; lean_object* v_startInclusive_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_str_285_ = lean_ctor_get(v_s_282_, 0);
v_startInclusive_286_ = lean_ctor_get(v_s_282_, 1);
v___x_287_ = lean_nat_add(v_startInclusive_286_, v_p_283_);
v___x_288_ = lean_string_get_byte_fast(v_str_285_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_289_, lean_object* v_p_290_, lean_object* v_h_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_String_Slice_getUTF8Byte(v_s_289_, v_p_290_, v_h_291_);
lean_dec(v_p_290_);
lean_dec_ref(v_s_289_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_294_){
_start:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_295_ = l_instInhabitedUInt8;
v___x_296_ = lean_box(v___x_295_);
v___x_297_ = lean_panic_fn_borrowed(v___x_296_, v_msg_294_);
lean_dec(v___x_296_);
v___x_298_ = lean_unbox(v___x_297_);
lean_dec(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_305_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_unsigned_to_nat(512u);
v___x_308_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_309_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_310_ = l_mkPanicMessageWithDecl(v___x_309_, v___x_308_, v___x_307_, v___x_306_, v___x_305_);
return v___x_310_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_311_, lean_object* v_p_312_){
_start:
{
lean_object* v_str_313_; lean_object* v_startInclusive_314_; lean_object* v_endExclusive_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_str_313_ = lean_ctor_get(v_s_311_, 0);
v_startInclusive_314_ = lean_ctor_get(v_s_311_, 1);
v_endExclusive_315_ = lean_ctor_get(v_s_311_, 2);
v___x_316_ = lean_nat_sub(v_endExclusive_315_, v_startInclusive_314_);
v___x_317_ = lean_nat_dec_lt(v_p_312_, v___x_316_);
lean_dec(v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_319_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_318_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_nat_add(v_startInclusive_314_, v_p_312_);
v___x_321_ = lean_string_get_byte_fast(v_str_313_, v___x_320_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_322_, lean_object* v_p_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_String_Slice_getUTF8Byte_x21(v_s_322_, v_p_323_);
lean_dec(v_p_323_);
lean_dec_ref(v_s_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_nat_dec_eq(v_x_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec(v_x_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_nat_dec_eq(v_x_334_, v_x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_String_Slice_instDecidableEqPos_decEq(v_s_337_, v_x_338_, v_x_339_);
lean_dec(v_x_339_);
lean_dec(v_x_338_);
lean_dec_ref(v_s_337_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = lean_nat_dec_eq(v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_String_Slice_instDecidableEqPos___redArg(v_x_345_, v_x_346_);
lean_dec(v_x_346_);
lean_dec(v_x_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_eq(v_x_350_, v_x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_String_Slice_instDecidableEqPos(v_s_353_, v_x_354_, v_x_355_);
lean_dec(v_x_355_);
lean_dec(v_x_354_);
lean_dec_ref(v_s_353_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_unsigned_to_nat(0u);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_String_Slice_startPos(v_s_360_);
lean_dec_ref(v_s_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_unsigned_to_nat(0u);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_String_instInhabitedPos__1(v_s_364_);
lean_dec_ref(v_s_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_366_){
_start:
{
lean_object* v_startInclusive_367_; lean_object* v_endExclusive_368_; lean_object* v___x_369_; 
v_startInclusive_367_ = lean_ctor_get(v_s_366_, 1);
v_endExclusive_368_ = lean_ctor_get(v_s_366_, 2);
v___x_369_ = lean_nat_sub(v_endExclusive_368_, v_startInclusive_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_String_Slice_endPos(v_s_370_);
lean_dec_ref(v_s_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_box(0);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_String_instLEPos__1(v_s_374_);
lean_dec_ref(v_s_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_instLTPos__1(v_s_378_);
lean_dec_ref(v_s_378_);
return v_res_379_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_380_, lean_object* v_r_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_nat_dec_le(v_l_380_, v_r_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_383_, lean_object* v_r_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_String_instDecidableLePos__1___redArg(v_l_383_, v_r_384_);
lean_dec(v_r_384_);
lean_dec(v_l_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_387_, lean_object* v_l_388_, lean_object* v_r_389_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = lean_nat_dec_le(v_l_388_, v_r_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_391_, lean_object* v_l_392_, lean_object* v_r_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_String_instDecidableLePos__1(v_s_391_, v_l_392_, v_r_393_);
lean_dec(v_r_393_);
lean_dec(v_l_392_);
lean_dec_ref(v_s_391_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_396_, lean_object* v_r_397_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_lt(v_l_396_, v_r_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_399_, lean_object* v_r_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_String_instDecidableLtPos__1___redArg(v_l_399_, v_r_400_);
lean_dec(v_r_400_);
lean_dec(v_l_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_403_, lean_object* v_l_404_, lean_object* v_r_405_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_lt(v_l_404_, v_r_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_407_, lean_object* v_l_408_, lean_object* v_r_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_String_instDecidableLtPos__1(v_s_407_, v_l_408_, v_r_409_);
lean_dec(v_r_409_);
lean_dec(v_l_408_);
lean_dec_ref(v_s_407_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_412_, lean_object* v_pos_413_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_string_utf8_byte_size(v_s_412_);
v___x_415_ = lean_nat_dec_eq(v_pos_413_, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_416_, lean_object* v_pos_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_String_instDecidableIsAtEnd(v_s_416_, v_pos_417_);
lean_dec(v_pos_417_);
lean_dec_ref(v_s_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_420_, lean_object* v_pos_421_){
_start:
{
lean_object* v_startInclusive_422_; lean_object* v_endExclusive_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_startInclusive_422_ = lean_ctor_get(v_s_420_, 1);
v_endExclusive_423_ = lean_ctor_get(v_s_420_, 2);
v___x_424_ = lean_nat_sub(v_endExclusive_423_, v_startInclusive_422_);
v___x_425_ = lean_nat_dec_eq(v_pos_421_, v___x_424_);
lean_dec(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_426_, lean_object* v_pos_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_String_instDecidableIsAtEnd__1(v_s_426_, v_pos_427_);
lean_dec(v_pos_427_);
lean_dec_ref(v_s_426_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_430_, lean_object* v_pos_431_){
_start:
{
lean_object* v_str_432_; lean_object* v_startInclusive_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_str_432_ = lean_ctor_get(v_s_430_, 0);
v_startInclusive_433_ = lean_ctor_get(v_s_430_, 1);
v___x_434_ = lean_nat_add(v_startInclusive_433_, v_pos_431_);
v___x_435_ = lean_string_get_byte_fast(v_str_432_, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_436_, lean_object* v_pos_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_String_Slice_Pos_byte___redArg(v_s_436_, v_pos_437_);
lean_dec(v_pos_437_);
lean_dec_ref(v_s_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_440_, lean_object* v_pos_441_, lean_object* v_h_442_){
_start:
{
lean_object* v_str_443_; lean_object* v_startInclusive_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_str_443_ = lean_ctor_get(v_s_440_, 0);
v_startInclusive_444_ = lean_ctor_get(v_s_440_, 1);
v___x_445_ = lean_nat_add(v_startInclusive_444_, v_pos_441_);
v___x_446_ = lean_string_get_byte_fast(v_str_443_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_447_, lean_object* v_pos_448_, lean_object* v_h_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_String_Slice_Pos_byte(v_s_447_, v_pos_448_, v_h_449_);
lean_dec(v_pos_448_);
lean_dec_ref(v_s_447_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_452_){
_start:
{
lean_object* v_startInclusive_453_; lean_object* v_endExclusive_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_startInclusive_453_ = lean_ctor_get(v_s_452_, 1);
v_endExclusive_454_ = lean_ctor_get(v_s_452_, 2);
v___x_455_ = lean_nat_sub(v_endExclusive_454_, v_startInclusive_453_);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_nat_dec_eq(v___x_455_, v___x_456_);
lean_dec(v___x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_String_Slice_isEmpty(v_s_458_);
lean_dec_ref(v_s_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_string_utf8_byte_size(v_s_461_);
v___x_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_464_, 0, v_s_461_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_String_toRawSubstring_x27(v_s_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_unsigned_to_nat(0u);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_String_startValidPos(v_s_469_);
lean_dec_ref(v_s_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_string_utf8_byte_size(v_s_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_String_endValidPos(v_s_473_);
lean_dec_ref(v_s_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_String_String_bytes(lean_object* v_s_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_string_to_utf8(v_s_475_);
return v___x_476_;
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
