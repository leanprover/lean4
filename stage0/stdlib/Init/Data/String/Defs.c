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
lean_object* lean_string_mark_linear(lean_object*);
LEAN_EXPORT lean_object* l_String_markLinear___boxed(lean_object*);
lean_object* lean_string_propagate_mark(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_propagateMark___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_markLinear___boxed(lean_object* v_s_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lean_string_mark_linear(v_s_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_String_propagateMark___boxed(lean_object* v_s_26_, lean_object* v_t_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lean_string_propagate_mark(v_s_26_, v_t_27_);
lean_dec_ref(v_s_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(lean_object* v_x_29_, uint32_t v_x_30_, lean_object* v_h__1_31_){
_start:
{
lean_object* v_toByteArray_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_toByteArray_32_ = lean_string_to_utf8(v_x_29_);
v___x_33_ = lean_box_uint32(v_x_30_);
v___x_34_ = lean_apply_3(v_h__1_31_, v_toByteArray_32_, lean_box(0), v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg___boxed(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_h__1_37_){
_start:
{
uint32_t v_x_18__boxed_38_; lean_object* v_res_39_; 
v_x_18__boxed_38_ = lean_unbox_uint32(v_x_36_);
lean_dec(v_x_36_);
v_res_39_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(v_x_35_, v_x_18__boxed_38_, v_h__1_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(lean_object* v_motive_40_, lean_object* v_x_41_, uint32_t v_x_42_, lean_object* v_h__1_43_){
_start:
{
lean_object* v_toByteArray_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_toByteArray_44_ = lean_string_to_utf8(v_x_41_);
v___x_45_ = lean_box_uint32(v_x_42_);
v___x_46_ = lean_apply_3(v_h__1_43_, v_toByteArray_44_, lean_box(0), v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___boxed(lean_object* v_motive_47_, lean_object* v_x_48_, lean_object* v_x_49_, lean_object* v_h__1_50_){
_start:
{
uint32_t v_x_30__boxed_51_; lean_object* v_res_52_; 
v_x_30__boxed_51_ = lean_unbox_uint32(v_x_49_);
lean_dec(v_x_49_);
v_res_52_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(v_motive_47_, v_x_48_, v_x_30__boxed_51_, v_h__1_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_unsigned_to_nat(0u);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_String_rawStartPos(v___s_55_);
lean_dec_ref(v___s_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t v_c_57_, lean_object* v_s_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_string_push(v_s_58_, v_c_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_60_, lean_object* v_s_61_){
_start:
{
uint32_t v_c_boxed_62_; lean_object* v_res_63_; 
v_c_boxed_62_ = lean_unbox_uint32(v_c_60_);
lean_dec(v_c_60_);
v_res_63_ = l_String_pushn___lam__0(v_c_boxed_62_, v_s_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* v_s_64_, uint32_t v_c_65_, lean_object* v_n_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___f_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box_uint32(v_c_65_);
v___f_68_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_68_, 0, v___x_67_);
v___x_69_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_68_, v_n_66_, v_s_64_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_70_, lean_object* v_c_71_, lean_object* v_n_72_){
_start:
{
uint32_t v_c_boxed_73_; lean_object* v_res_74_; 
v_c_boxed_73_ = lean_unbox_uint32(v_c_71_);
lean_dec(v_c_71_);
v_res_74_ = l_String_pushn(v_s_70_, v_c_boxed_73_, v_n_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_zero_78_; uint8_t v_isZero_79_; 
v_zero_78_ = lean_unsigned_to_nat(0u);
v_isZero_79_ = lean_nat_dec_eq(v_x_76_, v_zero_78_);
if (v_isZero_79_ == 1)
{
lean_dec(v_x_76_);
return v_x_77_;
}
else
{
lean_object* v_one_80_; lean_object* v_n_81_; lean_object* v___x_82_; 
v_one_80_ = lean_unsigned_to_nat(1u);
v_n_81_ = lean_nat_sub(v_x_76_, v_one_80_);
lean_dec(v_x_76_);
v___x_82_ = lean_string_push(v_x_77_, v_c_75_);
v_x_76_ = v_n_81_;
v_x_77_ = v___x_82_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint32_t v_c_boxed_87_; lean_object* v_res_88_; 
v_c_boxed_87_ = lean_unbox_uint32(v_c_84_);
lean_dec(v_c_84_);
v_res_88_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_87_, v_x_85_, v_x_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* v_s_89_, uint32_t v_c_90_, lean_object* v_n_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_90_, v_n_91_, v_s_89_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_93_, lean_object* v_c_94_, lean_object* v_n_95_){
_start:
{
uint32_t v_c_boxed_96_; lean_object* v_res_97_; 
v_c_boxed_96_ = lean_unbox_uint32(v_c_94_);
lean_dec(v_c_94_);
v_res_97_ = lean_string_pushn(v_s_93_, v_c_boxed_96_, v_n_95_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* v_s_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_string_utf8_byte_size(v_s_98_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_nat_dec_eq(v___x_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_String_isEmpty(v_s_102_);
lean_dec_ref(v_s_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* v_s_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_string_utf8_byte_size(v_s_105_);
lean_dec_ref(v_s_105_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_dec_eq(v___x_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = lean_string_isempty(v_s_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___f_114_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_115_ = ((lean_object*)(l_String_join___closed__0));
v___x_116_ = l_List_foldl___redArg(v___f_114_, v___x_115_, v_l_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_117_, lean_object* v_s_118_, lean_object* v_a_119_){
_start:
{
if (lean_obj_tag(v_a_119_) == 0)
{
return v_acc_117_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_head_120_ = lean_ctor_get(v_a_119_, 0);
v_tail_121_ = lean_ctor_get(v_a_119_, 1);
v___x_122_ = lean_string_append(v_acc_117_, v_s_118_);
v___x_123_ = lean_string_append(v___x_122_, v_head_120_);
v_acc_117_ = v___x_123_;
v_a_119_ = v_tail_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_125_, lean_object* v_s_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_125_, v_s_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_s_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v___x_131_; 
v___x_131_ = ((lean_object*)(l_String_join___closed__0));
return v___x_131_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_134_; 
v_head_132_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_head_132_);
v_tail_133_ = lean_ctor_get(v_x_130_, 1);
lean_inc(v_tail_133_);
lean_dec_ref_known(v_x_130_, 2);
v___x_134_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_132_, v_s_129_, v_tail_133_);
lean_dec(v_tail_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_String_intercalate(v_s_135_, v_x_136_);
lean_dec_ref(v_s_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_String_intercalate(v_s_138_, v_a_139_);
lean_dec_ref(v_s_138_);
return v___x_140_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
uint8_t v_decide_143_; 
v_decide_143_ = lean_nat_dec_eq(v_x_141_, v_x_142_);
return v_decide_143_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_String_instDecidableEqPos_decEq___redArg(v_x_144_, v_x_145_);
lean_dec(v_x_145_);
lean_dec(v_x_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_decide_151_; 
v_decide_151_ = lean_nat_dec_eq(v_x_149_, v_x_150_);
return v_decide_151_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_String_instDecidableEqPos_decEq(v_s_152_, v_x_153_, v_x_154_);
lean_dec(v_x_154_);
lean_dec(v_x_153_);
lean_dec_ref(v_s_152_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_decide_159_; 
v_decide_159_ = lean_nat_dec_eq(v_x_157_, v_x_158_);
return v_decide_159_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_String_instDecidableEqPos___redArg(v_x_160_, v_x_161_);
lean_dec(v_x_161_);
lean_dec(v_x_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* v_s_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
uint8_t v_decide_167_; 
v_decide_167_ = lean_nat_dec_eq(v_x_165_, v_x_166_);
return v_decide_167_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_String_instDecidableEqPos(v_s_168_, v_x_169_, v_x_170_);
lean_dec(v_x_170_);
lean_dec(v_x_169_);
lean_dec_ref(v_s_168_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* v_s_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_unsigned_to_nat(0u);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* v_s_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_String_startPos(v_s_175_);
lean_dec_ref(v_s_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(0u);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_String_instInhabitedPos(v_s_179_);
lean_dec_ref(v_s_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_string_utf8_byte_size(v_s_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_String_endPos(v_s_183_);
lean_dec_ref(v_s_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* v_s_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* v_s_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_String_instLEPos(v_s_187_);
lean_dec_ref(v_s_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_String_instLTPos(v_s_191_);
lean_dec_ref(v_s_191_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_193_, lean_object* v_r_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_le(v_l_193_, v_r_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_196_, lean_object* v_r_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_String_instDecidableLePos___redArg(v_l_196_, v_r_197_);
lean_dec(v_r_197_);
lean_dec(v_l_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* v_s_200_, lean_object* v_l_201_, lean_object* v_r_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lean_nat_dec_le(v_l_201_, v_r_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_204_, lean_object* v_l_205_, lean_object* v_r_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_String_instDecidableLePos(v_s_204_, v_l_205_, v_r_206_);
lean_dec(v_r_206_);
lean_dec(v_l_205_);
lean_dec_ref(v_s_204_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_209_, lean_object* v_r_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_l_209_, v___x_211_);
v___x_213_ = lean_nat_dec_le(v___x_212_, v_r_210_);
lean_dec(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_214_, lean_object* v_r_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_String_instDecidableLtPos___redArg(v_l_214_, v_r_215_);
lean_dec(v_r_215_);
lean_dec(v_l_214_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* v_s_218_, lean_object* v_l_219_, lean_object* v_r_220_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = l_String_instDecidableLtPos___redArg(v_l_219_, v_r_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_222_, lean_object* v_l_223_, lean_object* v_r_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_String_instDecidableLtPos(v_s_222_, v_l_223_, v_r_224_);
lean_dec(v_r_224_);
lean_dec(v_l_223_);
lean_dec_ref(v_s_222_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_string_utf8_byte_size(v_s_231_);
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v_s_231_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_237_){
_start:
{
lean_object* v_startInclusive_238_; lean_object* v_endExclusive_239_; lean_object* v___x_240_; 
v_startInclusive_238_ = lean_ctor_get(v_s_237_, 1);
v_endExclusive_239_ = lean_ctor_get(v_s_237_, 2);
v___x_240_ = lean_nat_sub(v_endExclusive_239_, v_startInclusive_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_String_Slice_utf8ByteSize(v_s_241_);
lean_dec_ref(v_s_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_243_, lean_object* v_s_244_){
_start:
{
lean_object* v_startInclusive_245_; lean_object* v_endExclusive_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_startInclusive_245_ = lean_ctor_get(v_s_244_, 1);
v_endExclusive_246_ = lean_ctor_get(v_s_244_, 2);
v___x_247_ = lean_nat_sub(v_endExclusive_246_, v_startInclusive_245_);
v___x_248_ = lean_nat_add(v_p_243_, v___x_247_);
lean_dec(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_249_, lean_object* v_s_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_String_instHAddRawSlice___lam__0(v_p_249_, v_s_250_);
lean_dec_ref(v_s_250_);
lean_dec(v_p_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_254_, lean_object* v_p_255_){
_start:
{
lean_object* v_startInclusive_256_; lean_object* v_endExclusive_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_startInclusive_256_ = lean_ctor_get(v_s_254_, 1);
v_endExclusive_257_ = lean_ctor_get(v_s_254_, 2);
v___x_258_ = lean_nat_sub(v_endExclusive_257_, v_startInclusive_256_);
v___x_259_ = lean_nat_add(v___x_258_, v_p_255_);
lean_dec(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_260_, lean_object* v_p_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_String_instHAddSliceRaw___lam__0(v_s_260_, v_p_261_);
lean_dec(v_p_261_);
lean_dec_ref(v_s_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_265_, lean_object* v_s_266_){
_start:
{
lean_object* v_startInclusive_267_; lean_object* v_endExclusive_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_startInclusive_267_ = lean_ctor_get(v_s_266_, 1);
v_endExclusive_268_ = lean_ctor_get(v_s_266_, 2);
v___x_269_ = lean_nat_sub(v_endExclusive_268_, v_startInclusive_267_);
v___x_270_ = lean_nat_sub(v_p_265_, v___x_269_);
lean_dec(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_271_, lean_object* v_s_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_String_instHSubRawSlice___lam__0(v_p_271_, v_s_272_);
lean_dec_ref(v_s_272_);
lean_dec(v_p_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_276_){
_start:
{
lean_object* v_startInclusive_277_; lean_object* v_endExclusive_278_; lean_object* v___x_279_; 
v_startInclusive_277_ = lean_ctor_get(v_s_276_, 1);
v_endExclusive_278_ = lean_ctor_get(v_s_276_, 2);
v___x_279_ = lean_nat_sub(v_endExclusive_278_, v_startInclusive_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_String_Slice_rawEndPos(v_s_280_);
lean_dec_ref(v_s_280_);
return v_res_281_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_282_, lean_object* v_p_283_){
_start:
{
lean_object* v_str_284_; lean_object* v_startInclusive_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_str_284_ = lean_ctor_get(v_s_282_, 0);
v_startInclusive_285_ = lean_ctor_get(v_s_282_, 1);
v___x_286_ = lean_nat_add(v_startInclusive_285_, v_p_283_);
v___x_287_ = lean_string_get_byte_fast(v_str_284_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* v_s_288_, lean_object* v_p_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_String_Slice_getUTF8Byte___redArg(v_s_288_, v_p_289_);
lean_dec(v_p_289_);
lean_dec_ref(v_s_288_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_292_, lean_object* v_p_293_, lean_object* v_h_294_){
_start:
{
lean_object* v_str_295_; lean_object* v_startInclusive_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_str_295_ = lean_ctor_get(v_s_292_, 0);
v_startInclusive_296_ = lean_ctor_get(v_s_292_, 1);
v___x_297_ = lean_nat_add(v_startInclusive_296_, v_p_293_);
v___x_298_ = lean_string_get_byte_fast(v_str_295_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_299_, lean_object* v_p_300_, lean_object* v_h_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_String_Slice_getUTF8Byte(v_s_299_, v_p_300_, v_h_301_);
lean_dec(v_p_300_);
lean_dec_ref(v_s_299_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_304_){
_start:
{
uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_305_ = 0;
v___x_306_ = lean_box(v___x_305_);
v___x_307_ = lean_panic_fn_borrowed(v___x_306_, v_msg_304_);
lean_dec(v___x_306_);
v___x_308_ = lean_unbox(v___x_307_);
lean_dec(v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_315_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_316_ = lean_unsigned_to_nat(4u);
v___x_317_ = lean_unsigned_to_nat(536u);
v___x_318_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_319_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_320_ = l_mkPanicMessageWithDecl(v___x_319_, v___x_318_, v___x_317_, v___x_316_, v___x_315_);
return v___x_320_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_321_, lean_object* v_p_322_){
_start:
{
lean_object* v_str_323_; lean_object* v_startInclusive_324_; lean_object* v_endExclusive_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_str_323_ = lean_ctor_get(v_s_321_, 0);
v_startInclusive_324_ = lean_ctor_get(v_s_321_, 1);
v_endExclusive_325_ = lean_ctor_get(v_s_321_, 2);
v___x_326_ = lean_nat_sub(v_endExclusive_325_, v_startInclusive_324_);
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_p_322_, v___x_327_);
v___x_329_ = lean_nat_dec_le(v___x_328_, v___x_326_);
lean_dec(v___x_326_);
lean_dec(v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_331_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_nat_add(v_startInclusive_324_, v_p_322_);
v___x_333_ = lean_string_get_byte_fast(v_str_323_, v___x_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_334_, lean_object* v_p_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_String_Slice_getUTF8Byte_x21(v_s_334_, v_p_335_);
lean_dec(v_p_335_);
lean_dec_ref(v_s_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_decide_340_; 
v_decide_340_ = lean_nat_dec_eq(v_x_338_, v_x_339_);
return v_decide_340_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_341_, v_x_342_);
lean_dec(v_x_342_);
lean_dec(v_x_341_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
uint8_t v_decide_348_; 
v_decide_348_ = lean_nat_dec_eq(v_x_346_, v_x_347_);
return v_decide_348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_String_Slice_instDecidableEqPos_decEq(v_s_349_, v_x_350_, v_x_351_);
lean_dec(v_x_351_);
lean_dec(v_x_350_);
lean_dec_ref(v_s_349_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v_decide_356_; 
v_decide_356_ = lean_nat_dec_eq(v_x_354_, v_x_355_);
return v_decide_356_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_String_Slice_instDecidableEqPos___redArg(v_x_357_, v_x_358_);
lean_dec(v_x_358_);
lean_dec(v_x_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
uint8_t v_decide_364_; 
v_decide_364_ = lean_nat_dec_eq(v_x_362_, v_x_363_);
return v_decide_364_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_String_Slice_instDecidableEqPos(v_s_365_, v_x_366_, v_x_367_);
lean_dec(v_x_367_);
lean_dec(v_x_366_);
lean_dec_ref(v_s_365_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_unsigned_to_nat(0u);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_String_Slice_startPos(v_s_372_);
lean_dec_ref(v_s_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_unsigned_to_nat(0u);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_String_instInhabitedPos__1(v_s_376_);
lean_dec_ref(v_s_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_378_){
_start:
{
lean_object* v_startInclusive_379_; lean_object* v_endExclusive_380_; lean_object* v___x_381_; 
v_startInclusive_379_ = lean_ctor_get(v_s_378_, 1);
v_endExclusive_380_ = lean_ctor_get(v_s_378_, 2);
v___x_381_ = lean_nat_sub(v_endExclusive_380_, v_startInclusive_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_String_Slice_endPos(v_s_382_);
lean_dec_ref(v_s_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_String_instLEPos__1(v_s_386_);
lean_dec_ref(v_s_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_String_instLTPos__1(v_s_390_);
lean_dec_ref(v_s_390_);
return v_res_391_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_392_, lean_object* v_r_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_nat_dec_le(v_l_392_, v_r_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_395_, lean_object* v_r_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_String_instDecidableLePos__1___redArg(v_l_395_, v_r_396_);
lean_dec(v_r_396_);
lean_dec(v_l_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_399_, lean_object* v_l_400_, lean_object* v_r_401_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_nat_dec_le(v_l_400_, v_r_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_403_, lean_object* v_l_404_, lean_object* v_r_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_String_instDecidableLePos__1(v_s_403_, v_l_404_, v_r_405_);
lean_dec(v_r_405_);
lean_dec(v_l_404_);
lean_dec_ref(v_s_403_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_408_, lean_object* v_r_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_l_408_, v___x_410_);
v___x_412_ = lean_nat_dec_le(v___x_411_, v_r_409_);
lean_dec(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_413_, lean_object* v_r_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_String_instDecidableLtPos__1___redArg(v_l_413_, v_r_414_);
lean_dec(v_r_414_);
lean_dec(v_l_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_417_, lean_object* v_l_418_, lean_object* v_r_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = l_String_instDecidableLtPos__1___redArg(v_l_418_, v_r_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_421_, lean_object* v_l_422_, lean_object* v_r_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_String_instDecidableLtPos__1(v_s_421_, v_l_422_, v_r_423_);
lean_dec(v_r_423_);
lean_dec(v_l_422_);
lean_dec_ref(v_s_421_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_426_, lean_object* v_pos_427_){
_start:
{
lean_object* v___x_428_; uint8_t v_decide_429_; 
v___x_428_ = lean_string_utf8_byte_size(v_s_426_);
v_decide_429_ = lean_nat_dec_eq(v_pos_427_, v___x_428_);
return v_decide_429_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_430_, lean_object* v_pos_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_String_instDecidableIsAtEnd(v_s_430_, v_pos_431_);
lean_dec(v_pos_431_);
lean_dec_ref(v_s_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_434_, lean_object* v_pos_435_){
_start:
{
lean_object* v_startInclusive_436_; lean_object* v_endExclusive_437_; lean_object* v___x_438_; uint8_t v_decide_439_; 
v_startInclusive_436_ = lean_ctor_get(v_s_434_, 1);
v_endExclusive_437_ = lean_ctor_get(v_s_434_, 2);
v___x_438_ = lean_nat_sub(v_endExclusive_437_, v_startInclusive_436_);
v_decide_439_ = lean_nat_dec_eq(v_pos_435_, v___x_438_);
lean_dec(v___x_438_);
return v_decide_439_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_440_, lean_object* v_pos_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_String_instDecidableIsAtEnd__1(v_s_440_, v_pos_441_);
lean_dec(v_pos_441_);
lean_dec_ref(v_s_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_444_, lean_object* v_pos_445_){
_start:
{
lean_object* v_str_446_; lean_object* v_startInclusive_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_str_446_ = lean_ctor_get(v_s_444_, 0);
v_startInclusive_447_ = lean_ctor_get(v_s_444_, 1);
v___x_448_ = lean_nat_add(v_startInclusive_447_, v_pos_445_);
v___x_449_ = lean_string_get_byte_fast(v_str_446_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_450_, lean_object* v_pos_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_String_Slice_Pos_byte___redArg(v_s_450_, v_pos_451_);
lean_dec(v_pos_451_);
lean_dec_ref(v_s_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_454_, lean_object* v_pos_455_, lean_object* v_h_456_){
_start:
{
lean_object* v_str_457_; lean_object* v_startInclusive_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_str_457_ = lean_ctor_get(v_s_454_, 0);
v_startInclusive_458_ = lean_ctor_get(v_s_454_, 1);
v___x_459_ = lean_nat_add(v_startInclusive_458_, v_pos_455_);
v___x_460_ = lean_string_get_byte_fast(v_str_457_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_461_, lean_object* v_pos_462_, lean_object* v_h_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_String_Slice_Pos_byte(v_s_461_, v_pos_462_, v_h_463_);
lean_dec(v_pos_462_);
lean_dec_ref(v_s_461_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_466_){
_start:
{
lean_object* v_startInclusive_467_; lean_object* v_endExclusive_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_startInclusive_467_ = lean_ctor_get(v_s_466_, 1);
v_endExclusive_468_ = lean_ctor_get(v_s_466_, 2);
v___x_469_ = lean_nat_sub(v_endExclusive_468_, v_startInclusive_467_);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_nat_dec_eq(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_String_Slice_isEmpty(v_s_472_);
lean_dec_ref(v_s_472_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_string_utf8_byte_size(v_s_475_);
v___x_478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_478_, 0, v_s_475_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
lean_ctor_set(v___x_478_, 2, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_String_toRawSubstring_x27(v_s_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_unsigned_to_nat(0u);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_String_startValidPos(v_s_483_);
lean_dec_ref(v_s_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_string_utf8_byte_size(v_s_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_String_endValidPos(v_s_487_);
lean_dec_ref(v_s_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_String_bytes(lean_object* v_s_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_string_to_utf8(v_s_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii(lean_object* v_s_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_string_utf8_byte_size(v_s_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii___boxed(lean_object* v_s_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_String_lengthAssumingAscii(v_s_493_);
lean_dec_ref(v_s_493_);
return v_res_494_;
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
