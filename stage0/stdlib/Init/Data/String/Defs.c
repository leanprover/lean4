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
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toUTF8(lean_object*);
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
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg();
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_startPos___redArg();
LEAN_EXPORT lean_object* l_String_startPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_startPos(lean_object*);
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg();
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_endPos(lean_object*);
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos___redArg();
LEAN_EXPORT lean_object* l_String_instLEPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos___redArg();
LEAN_EXPORT lean_object* l_String_instLTPos___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg();
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg();
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg();
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg();
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_startValidPos___redArg();
LEAN_EXPORT lean_object* l_String_startValidPos___redArg___boxed(lean_object*);
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
v___x_2_ = lean_string_from_utf8_unchecked(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object* v_a_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_string_from_utf8_unchecked(v_a_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_String_toUTF8(lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_string_to_utf8(v_a_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object* v_s_10_, lean_object* v_t_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lean_string_append(v_s_10_, v_t_11_);
lean_dec_ref(v_t_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_String_markLinear___boxed(lean_object* v_s_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lean_string_mark_linear(v_s_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_String_propagateMark___boxed(lean_object* v_s_20_, lean_object* v_t_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lean_string_propagate_mark(v_s_20_, v_t_21_);
lean_dec_ref(v_s_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(lean_object* v_x_23_, uint32_t v_x_24_, lean_object* v_h__1_25_){
_start:
{
lean_object* v_toByteArray_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_toByteArray_26_ = lean_string_to_utf8(v_x_23_);
v___x_27_ = lean_box_uint32(v_x_24_);
v___x_28_ = lean_apply_3(v_h__1_25_, v_toByteArray_26_, lean_box(0), v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg___boxed(lean_object* v_x_29_, lean_object* v_x_30_, lean_object* v_h__1_31_){
_start:
{
uint32_t v_x_18__boxed_32_; lean_object* v_res_33_; 
v_x_18__boxed_32_ = lean_unbox_uint32(v_x_30_);
lean_dec(v_x_30_);
v_res_33_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(v_x_29_, v_x_18__boxed_32_, v_h__1_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(lean_object* v_motive_34_, lean_object* v_x_35_, uint32_t v_x_36_, lean_object* v_h__1_37_){
_start:
{
lean_object* v_toByteArray_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_toByteArray_38_ = lean_string_to_utf8(v_x_35_);
v___x_39_ = lean_box_uint32(v_x_36_);
v___x_40_ = lean_apply_3(v_h__1_37_, v_toByteArray_38_, lean_box(0), v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___boxed(lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_h__1_44_){
_start:
{
uint32_t v_x_30__boxed_45_; lean_object* v_res_46_; 
v_x_30__boxed_45_ = lean_unbox_uint32(v_x_43_);
lean_dec(v_x_43_);
v_res_46_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(v_motive_41_, v_x_42_, v_x_30__boxed_45_, v_h__1_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg(){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_unsigned_to_nat(0u);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg___boxed(lean_object* v___dummy_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_String_rawStartPos___redArg();
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_unsigned_to_nat(0u);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_String_rawStartPos(v___s_53_);
lean_dec_ref(v___s_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t v_c_55_, lean_object* v_s_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_string_push(v_s_56_, v_c_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_58_, lean_object* v_s_59_){
_start:
{
uint32_t v_c_boxed_60_; lean_object* v_res_61_; 
v_c_boxed_60_ = lean_unbox_uint32(v_c_58_);
lean_dec(v_c_58_);
v_res_61_ = l_String_pushn___lam__0(v_c_boxed_60_, v_s_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* v_s_62_, uint32_t v_c_63_, lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___f_66_; lean_object* v___x_67_; 
v___x_65_ = lean_box_uint32(v_c_63_);
v___f_66_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_66_, 0, v___x_65_);
v___x_67_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_66_, v_n_64_, v_s_62_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_68_, lean_object* v_c_69_, lean_object* v_n_70_){
_start:
{
uint32_t v_c_boxed_71_; lean_object* v_res_72_; 
v_c_boxed_71_ = lean_unbox_uint32(v_c_69_);
lean_dec(v_c_69_);
v_res_72_ = l_String_pushn(v_s_68_, v_c_boxed_71_, v_n_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_zero_76_; uint8_t v_isZero_77_; 
v_zero_76_ = lean_unsigned_to_nat(0u);
v_isZero_77_ = lean_nat_dec_eq(v_x_74_, v_zero_76_);
if (v_isZero_77_ == 1)
{
lean_dec(v_x_74_);
return v_x_75_;
}
else
{
lean_object* v_one_78_; lean_object* v_n_79_; lean_object* v___x_80_; 
v_one_78_ = lean_unsigned_to_nat(1u);
v_n_79_ = lean_nat_sub(v_x_74_, v_one_78_);
lean_dec(v_x_74_);
v___x_80_ = lean_string_push(v_x_75_, v_c_73_);
v_x_74_ = v_n_79_;
v_x_75_ = v___x_80_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_82_, lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
uint32_t v_c_boxed_85_; lean_object* v_res_86_; 
v_c_boxed_85_ = lean_unbox_uint32(v_c_82_);
lean_dec(v_c_82_);
v_res_86_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_85_, v_x_83_, v_x_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* v_s_87_, uint32_t v_c_88_, lean_object* v_n_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_88_, v_n_89_, v_s_87_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_91_, lean_object* v_c_92_, lean_object* v_n_93_){
_start:
{
uint32_t v_c_boxed_94_; lean_object* v_res_95_; 
v_c_boxed_94_ = lean_unbox_uint32(v_c_92_);
lean_dec(v_c_92_);
v_res_95_ = lean_string_pushn(v_s_91_, v_c_boxed_94_, v_n_93_);
return v_res_95_;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* v_s_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_97_ = lean_string_utf8_byte_size(v_s_96_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_String_isEmpty(v_s_100_);
lean_dec_ref(v_s_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* v_s_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = lean_string_utf8_byte_size(v_s_103_);
lean_dec_ref(v_s_103_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = lean_string_isempty(v_s_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_111_){
_start:
{
lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___f_112_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_113_ = ((lean_object*)(l_String_join___closed__0));
v___x_114_ = l_List_foldl___redArg(v___f_112_, v___x_113_, v_l_111_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_115_, lean_object* v_s_116_, lean_object* v_a_117_){
_start:
{
if (lean_obj_tag(v_a_117_) == 0)
{
return v_acc_115_;
}
else
{
lean_object* v_head_118_; lean_object* v_tail_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_head_118_ = lean_ctor_get(v_a_117_, 0);
v_tail_119_ = lean_ctor_get(v_a_117_, 1);
v___x_120_ = lean_string_append(v_acc_115_, v_s_116_);
v___x_121_ = lean_string_append(v___x_120_, v_head_118_);
v_acc_115_ = v___x_121_;
v_a_117_ = v_tail_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_123_, lean_object* v_s_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_123_, v_s_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_s_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_String_join___closed__0));
return v___x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_132_; 
v_head_130_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_130_);
v_tail_131_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_tail_131_);
lean_dec_ref_known(v_x_128_, 2);
v___x_132_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_130_, v_s_127_, v_tail_131_);
lean_dec(v_tail_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_133_, lean_object* v_x_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_String_intercalate(v_s_133_, v_x_134_);
lean_dec_ref(v_s_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_String_intercalate(v_s_136_, v_a_137_);
lean_dec_ref(v_s_136_);
return v___x_138_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
uint8_t v_decide_141_; 
v_decide_141_ = lean_nat_dec_eq(v_x_139_, v_x_140_);
return v_decide_141_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_String_instDecidableEqPos_decEq___redArg(v_x_142_, v_x_143_);
lean_dec(v_x_143_);
lean_dec(v_x_142_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_decide_149_; 
v_decide_149_ = lean_nat_dec_eq(v_x_147_, v_x_148_);
return v_decide_149_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_String_instDecidableEqPos_decEq(v_s_150_, v_x_151_, v_x_152_);
lean_dec(v_x_152_);
lean_dec(v_x_151_);
lean_dec_ref(v_s_150_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
uint8_t v_decide_157_; 
v_decide_157_ = lean_nat_dec_eq(v_x_155_, v_x_156_);
return v_decide_157_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_String_instDecidableEqPos___redArg(v_x_158_, v_x_159_);
lean_dec(v_x_159_);
lean_dec(v_x_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* v_s_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
uint8_t v_decide_165_; 
v_decide_165_ = lean_nat_dec_eq(v_x_163_, v_x_164_);
return v_decide_165_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_String_instDecidableEqPos(v_s_166_, v_x_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec(v_x_167_);
lean_dec_ref(v_s_166_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___redArg(){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_unsigned_to_nat(0u);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___redArg___boxed(lean_object* v___dummy_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_String_startPos___redArg();
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* v_s_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(0u);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* v_s_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_String_startPos(v_s_177_);
lean_dec_ref(v_s_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg(){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(0u);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg___boxed(lean_object* v___dummy_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_String_instInhabitedPos___redArg();
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_unsigned_to_nat(0u);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_String_instInhabitedPos(v_s_185_);
lean_dec_ref(v_s_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_string_utf8_byte_size(v_s_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_String_endPos(v_s_189_);
lean_dec_ref(v_s_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___redArg(){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___redArg___boxed(lean_object* v___dummy_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_String_instLEPos___redArg();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* v_s_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* v_s_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_String_instLEPos(v_s_197_);
lean_dec_ref(v_s_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___redArg(){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___redArg___boxed(lean_object* v___dummy_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_String_instLTPos___redArg();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_String_instLTPos(v_s_205_);
lean_dec_ref(v_s_205_);
return v_res_206_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_207_, lean_object* v_r_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_le(v_l_207_, v_r_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_210_, lean_object* v_r_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_String_instDecidableLePos___redArg(v_l_210_, v_r_211_);
lean_dec(v_r_211_);
lean_dec(v_l_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* v_s_214_, lean_object* v_l_215_, lean_object* v_r_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_le(v_l_215_, v_r_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_218_, lean_object* v_l_219_, lean_object* v_r_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_String_instDecidableLePos(v_s_218_, v_l_219_, v_r_220_);
lean_dec(v_r_220_);
lean_dec(v_l_219_);
lean_dec_ref(v_s_218_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_223_, lean_object* v_r_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_l_223_, v___x_225_);
v___x_227_ = lean_nat_dec_le(v___x_226_, v_r_224_);
lean_dec(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_228_, lean_object* v_r_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_String_instDecidableLtPos___redArg(v_l_228_, v_r_229_);
lean_dec(v_r_229_);
lean_dec(v_l_228_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* v_s_232_, lean_object* v_l_233_, lean_object* v_r_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = l_String_instDecidableLtPos___redArg(v_l_233_, v_r_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_236_, lean_object* v_l_237_, lean_object* v_r_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_String_instDecidableLtPos(v_s_236_, v_l_237_, v_r_238_);
lean_dec(v_r_238_);
lean_dec(v_l_237_);
lean_dec_ref(v_s_236_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_string_utf8_byte_size(v_s_245_);
v___x_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_248_, 0, v_s_245_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_251_){
_start:
{
lean_object* v_startInclusive_252_; lean_object* v_endExclusive_253_; lean_object* v___x_254_; 
v_startInclusive_252_ = lean_ctor_get(v_s_251_, 1);
v_endExclusive_253_ = lean_ctor_get(v_s_251_, 2);
v___x_254_ = lean_nat_sub(v_endExclusive_253_, v_startInclusive_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_String_Slice_utf8ByteSize(v_s_255_);
lean_dec_ref(v_s_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_startInclusive_259_; lean_object* v_endExclusive_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_startInclusive_259_ = lean_ctor_get(v_s_258_, 1);
v_endExclusive_260_ = lean_ctor_get(v_s_258_, 2);
v___x_261_ = lean_nat_sub(v_endExclusive_260_, v_startInclusive_259_);
v___x_262_ = lean_nat_add(v_p_257_, v___x_261_);
lean_dec(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_263_, lean_object* v_s_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_String_instHAddRawSlice___lam__0(v_p_263_, v_s_264_);
lean_dec_ref(v_s_264_);
lean_dec(v_p_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_268_, lean_object* v_p_269_){
_start:
{
lean_object* v_startInclusive_270_; lean_object* v_endExclusive_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_startInclusive_270_ = lean_ctor_get(v_s_268_, 1);
v_endExclusive_271_ = lean_ctor_get(v_s_268_, 2);
v___x_272_ = lean_nat_sub(v_endExclusive_271_, v_startInclusive_270_);
v___x_273_ = lean_nat_add(v___x_272_, v_p_269_);
lean_dec(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_274_, lean_object* v_p_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_String_instHAddSliceRaw___lam__0(v_s_274_, v_p_275_);
lean_dec(v_p_275_);
lean_dec_ref(v_s_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_279_, lean_object* v_s_280_){
_start:
{
lean_object* v_startInclusive_281_; lean_object* v_endExclusive_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_startInclusive_281_ = lean_ctor_get(v_s_280_, 1);
v_endExclusive_282_ = lean_ctor_get(v_s_280_, 2);
v___x_283_ = lean_nat_sub(v_endExclusive_282_, v_startInclusive_281_);
v___x_284_ = lean_nat_sub(v_p_279_, v___x_283_);
lean_dec(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_285_, lean_object* v_s_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_String_instHSubRawSlice___lam__0(v_p_285_, v_s_286_);
lean_dec_ref(v_s_286_);
lean_dec(v_p_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_290_){
_start:
{
lean_object* v_startInclusive_291_; lean_object* v_endExclusive_292_; lean_object* v___x_293_; 
v_startInclusive_291_ = lean_ctor_get(v_s_290_, 1);
v_endExclusive_292_ = lean_ctor_get(v_s_290_, 2);
v___x_293_ = lean_nat_sub(v_endExclusive_292_, v_startInclusive_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_String_Slice_rawEndPos(v_s_294_);
lean_dec_ref(v_s_294_);
return v_res_295_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_296_, lean_object* v_p_297_){
_start:
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_str_298_ = lean_ctor_get(v_s_296_, 0);
v_startInclusive_299_ = lean_ctor_get(v_s_296_, 1);
v___x_300_ = lean_nat_add(v_startInclusive_299_, v_p_297_);
v___x_301_ = lean_string_get_byte_fast(v_str_298_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* v_s_302_, lean_object* v_p_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_String_Slice_getUTF8Byte___redArg(v_s_302_, v_p_303_);
lean_dec(v_p_303_);
lean_dec_ref(v_s_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_306_, lean_object* v_p_307_, lean_object* v_h_308_){
_start:
{
lean_object* v_str_309_; lean_object* v_startInclusive_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_str_309_ = lean_ctor_get(v_s_306_, 0);
v_startInclusive_310_ = lean_ctor_get(v_s_306_, 1);
v___x_311_ = lean_nat_add(v_startInclusive_310_, v_p_307_);
v___x_312_ = lean_string_get_byte_fast(v_str_309_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_313_, lean_object* v_p_314_, lean_object* v_h_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_String_Slice_getUTF8Byte(v_s_313_, v_p_314_, v_h_315_);
lean_dec(v_p_314_);
lean_dec_ref(v_s_313_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_318_){
_start:
{
uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_319_ = 0;
v___x_320_ = lean_box(v___x_319_);
v___x_321_ = lean_panic_fn_borrowed(v___x_320_, v_msg_318_);
lean_dec(v___x_320_);
v___x_322_ = lean_unbox(v___x_321_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_323_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_330_ = lean_unsigned_to_nat(4u);
v___x_331_ = lean_unsigned_to_nat(539u);
v___x_332_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_333_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_334_ = l_mkPanicMessageWithDecl(v___x_333_, v___x_332_, v___x_331_, v___x_330_, v___x_329_);
return v___x_334_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_335_, lean_object* v_p_336_){
_start:
{
lean_object* v_str_337_; lean_object* v_startInclusive_338_; lean_object* v_endExclusive_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_str_337_ = lean_ctor_get(v_s_335_, 0);
v_startInclusive_338_ = lean_ctor_get(v_s_335_, 1);
v_endExclusive_339_ = lean_ctor_get(v_s_335_, 2);
v___x_340_ = lean_nat_sub(v_endExclusive_339_, v_startInclusive_338_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v_p_336_, v___x_341_);
v___x_343_ = lean_nat_dec_le(v___x_342_, v___x_340_);
lean_dec(v___x_340_);
lean_dec(v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_345_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_344_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_nat_add(v_startInclusive_338_, v_p_336_);
v___x_347_ = lean_string_get_byte_fast(v_str_337_, v___x_346_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_348_, lean_object* v_p_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_String_Slice_getUTF8Byte_x21(v_s_348_, v_p_349_);
lean_dec(v_p_349_);
lean_dec_ref(v_s_348_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
uint8_t v_decide_354_; 
v_decide_354_ = lean_nat_dec_eq(v_x_352_, v_x_353_);
return v_decide_354_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_355_, v_x_356_);
lean_dec(v_x_356_);
lean_dec(v_x_355_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_decide_362_; 
v_decide_362_ = lean_nat_dec_eq(v_x_360_, v_x_361_);
return v_decide_362_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_String_Slice_instDecidableEqPos_decEq(v_s_363_, v_x_364_, v_x_365_);
lean_dec(v_x_365_);
lean_dec(v_x_364_);
lean_dec_ref(v_s_363_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
uint8_t v_decide_370_; 
v_decide_370_ = lean_nat_dec_eq(v_x_368_, v_x_369_);
return v_decide_370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_String_Slice_instDecidableEqPos___redArg(v_x_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec(v_x_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_decide_378_; 
v_decide_378_ = lean_nat_dec_eq(v_x_376_, v_x_377_);
return v_decide_378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_String_Slice_instDecidableEqPos(v_s_379_, v_x_380_, v_x_381_);
lean_dec(v_x_381_);
lean_dec(v_x_380_);
lean_dec_ref(v_s_379_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg(){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(0u);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg___boxed(lean_object* v___dummy_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_String_Slice_startPos___redArg();
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_unsigned_to_nat(0u);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_String_Slice_startPos(v_s_390_);
lean_dec_ref(v_s_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg(){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_unsigned_to_nat(0u);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg___boxed(lean_object* v___dummy_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_String_instInhabitedPos__1___redArg();
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = lean_unsigned_to_nat(0u);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_String_instInhabitedPos__1(v_s_398_);
lean_dec_ref(v_s_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_400_){
_start:
{
lean_object* v_startInclusive_401_; lean_object* v_endExclusive_402_; lean_object* v___x_403_; 
v_startInclusive_401_ = lean_ctor_get(v_s_400_, 1);
v_endExclusive_402_ = lean_ctor_get(v_s_400_, 2);
v___x_403_ = lean_nat_sub(v_endExclusive_402_, v_startInclusive_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_String_Slice_endPos(v_s_404_);
lean_dec_ref(v_s_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg(){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg___boxed(lean_object* v___dummy_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_String_instLEPos__1___redArg();
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_String_instLEPos__1(v_s_412_);
lean_dec_ref(v_s_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg(){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg___boxed(lean_object* v___dummy_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_String_instLTPos__1___redArg();
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lean_box(0);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_String_instLTPos__1(v_s_420_);
lean_dec_ref(v_s_420_);
return v_res_421_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_422_, lean_object* v_r_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_le(v_l_422_, v_r_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_425_, lean_object* v_r_426_){
_start:
{
uint8_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l_String_instDecidableLePos__1___redArg(v_l_425_, v_r_426_);
lean_dec(v_r_426_);
lean_dec(v_l_425_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_429_, lean_object* v_l_430_, lean_object* v_r_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_le(v_l_430_, v_r_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_433_, lean_object* v_l_434_, lean_object* v_r_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_String_instDecidableLePos__1(v_s_433_, v_l_434_, v_r_435_);
lean_dec(v_r_435_);
lean_dec(v_l_434_);
lean_dec_ref(v_s_433_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_438_, lean_object* v_r_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_l_438_, v___x_440_);
v___x_442_ = lean_nat_dec_le(v___x_441_, v_r_439_);
lean_dec(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_443_, lean_object* v_r_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_String_instDecidableLtPos__1___redArg(v_l_443_, v_r_444_);
lean_dec(v_r_444_);
lean_dec(v_l_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_447_, lean_object* v_l_448_, lean_object* v_r_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = l_String_instDecidableLtPos__1___redArg(v_l_448_, v_r_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_451_, lean_object* v_l_452_, lean_object* v_r_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_String_instDecidableLtPos__1(v_s_451_, v_l_452_, v_r_453_);
lean_dec(v_r_453_);
lean_dec(v_l_452_);
lean_dec_ref(v_s_451_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_456_, lean_object* v_pos_457_){
_start:
{
lean_object* v___x_458_; uint8_t v_decide_459_; 
v___x_458_ = lean_string_utf8_byte_size(v_s_456_);
v_decide_459_ = lean_nat_dec_eq(v_pos_457_, v___x_458_);
return v_decide_459_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_460_, lean_object* v_pos_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_String_instDecidableIsAtEnd(v_s_460_, v_pos_461_);
lean_dec(v_pos_461_);
lean_dec_ref(v_s_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_464_, lean_object* v_pos_465_){
_start:
{
lean_object* v_startInclusive_466_; lean_object* v_endExclusive_467_; lean_object* v___x_468_; uint8_t v_decide_469_; 
v_startInclusive_466_ = lean_ctor_get(v_s_464_, 1);
v_endExclusive_467_ = lean_ctor_get(v_s_464_, 2);
v___x_468_ = lean_nat_sub(v_endExclusive_467_, v_startInclusive_466_);
v_decide_469_ = lean_nat_dec_eq(v_pos_465_, v___x_468_);
lean_dec(v___x_468_);
return v_decide_469_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_470_, lean_object* v_pos_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_String_instDecidableIsAtEnd__1(v_s_470_, v_pos_471_);
lean_dec(v_pos_471_);
lean_dec_ref(v_s_470_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_474_, lean_object* v_pos_475_){
_start:
{
lean_object* v_str_476_; lean_object* v_startInclusive_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_str_476_ = lean_ctor_get(v_s_474_, 0);
v_startInclusive_477_ = lean_ctor_get(v_s_474_, 1);
v___x_478_ = lean_nat_add(v_startInclusive_477_, v_pos_475_);
v___x_479_ = lean_string_get_byte_fast(v_str_476_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_480_, lean_object* v_pos_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_String_Slice_Pos_byte___redArg(v_s_480_, v_pos_481_);
lean_dec(v_pos_481_);
lean_dec_ref(v_s_480_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_484_, lean_object* v_pos_485_, lean_object* v_h_486_){
_start:
{
lean_object* v_str_487_; lean_object* v_startInclusive_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_str_487_ = lean_ctor_get(v_s_484_, 0);
v_startInclusive_488_ = lean_ctor_get(v_s_484_, 1);
v___x_489_ = lean_nat_add(v_startInclusive_488_, v_pos_485_);
v___x_490_ = lean_string_get_byte_fast(v_str_487_, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_491_, lean_object* v_pos_492_, lean_object* v_h_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_String_Slice_Pos_byte(v_s_491_, v_pos_492_, v_h_493_);
lean_dec(v_pos_492_);
lean_dec_ref(v_s_491_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_496_){
_start:
{
lean_object* v_startInclusive_497_; lean_object* v_endExclusive_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_startInclusive_497_ = lean_ctor_get(v_s_496_, 1);
v_endExclusive_498_ = lean_ctor_get(v_s_496_, 2);
v___x_499_ = lean_nat_sub(v_endExclusive_498_, v_startInclusive_497_);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
lean_dec(v___x_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_String_Slice_isEmpty(v_s_502_);
lean_dec_ref(v_s_502_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_string_utf8_byte_size(v_s_505_);
v___x_508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_508_, 0, v_s_505_);
lean_ctor_set(v___x_508_, 1, v___x_506_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_String_toRawSubstring_x27(v_s_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___redArg(){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_unsigned_to_nat(0u);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___redArg___boxed(lean_object* v___dummy_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_String_startValidPos___redArg();
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_unsigned_to_nat(0u);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_String_startValidPos(v_s_517_);
lean_dec_ref(v_s_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_string_utf8_byte_size(v_s_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_String_endValidPos(v_s_521_);
lean_dec_ref(v_s_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_String_bytes(lean_object* v_s_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_string_to_utf8(v_s_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii(lean_object* v_s_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_string_utf8_byte_size(v_s_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii___boxed(lean_object* v_s_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_String_lengthAssumingAscii(v_s_527_);
lean_dec_ref(v_s_527_);
return v_res_528_;
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
