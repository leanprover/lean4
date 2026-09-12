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
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg(){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_unsigned_to_nat(0u);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg___boxed(lean_object* v___dummy_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_String_rawStartPos___redArg();
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_unsigned_to_nat(0u);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_String_rawStartPos(v___s_59_);
lean_dec_ref(v___s_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t v_c_61_, lean_object* v_s_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_string_push(v_s_62_, v_c_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_64_, lean_object* v_s_65_){
_start:
{
uint32_t v_c_boxed_66_; lean_object* v_res_67_; 
v_c_boxed_66_ = lean_unbox_uint32(v_c_64_);
lean_dec(v_c_64_);
v_res_67_ = l_String_pushn___lam__0(v_c_boxed_66_, v_s_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* v_s_68_, uint32_t v_c_69_, lean_object* v_n_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
v___x_71_ = lean_box_uint32(v_c_69_);
v___f_72_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_72_, 0, v___x_71_);
v___x_73_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_72_, v_n_70_, v_s_68_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_74_, lean_object* v_c_75_, lean_object* v_n_76_){
_start:
{
uint32_t v_c_boxed_77_; lean_object* v_res_78_; 
v_c_boxed_77_ = lean_unbox_uint32(v_c_75_);
lean_dec(v_c_75_);
v_res_78_ = l_String_pushn(v_s_74_, v_c_boxed_77_, v_n_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_79_, lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_zero_82_; uint8_t v_isZero_83_; 
v_zero_82_ = lean_unsigned_to_nat(0u);
v_isZero_83_ = lean_nat_dec_eq(v_x_80_, v_zero_82_);
if (v_isZero_83_ == 1)
{
lean_dec(v_x_80_);
return v_x_81_;
}
else
{
lean_object* v_one_84_; lean_object* v_n_85_; lean_object* v___x_86_; 
v_one_84_ = lean_unsigned_to_nat(1u);
v_n_85_ = lean_nat_sub(v_x_80_, v_one_84_);
lean_dec(v_x_80_);
v___x_86_ = lean_string_push(v_x_81_, v_c_79_);
v_x_80_ = v_n_85_;
v_x_81_ = v___x_86_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
uint32_t v_c_boxed_91_; lean_object* v_res_92_; 
v_c_boxed_91_ = lean_unbox_uint32(v_c_88_);
lean_dec(v_c_88_);
v_res_92_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_91_, v_x_89_, v_x_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* v_s_93_, uint32_t v_c_94_, lean_object* v_n_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_94_, v_n_95_, v_s_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_97_, lean_object* v_c_98_, lean_object* v_n_99_){
_start:
{
uint32_t v_c_boxed_100_; lean_object* v_res_101_; 
v_c_boxed_100_ = lean_unbox_uint32(v_c_98_);
lean_dec(v_c_98_);
v_res_101_ = lean_string_pushn(v_s_97_, v_c_boxed_100_, v_n_99_);
return v_res_101_;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* v_s_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = lean_string_utf8_byte_size(v_s_102_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_String_isEmpty(v_s_106_);
lean_dec_ref(v_s_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* v_s_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = lean_string_utf8_byte_size(v_s_109_);
lean_dec_ref(v_s_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_nat_dec_eq(v___x_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = lean_string_isempty(v_s_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_117_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___f_118_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_119_ = ((lean_object*)(l_String_join___closed__0));
v___x_120_ = l_List_foldl___redArg(v___f_118_, v___x_119_, v_l_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_121_, lean_object* v_s_122_, lean_object* v_a_123_){
_start:
{
if (lean_obj_tag(v_a_123_) == 0)
{
return v_acc_121_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_head_124_ = lean_ctor_get(v_a_123_, 0);
v_tail_125_ = lean_ctor_get(v_a_123_, 1);
v___x_126_ = lean_string_append(v_acc_121_, v_s_122_);
v___x_127_ = lean_string_append(v___x_126_, v_head_124_);
v_acc_121_ = v___x_127_;
v_a_123_ = v_tail_125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_129_, lean_object* v_s_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_129_, v_s_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_s_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_135_; 
v___x_135_ = ((lean_object*)(l_String_join___closed__0));
return v___x_135_;
}
else
{
lean_object* v_head_136_; lean_object* v_tail_137_; lean_object* v___x_138_; 
v_head_136_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_head_136_);
v_tail_137_ = lean_ctor_get(v_x_134_, 1);
lean_inc(v_tail_137_);
lean_dec_ref_known(v_x_134_, 2);
v___x_138_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_136_, v_s_133_, v_tail_137_);
lean_dec(v_tail_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_String_intercalate(v_s_139_, v_x_140_);
lean_dec_ref(v_s_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_String_intercalate(v_s_142_, v_a_143_);
lean_dec_ref(v_s_142_);
return v___x_144_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_decide_147_; 
v_decide_147_ = lean_nat_dec_eq(v_x_145_, v_x_146_);
return v_decide_147_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_String_instDecidableEqPos_decEq___redArg(v_x_148_, v_x_149_);
lean_dec(v_x_149_);
lean_dec(v_x_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
uint8_t v_decide_155_; 
v_decide_155_ = lean_nat_dec_eq(v_x_153_, v_x_154_);
return v_decide_155_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_String_instDecidableEqPos_decEq(v_s_156_, v_x_157_, v_x_158_);
lean_dec(v_x_158_);
lean_dec(v_x_157_);
lean_dec_ref(v_s_156_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
uint8_t v_decide_163_; 
v_decide_163_ = lean_nat_dec_eq(v_x_161_, v_x_162_);
return v_decide_163_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_String_instDecidableEqPos___redArg(v_x_164_, v_x_165_);
lean_dec(v_x_165_);
lean_dec(v_x_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* v_s_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_decide_171_; 
v_decide_171_ = lean_nat_dec_eq(v_x_169_, v_x_170_);
return v_decide_171_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_172_, lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_String_instDecidableEqPos(v_s_172_, v_x_173_, v_x_174_);
lean_dec(v_x_174_);
lean_dec(v_x_173_);
lean_dec_ref(v_s_172_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___redArg(){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(0u);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___redArg___boxed(lean_object* v___dummy_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_String_startPos___redArg();
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* v_s_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(0u);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* v_s_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_String_startPos(v_s_183_);
lean_dec_ref(v_s_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg(){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(0u);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg___boxed(lean_object* v___dummy_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_String_instInhabitedPos___redArg();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(0u);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_String_instInhabitedPos(v_s_191_);
lean_dec_ref(v_s_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_string_utf8_byte_size(v_s_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_String_endPos(v_s_195_);
lean_dec_ref(v_s_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___redArg(){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___redArg___boxed(lean_object* v___dummy_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_String_instLEPos___redArg();
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* v_s_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* v_s_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_String_instLEPos(v_s_203_);
lean_dec_ref(v_s_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___redArg(){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___redArg___boxed(lean_object* v___dummy_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_String_instLTPos___redArg();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_String_instLTPos(v_s_211_);
lean_dec_ref(v_s_211_);
return v_res_212_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_213_, lean_object* v_r_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = lean_nat_dec_le(v_l_213_, v_r_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_216_, lean_object* v_r_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_String_instDecidableLePos___redArg(v_l_216_, v_r_217_);
lean_dec(v_r_217_);
lean_dec(v_l_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* v_s_220_, lean_object* v_l_221_, lean_object* v_r_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = lean_nat_dec_le(v_l_221_, v_r_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_224_, lean_object* v_l_225_, lean_object* v_r_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_String_instDecidableLePos(v_s_224_, v_l_225_, v_r_226_);
lean_dec(v_r_226_);
lean_dec(v_l_225_);
lean_dec_ref(v_s_224_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_229_, lean_object* v_r_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_l_229_, v___x_231_);
v___x_233_ = lean_nat_dec_le(v___x_232_, v_r_230_);
lean_dec(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_234_, lean_object* v_r_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_String_instDecidableLtPos___redArg(v_l_234_, v_r_235_);
lean_dec(v_r_235_);
lean_dec(v_l_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* v_s_238_, lean_object* v_l_239_, lean_object* v_r_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_String_instDecidableLtPos___redArg(v_l_239_, v_r_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_242_, lean_object* v_l_243_, lean_object* v_r_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_String_instDecidableLtPos(v_s_242_, v_l_243_, v_r_244_);
lean_dec(v_r_244_);
lean_dec(v_l_243_);
lean_dec_ref(v_s_242_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_string_utf8_byte_size(v_s_251_);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v_s_251_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_257_){
_start:
{
lean_object* v_startInclusive_258_; lean_object* v_endExclusive_259_; lean_object* v___x_260_; 
v_startInclusive_258_ = lean_ctor_get(v_s_257_, 1);
v_endExclusive_259_ = lean_ctor_get(v_s_257_, 2);
v___x_260_ = lean_nat_sub(v_endExclusive_259_, v_startInclusive_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_String_Slice_utf8ByteSize(v_s_261_);
lean_dec_ref(v_s_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_263_, lean_object* v_s_264_){
_start:
{
lean_object* v_startInclusive_265_; lean_object* v_endExclusive_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_startInclusive_265_ = lean_ctor_get(v_s_264_, 1);
v_endExclusive_266_ = lean_ctor_get(v_s_264_, 2);
v___x_267_ = lean_nat_sub(v_endExclusive_266_, v_startInclusive_265_);
v___x_268_ = lean_nat_add(v_p_263_, v___x_267_);
lean_dec(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_269_, lean_object* v_s_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_String_instHAddRawSlice___lam__0(v_p_269_, v_s_270_);
lean_dec_ref(v_s_270_);
lean_dec(v_p_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_274_, lean_object* v_p_275_){
_start:
{
lean_object* v_startInclusive_276_; lean_object* v_endExclusive_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_startInclusive_276_ = lean_ctor_get(v_s_274_, 1);
v_endExclusive_277_ = lean_ctor_get(v_s_274_, 2);
v___x_278_ = lean_nat_sub(v_endExclusive_277_, v_startInclusive_276_);
v___x_279_ = lean_nat_add(v___x_278_, v_p_275_);
lean_dec(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_280_, lean_object* v_p_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_String_instHAddSliceRaw___lam__0(v_s_280_, v_p_281_);
lean_dec(v_p_281_);
lean_dec_ref(v_s_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_285_, lean_object* v_s_286_){
_start:
{
lean_object* v_startInclusive_287_; lean_object* v_endExclusive_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_startInclusive_287_ = lean_ctor_get(v_s_286_, 1);
v_endExclusive_288_ = lean_ctor_get(v_s_286_, 2);
v___x_289_ = lean_nat_sub(v_endExclusive_288_, v_startInclusive_287_);
v___x_290_ = lean_nat_sub(v_p_285_, v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_291_, lean_object* v_s_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_String_instHSubRawSlice___lam__0(v_p_291_, v_s_292_);
lean_dec_ref(v_s_292_);
lean_dec(v_p_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_296_){
_start:
{
lean_object* v_startInclusive_297_; lean_object* v_endExclusive_298_; lean_object* v___x_299_; 
v_startInclusive_297_ = lean_ctor_get(v_s_296_, 1);
v_endExclusive_298_ = lean_ctor_get(v_s_296_, 2);
v___x_299_ = lean_nat_sub(v_endExclusive_298_, v_startInclusive_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_String_Slice_rawEndPos(v_s_300_);
lean_dec_ref(v_s_300_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_302_, lean_object* v_p_303_){
_start:
{
lean_object* v_str_304_; lean_object* v_startInclusive_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_str_304_ = lean_ctor_get(v_s_302_, 0);
v_startInclusive_305_ = lean_ctor_get(v_s_302_, 1);
v___x_306_ = lean_nat_add(v_startInclusive_305_, v_p_303_);
v___x_307_ = lean_string_get_byte_fast(v_str_304_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* v_s_308_, lean_object* v_p_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_String_Slice_getUTF8Byte___redArg(v_s_308_, v_p_309_);
lean_dec(v_p_309_);
lean_dec_ref(v_s_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_312_, lean_object* v_p_313_, lean_object* v_h_314_){
_start:
{
lean_object* v_str_315_; lean_object* v_startInclusive_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_str_315_ = lean_ctor_get(v_s_312_, 0);
v_startInclusive_316_ = lean_ctor_get(v_s_312_, 1);
v___x_317_ = lean_nat_add(v_startInclusive_316_, v_p_313_);
v___x_318_ = lean_string_get_byte_fast(v_str_315_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_319_, lean_object* v_p_320_, lean_object* v_h_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_String_Slice_getUTF8Byte(v_s_319_, v_p_320_, v_h_321_);
lean_dec(v_p_320_);
lean_dec_ref(v_s_319_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_324_){
_start:
{
uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_325_ = 0;
v___x_326_ = lean_box(v___x_325_);
v___x_327_ = lean_panic_fn_borrowed(v___x_326_, v_msg_324_);
lean_dec(v___x_326_);
v___x_328_ = lean_unbox(v___x_327_);
lean_dec(v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_335_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_336_ = lean_unsigned_to_nat(4u);
v___x_337_ = lean_unsigned_to_nat(536u);
v___x_338_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_339_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_340_ = l_mkPanicMessageWithDecl(v___x_339_, v___x_338_, v___x_337_, v___x_336_, v___x_335_);
return v___x_340_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_341_, lean_object* v_p_342_){
_start:
{
lean_object* v_str_343_; lean_object* v_startInclusive_344_; lean_object* v_endExclusive_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_str_343_ = lean_ctor_get(v_s_341_, 0);
v_startInclusive_344_ = lean_ctor_get(v_s_341_, 1);
v_endExclusive_345_ = lean_ctor_get(v_s_341_, 2);
v___x_346_ = lean_nat_sub(v_endExclusive_345_, v_startInclusive_344_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_p_342_, v___x_347_);
v___x_349_ = lean_nat_dec_le(v___x_348_, v___x_346_);
lean_dec(v___x_346_);
lean_dec(v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_351_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_350_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_nat_add(v_startInclusive_344_, v_p_342_);
v___x_353_ = lean_string_get_byte_fast(v_str_343_, v___x_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_354_, lean_object* v_p_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_String_Slice_getUTF8Byte_x21(v_s_354_, v_p_355_);
lean_dec(v_p_355_);
lean_dec_ref(v_s_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
uint8_t v_decide_360_; 
v_decide_360_ = lean_nat_dec_eq(v_x_358_, v_x_359_);
return v_decide_360_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_361_, v_x_362_);
lean_dec(v_x_362_);
lean_dec(v_x_361_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_decide_368_; 
v_decide_368_ = lean_nat_dec_eq(v_x_366_, v_x_367_);
return v_decide_368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_String_Slice_instDecidableEqPos_decEq(v_s_369_, v_x_370_, v_x_371_);
lean_dec(v_x_371_);
lean_dec(v_x_370_);
lean_dec_ref(v_s_369_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
uint8_t v_decide_376_; 
v_decide_376_ = lean_nat_dec_eq(v_x_374_, v_x_375_);
return v_decide_376_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_String_Slice_instDecidableEqPos___redArg(v_x_377_, v_x_378_);
lean_dec(v_x_378_);
lean_dec(v_x_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
uint8_t v_decide_384_; 
v_decide_384_ = lean_nat_dec_eq(v_x_382_, v_x_383_);
return v_decide_384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_String_Slice_instDecidableEqPos(v_s_385_, v_x_386_, v_x_387_);
lean_dec(v_x_387_);
lean_dec(v_x_386_);
lean_dec_ref(v_s_385_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg(){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(0u);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg___boxed(lean_object* v___dummy_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_String_Slice_startPos___redArg();
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_unsigned_to_nat(0u);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_String_Slice_startPos(v_s_396_);
lean_dec_ref(v_s_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg(){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_unsigned_to_nat(0u);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg___boxed(lean_object* v___dummy_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_String_instInhabitedPos__1___redArg();
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_unsigned_to_nat(0u);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_String_instInhabitedPos__1(v_s_404_);
lean_dec_ref(v_s_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_406_){
_start:
{
lean_object* v_startInclusive_407_; lean_object* v_endExclusive_408_; lean_object* v___x_409_; 
v_startInclusive_407_ = lean_ctor_get(v_s_406_, 1);
v_endExclusive_408_ = lean_ctor_get(v_s_406_, 2);
v___x_409_ = lean_nat_sub(v_endExclusive_408_, v_startInclusive_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_String_Slice_endPos(v_s_410_);
lean_dec_ref(v_s_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg(){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_box(0);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg___boxed(lean_object* v___dummy_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_String_instLEPos__1___redArg();
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_box(0);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_String_instLEPos__1(v_s_418_);
lean_dec_ref(v_s_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg(){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_box(0);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg___boxed(lean_object* v___dummy_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_String_instLTPos__1___redArg();
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = lean_box(0);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_String_instLTPos__1(v_s_426_);
lean_dec_ref(v_s_426_);
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_428_, lean_object* v_r_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_le(v_l_428_, v_r_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_431_, lean_object* v_r_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_String_instDecidableLePos__1___redArg(v_l_431_, v_r_432_);
lean_dec(v_r_432_);
lean_dec(v_l_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_435_, lean_object* v_l_436_, lean_object* v_r_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = lean_nat_dec_le(v_l_436_, v_r_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_439_, lean_object* v_l_440_, lean_object* v_r_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_String_instDecidableLePos__1(v_s_439_, v_l_440_, v_r_441_);
lean_dec(v_r_441_);
lean_dec(v_l_440_);
lean_dec_ref(v_s_439_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_444_, lean_object* v_r_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_l_444_, v___x_446_);
v___x_448_ = lean_nat_dec_le(v___x_447_, v_r_445_);
lean_dec(v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_449_, lean_object* v_r_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_String_instDecidableLtPos__1___redArg(v_l_449_, v_r_450_);
lean_dec(v_r_450_);
lean_dec(v_l_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_453_, lean_object* v_l_454_, lean_object* v_r_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = l_String_instDecidableLtPos__1___redArg(v_l_454_, v_r_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_457_, lean_object* v_l_458_, lean_object* v_r_459_){
_start:
{
uint8_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_String_instDecidableLtPos__1(v_s_457_, v_l_458_, v_r_459_);
lean_dec(v_r_459_);
lean_dec(v_l_458_);
lean_dec_ref(v_s_457_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_462_, lean_object* v_pos_463_){
_start:
{
lean_object* v___x_464_; uint8_t v_decide_465_; 
v___x_464_ = lean_string_utf8_byte_size(v_s_462_);
v_decide_465_ = lean_nat_dec_eq(v_pos_463_, v___x_464_);
return v_decide_465_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_466_, lean_object* v_pos_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_String_instDecidableIsAtEnd(v_s_466_, v_pos_467_);
lean_dec(v_pos_467_);
lean_dec_ref(v_s_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_470_, lean_object* v_pos_471_){
_start:
{
lean_object* v_startInclusive_472_; lean_object* v_endExclusive_473_; lean_object* v___x_474_; uint8_t v_decide_475_; 
v_startInclusive_472_ = lean_ctor_get(v_s_470_, 1);
v_endExclusive_473_ = lean_ctor_get(v_s_470_, 2);
v___x_474_ = lean_nat_sub(v_endExclusive_473_, v_startInclusive_472_);
v_decide_475_ = lean_nat_dec_eq(v_pos_471_, v___x_474_);
lean_dec(v___x_474_);
return v_decide_475_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_476_, lean_object* v_pos_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_String_instDecidableIsAtEnd__1(v_s_476_, v_pos_477_);
lean_dec(v_pos_477_);
lean_dec_ref(v_s_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_480_, lean_object* v_pos_481_){
_start:
{
lean_object* v_str_482_; lean_object* v_startInclusive_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_str_482_ = lean_ctor_get(v_s_480_, 0);
v_startInclusive_483_ = lean_ctor_get(v_s_480_, 1);
v___x_484_ = lean_nat_add(v_startInclusive_483_, v_pos_481_);
v___x_485_ = lean_string_get_byte_fast(v_str_482_, v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_486_, lean_object* v_pos_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_String_Slice_Pos_byte___redArg(v_s_486_, v_pos_487_);
lean_dec(v_pos_487_);
lean_dec_ref(v_s_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_490_, lean_object* v_pos_491_, lean_object* v_h_492_){
_start:
{
lean_object* v_str_493_; lean_object* v_startInclusive_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_str_493_ = lean_ctor_get(v_s_490_, 0);
v_startInclusive_494_ = lean_ctor_get(v_s_490_, 1);
v___x_495_ = lean_nat_add(v_startInclusive_494_, v_pos_491_);
v___x_496_ = lean_string_get_byte_fast(v_str_493_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_497_, lean_object* v_pos_498_, lean_object* v_h_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_String_Slice_Pos_byte(v_s_497_, v_pos_498_, v_h_499_);
lean_dec(v_pos_498_);
lean_dec_ref(v_s_497_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_502_){
_start:
{
lean_object* v_startInclusive_503_; lean_object* v_endExclusive_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_startInclusive_503_ = lean_ctor_get(v_s_502_, 1);
v_endExclusive_504_ = lean_ctor_get(v_s_502_, 2);
v___x_505_ = lean_nat_sub(v_endExclusive_504_, v_startInclusive_503_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_nat_dec_eq(v___x_505_, v___x_506_);
lean_dec(v___x_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_String_Slice_isEmpty(v_s_508_);
lean_dec_ref(v_s_508_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_string_utf8_byte_size(v_s_511_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v_s_511_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_String_toRawSubstring_x27(v_s_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___redArg(){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lean_unsigned_to_nat(0u);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___redArg___boxed(lean_object* v___dummy_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_String_startValidPos___redArg();
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_unsigned_to_nat(0u);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_String_startValidPos(v_s_523_);
lean_dec_ref(v_s_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_string_utf8_byte_size(v_s_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_String_endValidPos(v_s_527_);
lean_dec_ref(v_s_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_String_bytes(lean_object* v_s_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_string_to_utf8(v_s_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii(lean_object* v_s_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_string_utf8_byte_size(v_s_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii___boxed(lean_object* v_s_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_String_lengthAssumingAscii(v_s_533_);
lean_dec_ref(v_s_533_);
return v_res_534_;
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
