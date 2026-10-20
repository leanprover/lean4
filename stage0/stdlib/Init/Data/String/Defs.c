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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
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
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg(){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(0u);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg___boxed(lean_object* v___dummy_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_String_rawStartPos___redArg();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_unsigned_to_nat(0u);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_String_rawStartPos(v___s_29_);
lean_dec_ref(v___s_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t v_c_31_, lean_object* v_s_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_string_push(v_s_32_, v_c_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_34_, lean_object* v_s_35_){
_start:
{
uint32_t v_c_boxed_36_; lean_object* v_res_37_; 
v_c_boxed_36_ = lean_unbox_uint32(v_c_34_);
lean_dec(v_c_34_);
v_res_37_ = l_String_pushn___lam__0(v_c_boxed_36_, v_s_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* v_s_38_, uint32_t v_c_39_, lean_object* v_n_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v___x_41_ = lean_box_uint32(v_c_39_);
v___f_42_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_42_, 0, v___x_41_);
v___x_43_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_42_, v_n_40_, v_s_38_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_44_, lean_object* v_c_45_, lean_object* v_n_46_){
_start:
{
uint32_t v_c_boxed_47_; lean_object* v_res_48_; 
v_c_boxed_47_ = lean_unbox_uint32(v_c_45_);
lean_dec(v_c_45_);
v_res_48_ = l_String_pushn(v_s_44_, v_c_boxed_47_, v_n_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_49_, lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_zero_52_; uint8_t v_isZero_53_; 
v_zero_52_ = lean_unsigned_to_nat(0u);
v_isZero_53_ = lean_nat_dec_eq(v_x_50_, v_zero_52_);
if (v_isZero_53_ == 1)
{
lean_dec(v_x_50_);
return v_x_51_;
}
else
{
lean_object* v_one_54_; lean_object* v_n_55_; lean_object* v___x_56_; 
v_one_54_ = lean_unsigned_to_nat(1u);
v_n_55_ = lean_nat_sub(v_x_50_, v_one_54_);
lean_dec(v_x_50_);
v___x_56_ = lean_string_push(v_x_51_, v_c_49_);
v_x_50_ = v_n_55_;
v_x_51_ = v___x_56_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_58_, lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
uint32_t v_c_boxed_61_; lean_object* v_res_62_; 
v_c_boxed_61_ = lean_unbox_uint32(v_c_58_);
lean_dec(v_c_58_);
v_res_62_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_61_, v_x_59_, v_x_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* v_s_63_, uint32_t v_c_64_, lean_object* v_n_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_64_, v_n_65_, v_s_63_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_67_, lean_object* v_c_68_, lean_object* v_n_69_){
_start:
{
uint32_t v_c_boxed_70_; lean_object* v_res_71_; 
v_c_boxed_70_ = lean_unbox_uint32(v_c_68_);
lean_dec(v_c_68_);
v_res_71_ = lean_string_pushn(v_s_67_, v_c_boxed_70_, v_n_69_);
return v_res_71_;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* v_s_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_string_utf8_byte_size(v_s_72_);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_nat_dec_eq(v___x_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_String_isEmpty(v_s_76_);
lean_dec_ref(v_s_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* v_s_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_string_utf8_byte_size(v_s_79_);
lean_dec_ref(v_s_79_);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_eq(v___x_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = lean_string_isempty(v_s_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_87_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___f_88_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_89_ = ((lean_object*)(l_String_join___closed__0));
v___x_90_ = l_List_foldl___redArg(v___f_88_, v___x_89_, v_l_87_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_91_, lean_object* v_s_92_, lean_object* v_a_93_){
_start:
{
if (lean_obj_tag(v_a_93_) == 0)
{
return v_acc_91_;
}
else
{
lean_object* v_head_94_; lean_object* v_tail_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_head_94_ = lean_ctor_get(v_a_93_, 0);
v_tail_95_ = lean_ctor_get(v_a_93_, 1);
v___x_96_ = lean_string_append(v_acc_91_, v_s_92_);
v___x_97_ = lean_string_append(v___x_96_, v_head_94_);
v_acc_91_ = v___x_97_;
v_a_93_ = v_tail_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_99_, lean_object* v_s_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_99_, v_s_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_s_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v___x_105_; 
v___x_105_ = ((lean_object*)(l_String_join___closed__0));
return v___x_105_;
}
else
{
lean_object* v_head_106_; lean_object* v_tail_107_; lean_object* v___x_108_; 
v_head_106_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_head_106_);
v_tail_107_ = lean_ctor_get(v_x_104_, 1);
lean_inc(v_tail_107_);
lean_dec_ref_known(v_x_104_, 2);
v___x_108_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_106_, v_s_103_, v_tail_107_);
lean_dec(v_tail_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_String_intercalate(v_s_109_, v_x_110_);
lean_dec_ref(v_s_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_String_intercalate(v_s_112_, v_a_113_);
lean_dec_ref(v_s_112_);
return v___x_114_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_decide_117_; 
v_decide_117_ = lean_nat_dec_eq(v_x_115_, v_x_116_);
return v_decide_117_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_String_instDecidableEqPos_decEq___redArg(v_x_118_, v_x_119_);
lean_dec(v_x_119_);
lean_dec(v_x_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
uint8_t v_decide_125_; 
v_decide_125_ = lean_nat_dec_eq(v_x_123_, v_x_124_);
return v_decide_125_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_126_, lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_String_instDecidableEqPos_decEq(v_s_126_, v_x_127_, v_x_128_);
lean_dec(v_x_128_);
lean_dec(v_x_127_);
lean_dec_ref(v_s_126_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_decide_133_; 
v_decide_133_ = lean_nat_dec_eq(v_x_131_, v_x_132_);
return v_decide_133_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_String_instDecidableEqPos___redArg(v_x_134_, v_x_135_);
lean_dec(v_x_135_);
lean_dec(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* v_s_138_, lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
uint8_t v_decide_141_; 
v_decide_141_ = lean_nat_dec_eq(v_x_139_, v_x_140_);
return v_decide_141_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_String_instDecidableEqPos(v_s_142_, v_x_143_, v_x_144_);
lean_dec(v_x_144_);
lean_dec(v_x_143_);
lean_dec_ref(v_s_142_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___redArg(){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_unsigned_to_nat(0u);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___redArg___boxed(lean_object* v___dummy_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_String_startPos___redArg();
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* v_s_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(0u);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* v_s_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_String_startPos(v_s_153_);
lean_dec_ref(v_s_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg(){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg___boxed(lean_object* v___dummy_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_String_instInhabitedPos___redArg();
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_unsigned_to_nat(0u);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_String_instInhabitedPos(v_s_161_);
lean_dec_ref(v_s_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_string_utf8_byte_size(v_s_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_String_endPos(v_s_165_);
lean_dec_ref(v_s_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___redArg(){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___redArg___boxed(lean_object* v___dummy_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_String_instLEPos___redArg();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* v_s_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* v_s_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_String_instLEPos(v_s_173_);
lean_dec_ref(v_s_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___redArg(){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___redArg___boxed(lean_object* v___dummy_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_String_instLTPos___redArg();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(0);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_String_instLTPos(v_s_181_);
lean_dec_ref(v_s_181_);
return v_res_182_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_183_, lean_object* v_r_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = lean_nat_dec_le(v_l_183_, v_r_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_186_, lean_object* v_r_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_String_instDecidableLePos___redArg(v_l_186_, v_r_187_);
lean_dec(v_r_187_);
lean_dec(v_l_186_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* v_s_190_, lean_object* v_l_191_, lean_object* v_r_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_le(v_l_191_, v_r_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_194_, lean_object* v_l_195_, lean_object* v_r_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_String_instDecidableLePos(v_s_194_, v_l_195_, v_r_196_);
lean_dec(v_r_196_);
lean_dec(v_l_195_);
lean_dec_ref(v_s_194_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_199_, lean_object* v_r_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_l_199_, v___x_201_);
v___x_203_ = lean_nat_dec_le(v___x_202_, v_r_200_);
lean_dec(v___x_202_);
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
v___x_211_ = l_String_instDecidableLtPos___redArg(v_l_209_, v_r_210_);
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
v___x_295_ = 0;
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
v___x_307_ = lean_unsigned_to_nat(539u);
v___x_308_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_309_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_310_ = l_mkPanicMessageWithDecl(v___x_309_, v___x_308_, v___x_307_, v___x_306_, v___x_305_);
return v___x_310_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_311_, lean_object* v_p_312_){
_start:
{
lean_object* v_str_313_; lean_object* v_startInclusive_314_; lean_object* v_endExclusive_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_str_313_ = lean_ctor_get(v_s_311_, 0);
v_startInclusive_314_ = lean_ctor_get(v_s_311_, 1);
v_endExclusive_315_ = lean_ctor_get(v_s_311_, 2);
v___x_316_ = lean_nat_sub(v_endExclusive_315_, v_startInclusive_314_);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_p_312_, v___x_317_);
v___x_319_ = lean_nat_dec_le(v___x_318_, v___x_316_);
lean_dec(v___x_316_);
lean_dec(v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_321_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_nat_add(v_startInclusive_314_, v_p_312_);
v___x_323_ = lean_string_get_byte_fast(v_str_313_, v___x_322_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_324_, lean_object* v_p_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_String_Slice_getUTF8Byte_x21(v_s_324_, v_p_325_);
lean_dec(v_p_325_);
lean_dec_ref(v_s_324_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
uint8_t v_decide_330_; 
v_decide_330_ = lean_nat_dec_eq(v_x_328_, v_x_329_);
return v_decide_330_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_331_, v_x_332_);
lean_dec(v_x_332_);
lean_dec(v_x_331_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
uint8_t v_decide_338_; 
v_decide_338_ = lean_nat_dec_eq(v_x_336_, v_x_337_);
return v_decide_338_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_String_Slice_instDecidableEqPos_decEq(v_s_339_, v_x_340_, v_x_341_);
lean_dec(v_x_341_);
lean_dec(v_x_340_);
lean_dec_ref(v_s_339_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
uint8_t v_decide_346_; 
v_decide_346_ = lean_nat_dec_eq(v_x_344_, v_x_345_);
return v_decide_346_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_String_Slice_instDecidableEqPos___redArg(v_x_347_, v_x_348_);
lean_dec(v_x_348_);
lean_dec(v_x_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
uint8_t v_decide_354_; 
v_decide_354_ = lean_nat_dec_eq(v_x_352_, v_x_353_);
return v_decide_354_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_String_Slice_instDecidableEqPos(v_s_355_, v_x_356_, v_x_357_);
lean_dec(v_x_357_);
lean_dec(v_x_356_);
lean_dec_ref(v_s_355_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg(){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_unsigned_to_nat(0u);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg___boxed(lean_object* v___dummy_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_String_Slice_startPos___redArg();
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_unsigned_to_nat(0u);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_String_Slice_startPos(v_s_366_);
lean_dec_ref(v_s_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg(){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_unsigned_to_nat(0u);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg___boxed(lean_object* v___dummy_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_String_instInhabitedPos__1___redArg();
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_unsigned_to_nat(0u);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_String_instInhabitedPos__1(v_s_374_);
lean_dec_ref(v_s_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_376_){
_start:
{
lean_object* v_startInclusive_377_; lean_object* v_endExclusive_378_; lean_object* v___x_379_; 
v_startInclusive_377_ = lean_ctor_get(v_s_376_, 1);
v_endExclusive_378_ = lean_ctor_get(v_s_376_, 2);
v___x_379_ = lean_nat_sub(v_endExclusive_378_, v_startInclusive_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_String_Slice_endPos(v_s_380_);
lean_dec_ref(v_s_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg(){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg___boxed(lean_object* v___dummy_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_String_instLEPos__1___redArg();
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_String_instLEPos__1(v_s_388_);
lean_dec_ref(v_s_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg(){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg___boxed(lean_object* v___dummy_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_String_instLTPos__1___redArg();
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_box(0);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_String_instLTPos__1(v_s_396_);
lean_dec_ref(v_s_396_);
return v_res_397_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_398_, lean_object* v_r_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_le(v_l_398_, v_r_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_401_, lean_object* v_r_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_String_instDecidableLePos__1___redArg(v_l_401_, v_r_402_);
lean_dec(v_r_402_);
lean_dec(v_l_401_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_405_, lean_object* v_l_406_, lean_object* v_r_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = lean_nat_dec_le(v_l_406_, v_r_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_409_, lean_object* v_l_410_, lean_object* v_r_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_String_instDecidableLePos__1(v_s_409_, v_l_410_, v_r_411_);
lean_dec(v_r_411_);
lean_dec(v_l_410_);
lean_dec_ref(v_s_409_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_414_, lean_object* v_r_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_add(v_l_414_, v___x_416_);
v___x_418_ = lean_nat_dec_le(v___x_417_, v_r_415_);
lean_dec(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_419_, lean_object* v_r_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_String_instDecidableLtPos__1___redArg(v_l_419_, v_r_420_);
lean_dec(v_r_420_);
lean_dec(v_l_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_423_, lean_object* v_l_424_, lean_object* v_r_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = l_String_instDecidableLtPos__1___redArg(v_l_424_, v_r_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_427_, lean_object* v_l_428_, lean_object* v_r_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_String_instDecidableLtPos__1(v_s_427_, v_l_428_, v_r_429_);
lean_dec(v_r_429_);
lean_dec(v_l_428_);
lean_dec_ref(v_s_427_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_432_, lean_object* v_pos_433_){
_start:
{
lean_object* v___x_434_; uint8_t v_decide_435_; 
v___x_434_ = lean_string_utf8_byte_size(v_s_432_);
v_decide_435_ = lean_nat_dec_eq(v_pos_433_, v___x_434_);
return v_decide_435_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_436_, lean_object* v_pos_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_String_instDecidableIsAtEnd(v_s_436_, v_pos_437_);
lean_dec(v_pos_437_);
lean_dec_ref(v_s_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_440_, lean_object* v_pos_441_){
_start:
{
lean_object* v_startInclusive_442_; lean_object* v_endExclusive_443_; lean_object* v___x_444_; uint8_t v_decide_445_; 
v_startInclusive_442_ = lean_ctor_get(v_s_440_, 1);
v_endExclusive_443_ = lean_ctor_get(v_s_440_, 2);
v___x_444_ = lean_nat_sub(v_endExclusive_443_, v_startInclusive_442_);
v_decide_445_ = lean_nat_dec_eq(v_pos_441_, v___x_444_);
lean_dec(v___x_444_);
return v_decide_445_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_446_, lean_object* v_pos_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_String_instDecidableIsAtEnd__1(v_s_446_, v_pos_447_);
lean_dec(v_pos_447_);
lean_dec_ref(v_s_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_450_, lean_object* v_pos_451_){
_start:
{
lean_object* v_str_452_; lean_object* v_startInclusive_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_str_452_ = lean_ctor_get(v_s_450_, 0);
v_startInclusive_453_ = lean_ctor_get(v_s_450_, 1);
v___x_454_ = lean_nat_add(v_startInclusive_453_, v_pos_451_);
v___x_455_ = lean_string_get_byte_fast(v_str_452_, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_456_, lean_object* v_pos_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_String_Slice_Pos_byte___redArg(v_s_456_, v_pos_457_);
lean_dec(v_pos_457_);
lean_dec_ref(v_s_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_460_, lean_object* v_pos_461_, lean_object* v_h_462_){
_start:
{
lean_object* v_str_463_; lean_object* v_startInclusive_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_str_463_ = lean_ctor_get(v_s_460_, 0);
v_startInclusive_464_ = lean_ctor_get(v_s_460_, 1);
v___x_465_ = lean_nat_add(v_startInclusive_464_, v_pos_461_);
v___x_466_ = lean_string_get_byte_fast(v_str_463_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_467_, lean_object* v_pos_468_, lean_object* v_h_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_String_Slice_Pos_byte(v_s_467_, v_pos_468_, v_h_469_);
lean_dec(v_pos_468_);
lean_dec_ref(v_s_467_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_472_){
_start:
{
lean_object* v_startInclusive_473_; lean_object* v_endExclusive_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_startInclusive_473_ = lean_ctor_get(v_s_472_, 1);
v_endExclusive_474_ = lean_ctor_get(v_s_472_, 2);
v___x_475_ = lean_nat_sub(v_endExclusive_474_, v_startInclusive_473_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_nat_dec_eq(v___x_475_, v___x_476_);
lean_dec(v___x_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_String_Slice_isEmpty(v_s_478_);
lean_dec_ref(v_s_478_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_string_utf8_byte_size(v_s_481_);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v_s_481_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_String_toRawSubstring_x27(v_s_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___redArg(){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_unsigned_to_nat(0u);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___redArg___boxed(lean_object* v___dummy_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_String_startValidPos___redArg();
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_unsigned_to_nat(0u);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_String_startValidPos(v_s_493_);
lean_dec_ref(v_s_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_string_utf8_byte_size(v_s_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_String_endValidPos(v_s_497_);
lean_dec_ref(v_s_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_String_bytes(lean_object* v_s_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = lean_string_to_utf8(v_s_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii(lean_object* v_s_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = lean_string_utf8_byte_size(v_s_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii___boxed(lean_object* v_s_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_String_lengthAssumingAscii(v_s_503_);
lean_dec_ref(v_s_503_);
return v_res_504_;
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
