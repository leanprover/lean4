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
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lean_string_to_utf8(v_a_7_);
lean_dec_ref(v_a_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object* v_s_11_, lean_object* v_t_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lean_string_append(v_s_11_, v_t_12_);
lean_dec_ref(v_t_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(0u);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_String_rawStartPos(v___s_18_);
lean_dec_ref(v___s_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t v_c_20_, lean_object* v_s_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_string_push(v_s_21_, v_c_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_23_, lean_object* v_s_24_){
_start:
{
uint32_t v_c_boxed_25_; lean_object* v_res_26_; 
v_c_boxed_25_ = lean_unbox_uint32(v_c_23_);
lean_dec(v_c_23_);
v_res_26_ = l_String_pushn___lam__0(v_c_boxed_25_, v_s_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* v_s_27_, uint32_t v_c_28_, lean_object* v_n_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box_uint32(v_c_28_);
v___f_31_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_31_, 0, v___x_30_);
v___x_32_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_31_, v_n_29_, v_s_27_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_33_, lean_object* v_c_34_, lean_object* v_n_35_){
_start:
{
uint32_t v_c_boxed_36_; lean_object* v_res_37_; 
v_c_boxed_36_ = lean_unbox_uint32(v_c_34_);
lean_dec(v_c_34_);
v_res_37_ = l_String_pushn(v_s_33_, v_c_boxed_36_, v_n_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_38_, lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_zero_41_; uint8_t v_isZero_42_; 
v_zero_41_ = lean_unsigned_to_nat(0u);
v_isZero_42_ = lean_nat_dec_eq(v_x_39_, v_zero_41_);
if (v_isZero_42_ == 1)
{
lean_dec(v_x_39_);
return v_x_40_;
}
else
{
lean_object* v_one_43_; lean_object* v_n_44_; lean_object* v___x_45_; 
v_one_43_ = lean_unsigned_to_nat(1u);
v_n_44_ = lean_nat_sub(v_x_39_, v_one_43_);
lean_dec(v_x_39_);
v___x_45_ = lean_string_push(v_x_40_, v_c_38_);
v_x_39_ = v_n_44_;
v_x_40_ = v___x_45_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
uint32_t v_c_boxed_50_; lean_object* v_res_51_; 
v_c_boxed_50_ = lean_unbox_uint32(v_c_47_);
lean_dec(v_c_47_);
v_res_51_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_50_, v_x_48_, v_x_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* v_s_52_, uint32_t v_c_53_, lean_object* v_n_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_53_, v_n_54_, v_s_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_56_, lean_object* v_c_57_, lean_object* v_n_58_){
_start:
{
uint32_t v_c_boxed_59_; lean_object* v_res_60_; 
v_c_boxed_59_ = lean_unbox_uint32(v_c_57_);
lean_dec(v_c_57_);
v_res_60_ = lean_string_pushn(v_s_56_, v_c_boxed_59_, v_n_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* v_s_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_string_utf8_byte_size(v_s_61_);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_nat_dec_eq(v___x_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_String_isEmpty(v_s_65_);
lean_dec_ref(v_s_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* v_s_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = lean_string_utf8_byte_size(v_s_68_);
lean_dec_ref(v_s_68_);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_eq(v___x_69_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = lean_string_isempty(v_s_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_76_){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___f_77_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_78_ = ((lean_object*)(l_String_join___closed__0));
v___x_79_ = l_List_foldl___redArg(v___f_77_, v___x_78_, v_l_76_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_80_, lean_object* v_s_81_, lean_object* v_a_82_){
_start:
{
if (lean_obj_tag(v_a_82_) == 0)
{
return v_acc_80_;
}
else
{
lean_object* v_head_83_; lean_object* v_tail_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_head_83_ = lean_ctor_get(v_a_82_, 0);
v_tail_84_ = lean_ctor_get(v_a_82_, 1);
v___x_85_ = lean_string_append(v_acc_80_, v_s_81_);
v___x_86_ = lean_string_append(v___x_85_, v_head_83_);
v_acc_80_ = v___x_86_;
v_a_82_ = v_tail_84_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_88_, lean_object* v_s_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_88_, v_s_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec_ref(v_s_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v___x_94_; 
v___x_94_ = ((lean_object*)(l_String_join___closed__0));
return v___x_94_;
}
else
{
lean_object* v_head_95_; lean_object* v_tail_96_; lean_object* v___x_97_; 
v_head_95_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_head_95_);
v_tail_96_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_tail_96_);
lean_dec_ref(v_x_93_);
v___x_97_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_95_, v_s_92_, v_tail_96_);
lean_dec(v_tail_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_String_intercalate(v_s_98_, v_x_99_);
lean_dec_ref(v_s_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_String_intercalate(v_s_101_, v_a_102_);
lean_dec_ref(v_s_101_);
return v___x_103_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_nat_dec_eq(v_x_104_, v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_String_instDecidableEqPos_decEq___redArg(v_x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_111_, lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = lean_nat_dec_eq(v_x_112_, v_x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_String_instDecidableEqPos_decEq(v_s_115_, v_x_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec(v_x_116_);
lean_dec_ref(v_s_115_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_eq(v_x_120_, v_x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_String_instDecidableEqPos___redArg(v_x_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec(v_x_123_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* v_s_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_eq(v_x_128_, v_x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_131_, lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_String_instDecidableEqPos(v_s_131_, v_x_132_, v_x_133_);
lean_dec(v_x_133_);
lean_dec(v_x_132_);
lean_dec_ref(v_s_131_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* v_s_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(0u);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* v_s_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_String_startPos(v_s_138_);
lean_dec_ref(v_s_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_unsigned_to_nat(0u);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_String_instInhabitedPos(v_s_142_);
lean_dec_ref(v_s_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_string_utf8_byte_size(v_s_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_String_endPos(v_s_146_);
lean_dec_ref(v_s_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* v_s_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* v_s_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_String_instLEPos(v_s_150_);
lean_dec_ref(v_s_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_String_instLTPos(v_s_154_);
lean_dec_ref(v_s_154_);
return v_res_155_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_156_, lean_object* v_r_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_le(v_l_156_, v_r_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_159_, lean_object* v_r_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_String_instDecidableLePos___redArg(v_l_159_, v_r_160_);
lean_dec(v_r_160_);
lean_dec(v_l_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* v_s_163_, lean_object* v_l_164_, lean_object* v_r_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_nat_dec_le(v_l_164_, v_r_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_167_, lean_object* v_l_168_, lean_object* v_r_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_String_instDecidableLePos(v_s_167_, v_l_168_, v_r_169_);
lean_dec(v_r_169_);
lean_dec(v_l_168_);
lean_dec_ref(v_s_167_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_172_, lean_object* v_r_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_lt(v_l_172_, v_r_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_175_, lean_object* v_r_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_String_instDecidableLtPos___redArg(v_l_175_, v_r_176_);
lean_dec(v_r_176_);
lean_dec(v_l_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* v_s_179_, lean_object* v_l_180_, lean_object* v_r_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_nat_dec_lt(v_l_180_, v_r_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_183_, lean_object* v_l_184_, lean_object* v_r_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_String_instDecidableLtPos(v_s_183_, v_l_184_, v_r_185_);
lean_dec(v_r_185_);
lean_dec(v_l_184_);
lean_dec_ref(v_s_183_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_string_utf8_byte_size(v_s_192_);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v_s_192_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_198_){
_start:
{
lean_object* v_startInclusive_199_; lean_object* v_endExclusive_200_; lean_object* v___x_201_; 
v_startInclusive_199_ = lean_ctor_get(v_s_198_, 1);
v_endExclusive_200_ = lean_ctor_get(v_s_198_, 2);
v___x_201_ = lean_nat_sub(v_endExclusive_200_, v_startInclusive_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_String_Slice_utf8ByteSize(v_s_202_);
lean_dec_ref(v_s_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_204_, lean_object* v_s_205_){
_start:
{
lean_object* v_startInclusive_206_; lean_object* v_endExclusive_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_startInclusive_206_ = lean_ctor_get(v_s_205_, 1);
v_endExclusive_207_ = lean_ctor_get(v_s_205_, 2);
v___x_208_ = lean_nat_sub(v_endExclusive_207_, v_startInclusive_206_);
v___x_209_ = lean_nat_add(v_p_204_, v___x_208_);
lean_dec(v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_210_, lean_object* v_s_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_String_instHAddRawSlice___lam__0(v_p_210_, v_s_211_);
lean_dec_ref(v_s_211_);
lean_dec(v_p_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_215_, lean_object* v_p_216_){
_start:
{
lean_object* v_startInclusive_217_; lean_object* v_endExclusive_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_startInclusive_217_ = lean_ctor_get(v_s_215_, 1);
v_endExclusive_218_ = lean_ctor_get(v_s_215_, 2);
v___x_219_ = lean_nat_sub(v_endExclusive_218_, v_startInclusive_217_);
v___x_220_ = lean_nat_add(v___x_219_, v_p_216_);
lean_dec(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_221_, lean_object* v_p_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_String_instHAddSliceRaw___lam__0(v_s_221_, v_p_222_);
lean_dec(v_p_222_);
lean_dec_ref(v_s_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_226_, lean_object* v_s_227_){
_start:
{
lean_object* v_startInclusive_228_; lean_object* v_endExclusive_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_startInclusive_228_ = lean_ctor_get(v_s_227_, 1);
v_endExclusive_229_ = lean_ctor_get(v_s_227_, 2);
v___x_230_ = lean_nat_sub(v_endExclusive_229_, v_startInclusive_228_);
v___x_231_ = lean_nat_sub(v_p_226_, v___x_230_);
lean_dec(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_232_, lean_object* v_s_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_String_instHSubRawSlice___lam__0(v_p_232_, v_s_233_);
lean_dec_ref(v_s_233_);
lean_dec(v_p_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_237_){
_start:
{
lean_object* v_startInclusive_238_; lean_object* v_endExclusive_239_; lean_object* v___x_240_; 
v_startInclusive_238_ = lean_ctor_get(v_s_237_, 1);
v_endExclusive_239_ = lean_ctor_get(v_s_237_, 2);
v___x_240_ = lean_nat_sub(v_endExclusive_239_, v_startInclusive_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_String_Slice_rawEndPos(v_s_241_);
lean_dec_ref(v_s_241_);
return v_res_242_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_243_, lean_object* v_p_244_){
_start:
{
lean_object* v_str_245_; lean_object* v_startInclusive_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_str_245_ = lean_ctor_get(v_s_243_, 0);
v_startInclusive_246_ = lean_ctor_get(v_s_243_, 1);
v___x_247_ = lean_nat_add(v_startInclusive_246_, v_p_244_);
v___x_248_ = lean_string_get_byte_fast(v_str_245_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* v_s_249_, lean_object* v_p_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_String_Slice_getUTF8Byte___redArg(v_s_249_, v_p_250_);
lean_dec(v_p_250_);
lean_dec_ref(v_s_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_253_, lean_object* v_p_254_, lean_object* v_h_255_){
_start:
{
lean_object* v_str_256_; lean_object* v_startInclusive_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_str_256_ = lean_ctor_get(v_s_253_, 0);
v_startInclusive_257_ = lean_ctor_get(v_s_253_, 1);
v___x_258_ = lean_nat_add(v_startInclusive_257_, v_p_254_);
v___x_259_ = lean_string_get_byte_fast(v_str_256_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_260_, lean_object* v_p_261_, lean_object* v_h_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_String_Slice_getUTF8Byte(v_s_260_, v_p_261_, v_h_262_);
lean_dec(v_p_261_);
lean_dec_ref(v_s_260_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_265_){
_start:
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = l_instInhabitedUInt8;
v___x_267_ = lean_box(v___x_266_);
v___x_268_ = lean_panic_fn(v___x_267_, v_msg_265_);
v___x_269_ = lean_unbox(v___x_268_);
lean_dec(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_270_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_277_ = lean_unsigned_to_nat(4u);
v___x_278_ = lean_unsigned_to_nat(509u);
v___x_279_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_280_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_281_ = l_mkPanicMessageWithDecl(v___x_280_, v___x_279_, v___x_278_, v___x_277_, v___x_276_);
return v___x_281_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_282_, lean_object* v_p_283_){
_start:
{
lean_object* v_str_284_; lean_object* v_startInclusive_285_; lean_object* v_endExclusive_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_str_284_ = lean_ctor_get(v_s_282_, 0);
v_startInclusive_285_ = lean_ctor_get(v_s_282_, 1);
v_endExclusive_286_ = lean_ctor_get(v_s_282_, 2);
v___x_287_ = lean_nat_sub(v_endExclusive_286_, v_startInclusive_285_);
v___x_288_ = lean_nat_dec_lt(v_p_283_, v___x_287_);
lean_dec(v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_290_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_289_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_nat_add(v_startInclusive_285_, v_p_283_);
v___x_292_ = lean_string_get_byte_fast(v_str_284_, v___x_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_293_, lean_object* v_p_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_String_Slice_getUTF8Byte_x21(v_s_293_, v_p_294_);
lean_dec(v_p_294_);
lean_dec_ref(v_s_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_eq(v_x_297_, v_x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_300_, v_x_301_);
lean_dec(v_x_301_);
lean_dec(v_x_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = lean_nat_dec_eq(v_x_305_, v_x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_String_Slice_instDecidableEqPos_decEq(v_s_308_, v_x_309_, v_x_310_);
lean_dec(v_x_310_);
lean_dec(v_x_309_);
lean_dec_ref(v_s_308_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
uint8_t v___x_315_; 
v___x_315_ = lean_nat_dec_eq(v_x_313_, v_x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_String_Slice_instDecidableEqPos___redArg(v_x_316_, v_x_317_);
lean_dec(v_x_317_);
lean_dec(v_x_316_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_eq(v_x_321_, v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_String_Slice_instDecidableEqPos(v_s_324_, v_x_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec(v_x_325_);
lean_dec_ref(v_s_324_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_unsigned_to_nat(0u);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_String_Slice_startPos(v_s_331_);
lean_dec_ref(v_s_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_String_instInhabitedPos__1(v_s_335_);
lean_dec_ref(v_s_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_337_){
_start:
{
lean_object* v_startInclusive_338_; lean_object* v_endExclusive_339_; lean_object* v___x_340_; 
v_startInclusive_338_ = lean_ctor_get(v_s_337_, 1);
v_endExclusive_339_ = lean_ctor_get(v_s_337_, 2);
v___x_340_ = lean_nat_sub(v_endExclusive_339_, v_startInclusive_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_String_Slice_endPos(v_s_341_);
lean_dec_ref(v_s_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_box(0);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_String_instLEPos__1(v_s_345_);
lean_dec_ref(v_s_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_String_instLTPos__1(v_s_349_);
lean_dec_ref(v_s_349_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_351_, lean_object* v_r_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = lean_nat_dec_le(v_l_351_, v_r_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_354_, lean_object* v_r_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_String_instDecidableLePos__1___redArg(v_l_354_, v_r_355_);
lean_dec(v_r_355_);
lean_dec(v_l_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* v_s_358_, lean_object* v_l_359_, lean_object* v_r_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_le(v_l_359_, v_r_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_362_, lean_object* v_l_363_, lean_object* v_r_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_String_instDecidableLePos__1(v_s_362_, v_l_363_, v_r_364_);
lean_dec(v_r_364_);
lean_dec(v_l_363_);
lean_dec_ref(v_s_362_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_367_, lean_object* v_r_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_nat_dec_lt(v_l_367_, v_r_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_370_, lean_object* v_r_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_String_instDecidableLtPos__1___redArg(v_l_370_, v_r_371_);
lean_dec(v_r_371_);
lean_dec(v_l_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_374_, lean_object* v_l_375_, lean_object* v_r_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_nat_dec_lt(v_l_375_, v_r_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_378_, lean_object* v_l_379_, lean_object* v_r_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_String_instDecidableLtPos__1(v_s_378_, v_l_379_, v_r_380_);
lean_dec(v_r_380_);
lean_dec(v_l_379_);
lean_dec_ref(v_s_378_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_383_, lean_object* v_pos_384_){
_start:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_string_utf8_byte_size(v_s_383_);
v___x_386_ = lean_nat_dec_eq(v_pos_384_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_387_, lean_object* v_pos_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_String_instDecidableIsAtEnd(v_s_387_, v_pos_388_);
lean_dec(v_pos_388_);
lean_dec_ref(v_s_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_391_, lean_object* v_pos_392_){
_start:
{
lean_object* v_startInclusive_393_; lean_object* v_endExclusive_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_startInclusive_393_ = lean_ctor_get(v_s_391_, 1);
v_endExclusive_394_ = lean_ctor_get(v_s_391_, 2);
v___x_395_ = lean_nat_sub(v_endExclusive_394_, v_startInclusive_393_);
v___x_396_ = lean_nat_dec_eq(v_pos_392_, v___x_395_);
lean_dec(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_397_, lean_object* v_pos_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_String_instDecidableIsAtEnd__1(v_s_397_, v_pos_398_);
lean_dec(v_pos_398_);
lean_dec_ref(v_s_397_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_401_, lean_object* v_pos_402_){
_start:
{
lean_object* v_str_403_; lean_object* v_startInclusive_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_str_403_ = lean_ctor_get(v_s_401_, 0);
v_startInclusive_404_ = lean_ctor_get(v_s_401_, 1);
v___x_405_ = lean_nat_add(v_startInclusive_404_, v_pos_402_);
v___x_406_ = lean_string_get_byte_fast(v_str_403_, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_407_, lean_object* v_pos_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_String_Slice_Pos_byte___redArg(v_s_407_, v_pos_408_);
lean_dec(v_pos_408_);
lean_dec_ref(v_s_407_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* v_s_411_, lean_object* v_pos_412_, lean_object* v_h_413_){
_start:
{
lean_object* v_str_414_; lean_object* v_startInclusive_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_str_414_ = lean_ctor_get(v_s_411_, 0);
v_startInclusive_415_ = lean_ctor_get(v_s_411_, 1);
v___x_416_ = lean_nat_add(v_startInclusive_415_, v_pos_412_);
v___x_417_ = lean_string_get_byte_fast(v_str_414_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_418_, lean_object* v_pos_419_, lean_object* v_h_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_String_Slice_Pos_byte(v_s_418_, v_pos_419_, v_h_420_);
lean_dec(v_pos_419_);
lean_dec_ref(v_s_418_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isEmpty(lean_object* v_s_423_){
_start:
{
lean_object* v_startInclusive_424_; lean_object* v_endExclusive_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_startInclusive_424_ = lean_ctor_get(v_s_423_, 1);
v_endExclusive_425_ = lean_ctor_get(v_s_423_, 2);
v___x_426_ = lean_nat_sub(v_endExclusive_425_, v_startInclusive_424_);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_nat_dec_eq(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_String_Slice_isEmpty(v_s_429_);
lean_dec_ref(v_s_429_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_string_utf8_byte_size(v_s_432_);
v___x_435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_435_, 0, v_s_432_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_String_toRawSubstring_x27(v_s_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_unsigned_to_nat(0u);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_String_startValidPos(v_s_440_);
lean_dec_ref(v_s_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_string_utf8_byte_size(v_s_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_String_endValidPos(v_s_444_);
lean_dec_ref(v_s_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_String_String_bytes(lean_object* v_s_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_string_to_utf8(v_s_446_);
return v___x_447_;
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
