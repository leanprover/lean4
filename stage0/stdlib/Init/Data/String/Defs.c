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
LEAN_EXPORT void l_String_toUTF8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_11_ = stack[0].m_obj;
lean_object* v_res_12_;
v_res_12_ = lean_string_to_utf8(v_a_11_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lean_string_to_utf8(v_a_13_);
lean_dec_ref(v_a_13_);
return v_res_14_;
}
}
LEAN_EXPORT void l_String_append_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_15_ = stack[0].m_obj;
lean_object* v_t_16_ = stack[1].m_obj;
lean_object* v_res_17_;
v_res_17_ = lean_string_append(v_s_15_, v_t_16_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object* v_s_18_, lean_object* v_t_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lean_string_append(v_s_18_, v_t_19_);
lean_dec_ref(v_t_19_);
return v_res_20_;
}
}
LEAN_EXPORT void l_String_markLinear_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_23_ = stack[0].m_obj;
lean_object* v_res_24_;
v_res_24_ = lean_string_mark_linear(v_s_23_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_String_markLinear___boxed(lean_object* v_s_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lean_string_mark_linear(v_s_25_);
return v_res_26_;
}
}
LEAN_EXPORT void l_String_propagateMark_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_27_ = stack[0].m_obj;
lean_object* v_t_28_ = stack[1].m_obj;
lean_object* v_res_29_;
v_res_29_ = lean_string_propagate_mark(v_s_27_, v_t_28_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_String_propagateMark___boxed(lean_object* v_s_30_, lean_object* v_t_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lean_string_propagate_mark(v_s_30_, v_t_31_);
lean_dec_ref(v_s_30_);
return v_res_32_;
}
}
lean_object* l_String_rawStartPos___redArg(){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_unsigned_to_nat(0u);
return v___x_34_;
}
}
LEAN_EXPORT void l_String_rawStartPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_35_;
v_res_35_ = l_String_rawStartPos___redArg();
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_String_rawStartPos___redArg___boxed(lean_object* v___dummy_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_String_rawStartPos___redArg();
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* v___s_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(0u);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* v___s_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_String_rawStartPos(v___s_40_);
lean_dec_ref(v___s_40_);
return v_res_41_;
}
}
lean_object* l_String_pushn___lam__0(uint32_t v_c_42_, lean_object* v_s_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_string_push(v_s_43_, v_c_42_);
return v___x_44_;
}
}
LEAN_EXPORT void l_String_pushn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_42_ = stack[0].m_num;
lean_object* v_s_43_ = stack[1].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_String_pushn___lam__0(v_c_42_, v_s_43_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* v_c_46_, lean_object* v_s_47_){
_start:
{
uint32_t v_c_boxed_48_; lean_object* v_res_49_; 
v_c_boxed_48_ = lean_unbox_uint32(v_c_46_);
lean_dec(v_c_46_);
v_res_49_ = l_String_pushn___lam__0(v_c_boxed_48_, v_s_47_);
return v_res_49_;
}
}
lean_object* l_String_pushn(lean_object* v_s_50_, uint32_t v_c_51_, lean_object* v_n_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___f_54_; lean_object* v___x_55_; 
v___x_53_ = lean_box_uint32(v_c_51_);
v___f_54_ = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_54_, 0, v___x_53_);
v___x_55_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_54_, v_n_52_, v_s_50_);
return v___x_55_;
}
}
LEAN_EXPORT void l_String_pushn_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_50_ = stack[0].m_obj;
uint32_t v_c_51_ = stack[1].m_num;
lean_object* v_n_52_ = stack[2].m_obj;
lean_object* v_res_56_;
v_res_56_ = l_String_pushn(v_s_50_, v_c_51_, v_n_52_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* v_s_57_, lean_object* v_c_58_, lean_object* v_n_59_){
_start:
{
uint32_t v_c_boxed_60_; lean_object* v_res_61_; 
v_c_boxed_60_ = lean_unbox_uint32(v_c_58_);
lean_dec(v_c_58_);
v_res_61_ = l_String_pushn(v_s_57_, v_c_boxed_60_, v_n_59_);
return v_res_61_;
}
}
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t v_c_62_, lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_zero_65_; uint8_t v_isZero_66_; 
v_zero_65_ = lean_unsigned_to_nat(0u);
v_isZero_66_ = lean_nat_dec_eq(v_x_63_, v_zero_65_);
if (v_isZero_66_ == 1)
{
lean_dec(v_x_63_);
return v_x_64_;
}
else
{
lean_object* v_one_67_; lean_object* v_n_68_; lean_object* v___x_69_; 
v_one_67_ = lean_unsigned_to_nat(1u);
v_n_68_ = lean_nat_sub(v_x_63_, v_one_67_);
lean_dec(v_x_63_);
v___x_69_ = lean_string_push(v_x_64_, v_c_62_);
v_x_63_ = v_n_68_;
v_x_64_ = v___x_69_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_62_ = stack[0].m_num;
lean_object* v_x_63_ = stack[1].m_obj;
lean_object* v_x_64_ = stack[2].m_obj;
lean_object* v_res_71_;
v_res_71_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_62_, v_x_63_, v_x_64_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* v_c_72_, lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint32_t v_c_boxed_75_; lean_object* v_res_76_; 
v_c_boxed_75_ = lean_unbox_uint32(v_c_72_);
lean_dec(v_c_72_);
v_res_76_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_75_, v_x_73_, v_x_74_);
return v_res_76_;
}
}
lean_object* lean_string_pushn(lean_object* v_s_77_, uint32_t v_c_78_, lean_object* v_n_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_78_, v_n_79_, v_s_77_);
return v___x_80_;
}
}
LEAN_EXPORT void lean_string_pushn_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_77_ = stack[0].m_obj;
uint32_t v_c_78_ = stack[1].m_num;
lean_object* v_n_79_ = stack[2].m_obj;
lean_object* v_res_81_;
v_res_81_ = lean_string_pushn(v_s_77_, v_c_78_, v_n_79_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* v_s_82_, lean_object* v_c_83_, lean_object* v_n_84_){
_start:
{
uint32_t v_c_boxed_85_; lean_object* v_res_86_; 
v_c_boxed_85_ = lean_unbox_uint32(v_c_83_);
lean_dec(v_c_83_);
v_res_86_ = lean_string_pushn(v_s_82_, v_c_boxed_85_, v_n_84_);
return v_res_86_;
}
}
uint8_t l_String_isEmpty(lean_object* v_s_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_88_ = lean_string_utf8_byte_size(v_s_87_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_nat_dec_eq(v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT void l_String_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_87_ = stack[0].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_String_isEmpty(v_s_87_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* v_s_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_String_isEmpty(v_s_92_);
lean_dec_ref(v_s_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint8_t lean_string_isempty(lean_object* v_s_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_96_ = lean_string_utf8_byte_size(v_s_95_);
lean_dec_ref(v_s_95_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_nat_dec_eq(v___x_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT void lean_string_isempty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_95_ = stack[0].m_obj;
uint8_t v_res_99_;
v_res_99_ = lean_string_isempty(v_s_95_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* v_s_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = lean_string_isempty(v_s_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* v_l_104_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___f_105_ = ((lean_object*)(l_instAppendString___closed__0));
v___x_106_ = ((lean_object*)(l_String_join___closed__0));
v___x_107_ = l_List_foldl___redArg(v___f_105_, v___x_106_, v_l_104_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* v_acc_108_, lean_object* v_s_109_, lean_object* v_a_110_){
_start:
{
if (lean_obj_tag(v_a_110_) == 0)
{
return v_acc_108_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_head_111_ = lean_ctor_get(v_a_110_, 0);
v_tail_112_ = lean_ctor_get(v_a_110_, 1);
v___x_113_ = lean_string_append(v_acc_108_, v_s_109_);
v___x_114_ = lean_string_append(v___x_113_, v_head_111_);
v_acc_108_ = v___x_114_;
v_a_110_ = v_tail_112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* v_acc_116_, lean_object* v_s_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_116_, v_s_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_s_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* v_s_120_, lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_String_join___closed__0));
return v___x_122_;
}
else
{
lean_object* v_head_123_; lean_object* v_tail_124_; lean_object* v___x_125_; 
v_head_123_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_head_123_);
v_tail_124_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_tail_124_);
lean_dec_ref_known(v_x_121_, 2);
v___x_125_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(v_head_123_, v_s_120_, v_tail_124_);
lean_dec(v_tail_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* v_s_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_String_intercalate(v_s_126_, v_x_127_);
lean_dec_ref(v_s_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* v_s_129_, lean_object* v_a_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_String_intercalate(v_s_129_, v_a_130_);
lean_dec_ref(v_s_129_);
return v___x_131_;
}
}
uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
uint8_t v_decide_134_; 
v_decide_134_ = lean_nat_dec_eq(v_x_132_, v_x_133_);
return v_decide_134_;
}
}
LEAN_EXPORT void l_String_instDecidableEqPos_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_132_ = stack[0].m_obj;
lean_object* v_x_133_ = stack[1].m_obj;
uint8_t v_res_135_;
v_res_135_ = l_String_instDecidableEqPos_decEq___redArg(v_x_132_, v_x_133_);
stack->m_num = v_res_135_;
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
uint8_t l_String_instDecidableEqPos_decEq(lean_object* v_s_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
uint8_t v_decide_143_; 
v_decide_143_ = lean_nat_dec_eq(v_x_141_, v_x_142_);
return v_decide_143_;
}
}
LEAN_EXPORT void l_String_instDecidableEqPos_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_140_ = stack[0].m_obj;
lean_object* v_x_141_ = stack[1].m_obj;
lean_object* v_x_142_ = stack[2].m_obj;
uint8_t v_res_144_;
v_res_144_ = l_String_instDecidableEqPos_decEq(v_s_140_, v_x_141_, v_x_142_);
stack->m_num = v_res_144_;
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* v_s_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_String_instDecidableEqPos_decEq(v_s_145_, v_x_146_, v_x_147_);
lean_dec(v_x_147_);
lean_dec(v_x_146_);
lean_dec_ref(v_s_145_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
uint8_t l_String_instDecidableEqPos___redArg(lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
uint8_t v_decide_152_; 
v_decide_152_ = lean_nat_dec_eq(v_x_150_, v_x_151_);
return v_decide_152_;
}
}
LEAN_EXPORT void l_String_instDecidableEqPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_150_ = stack[0].m_obj;
lean_object* v_x_151_ = stack[1].m_obj;
uint8_t v_res_153_;
v_res_153_ = l_String_instDecidableEqPos___redArg(v_x_150_, v_x_151_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_String_instDecidableEqPos___redArg(v_x_154_, v_x_155_);
lean_dec(v_x_155_);
lean_dec(v_x_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
uint8_t l_String_instDecidableEqPos(lean_object* v_s_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
uint8_t v_decide_161_; 
v_decide_161_ = lean_nat_dec_eq(v_x_159_, v_x_160_);
return v_decide_161_;
}
}
LEAN_EXPORT void l_String_instDecidableEqPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_158_ = stack[0].m_obj;
lean_object* v_x_159_ = stack[1].m_obj;
lean_object* v_x_160_ = stack[2].m_obj;
uint8_t v_res_162_;
v_res_162_ = l_String_instDecidableEqPos(v_s_158_, v_x_159_, v_x_160_);
stack->m_num = v_res_162_;
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* v_s_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_String_instDecidableEqPos(v_s_163_, v_x_164_, v_x_165_);
lean_dec(v_x_165_);
lean_dec(v_x_164_);
lean_dec_ref(v_s_163_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
lean_object* l_String_startPos___redArg(){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_unsigned_to_nat(0u);
return v___x_169_;
}
}
LEAN_EXPORT void l_String_startPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_170_;
v_res_170_ = l_String_startPos___redArg();
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_String_startPos___redArg___boxed(lean_object* v___dummy_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_String_startPos___redArg();
return v_res_172_;
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
lean_object* l_String_instInhabitedPos___redArg(){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(0u);
return v___x_178_;
}
}
LEAN_EXPORT void l_String_instInhabitedPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_179_;
v_res_179_ = l_String_instInhabitedPos___redArg();
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___redArg___boxed(lean_object* v___dummy_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_String_instInhabitedPos___redArg();
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* v_s_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(0u);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* v_s_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_String_instInhabitedPos(v_s_184_);
lean_dec_ref(v_s_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* v_s_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_string_utf8_byte_size(v_s_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* v_s_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_String_endPos(v_s_188_);
lean_dec_ref(v_s_188_);
return v_res_189_;
}
}
lean_object* l_String_instLEPos___redArg(){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT void l_String_instLEPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_192_;
v_res_192_ = l_String_instLEPos___redArg();
stack->m_obj
 = v_res_192_;
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
lean_object* l_String_instLTPos___redArg(){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
LEAN_EXPORT void l_String_instLTPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_201_;
v_res_201_ = l_String_instLTPos___redArg();
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_String_instLTPos___redArg___boxed(lean_object* v___dummy_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_String_instLTPos___redArg();
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* v_s_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* v_s_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_String_instLTPos(v_s_206_);
lean_dec_ref(v_s_206_);
return v_res_207_;
}
}
uint8_t l_String_instDecidableLePos___redArg(lean_object* v_l_208_, lean_object* v_r_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = lean_nat_dec_le(v_l_208_, v_r_209_);
return v___x_210_;
}
}
LEAN_EXPORT void l_String_instDecidableLePos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_208_ = stack[0].m_obj;
lean_object* v_r_209_ = stack[1].m_obj;
uint8_t v_res_211_;
v_res_211_ = l_String_instDecidableLePos___redArg(v_l_208_, v_r_209_);
stack->m_num = v_res_211_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* v_l_212_, lean_object* v_r_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_String_instDecidableLePos___redArg(v_l_212_, v_r_213_);
lean_dec(v_r_213_);
lean_dec(v_l_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
uint8_t l_String_instDecidableLePos(lean_object* v_s_216_, lean_object* v_l_217_, lean_object* v_r_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = lean_nat_dec_le(v_l_217_, v_r_218_);
return v___x_219_;
}
}
LEAN_EXPORT void l_String_instDecidableLePos_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_216_ = stack[0].m_obj;
lean_object* v_l_217_ = stack[1].m_obj;
lean_object* v_r_218_ = stack[2].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_String_instDecidableLePos(v_s_216_, v_l_217_, v_r_218_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* v_s_221_, lean_object* v_l_222_, lean_object* v_r_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_String_instDecidableLePos(v_s_221_, v_l_222_, v_r_223_);
lean_dec(v_r_223_);
lean_dec(v_l_222_);
lean_dec_ref(v_s_221_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
uint8_t l_String_instDecidableLtPos___redArg(lean_object* v_l_226_, lean_object* v_r_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_add(v_l_226_, v___x_228_);
v___x_230_ = lean_nat_dec_le(v___x_229_, v_r_227_);
lean_dec(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT void l_String_instDecidableLtPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_226_ = stack[0].m_obj;
lean_object* v_r_227_ = stack[1].m_obj;
uint8_t v_res_231_;
v_res_231_ = l_String_instDecidableLtPos___redArg(v_l_226_, v_r_227_);
stack->m_num = v_res_231_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* v_l_232_, lean_object* v_r_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_String_instDecidableLtPos___redArg(v_l_232_, v_r_233_);
lean_dec(v_r_233_);
lean_dec(v_l_232_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
uint8_t l_String_instDecidableLtPos(lean_object* v_s_236_, lean_object* v_l_237_, lean_object* v_r_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_String_instDecidableLtPos___redArg(v_l_237_, v_r_238_);
return v___x_239_;
}
}
LEAN_EXPORT void l_String_instDecidableLtPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_236_ = stack[0].m_obj;
lean_object* v_l_237_ = stack[1].m_obj;
lean_object* v_r_238_ = stack[2].m_obj;
uint8_t v_res_240_;
v_res_240_ = l_String_instDecidableLtPos(v_s_236_, v_l_237_, v_r_238_);
stack->m_num = v_res_240_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* v_s_241_, lean_object* v_l_242_, lean_object* v_r_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_String_instDecidableLtPos(v_s_241_, v_l_242_, v_r_243_);
lean_dec(v_r_243_);
lean_dec(v_l_242_);
lean_dec_ref(v_s_241_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* v_s_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_string_utf8_byte_size(v_s_250_);
v___x_253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_253_, 0, v_s_250_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* v_s_256_){
_start:
{
lean_object* v_startInclusive_257_; lean_object* v_endExclusive_258_; lean_object* v___x_259_; 
v_startInclusive_257_ = lean_ctor_get(v_s_256_, 1);
v_endExclusive_258_ = lean_ctor_get(v_s_256_, 2);
v___x_259_ = lean_nat_sub(v_endExclusive_258_, v_startInclusive_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* v_s_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_String_Slice_utf8ByteSize(v_s_260_);
lean_dec_ref(v_s_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* v_p_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_startInclusive_264_; lean_object* v_endExclusive_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_startInclusive_264_ = lean_ctor_get(v_s_263_, 1);
v_endExclusive_265_ = lean_ctor_get(v_s_263_, 2);
v___x_266_ = lean_nat_sub(v_endExclusive_265_, v_startInclusive_264_);
v___x_267_ = lean_nat_add(v_p_262_, v___x_266_);
lean_dec(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* v_p_268_, lean_object* v_s_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_String_instHAddRawSlice___lam__0(v_p_268_, v_s_269_);
lean_dec_ref(v_s_269_);
lean_dec(v_p_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* v_s_273_, lean_object* v_p_274_){
_start:
{
lean_object* v_startInclusive_275_; lean_object* v_endExclusive_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_startInclusive_275_ = lean_ctor_get(v_s_273_, 1);
v_endExclusive_276_ = lean_ctor_get(v_s_273_, 2);
v___x_277_ = lean_nat_sub(v_endExclusive_276_, v_startInclusive_275_);
v___x_278_ = lean_nat_add(v___x_277_, v_p_274_);
lean_dec(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* v_s_279_, lean_object* v_p_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_String_instHAddSliceRaw___lam__0(v_s_279_, v_p_280_);
lean_dec(v_p_280_);
lean_dec_ref(v_s_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* v_p_284_, lean_object* v_s_285_){
_start:
{
lean_object* v_startInclusive_286_; lean_object* v_endExclusive_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_startInclusive_286_ = lean_ctor_get(v_s_285_, 1);
v_endExclusive_287_ = lean_ctor_get(v_s_285_, 2);
v___x_288_ = lean_nat_sub(v_endExclusive_287_, v_startInclusive_286_);
v___x_289_ = lean_nat_sub(v_p_284_, v___x_288_);
lean_dec(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* v_p_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_String_instHSubRawSlice___lam__0(v_p_290_, v_s_291_);
lean_dec_ref(v_s_291_);
lean_dec(v_p_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* v_s_295_){
_start:
{
lean_object* v_startInclusive_296_; lean_object* v_endExclusive_297_; lean_object* v___x_298_; 
v_startInclusive_296_ = lean_ctor_get(v_s_295_, 1);
v_endExclusive_297_ = lean_ctor_get(v_s_295_, 2);
v___x_298_ = lean_nat_sub(v_endExclusive_297_, v_startInclusive_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* v_s_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_String_Slice_rawEndPos(v_s_299_);
lean_dec_ref(v_s_299_);
return v_res_300_;
}
}
uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* v_s_301_, lean_object* v_p_302_){
_start:
{
lean_object* v_str_303_; lean_object* v_startInclusive_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_str_303_ = lean_ctor_get(v_s_301_, 0);
v_startInclusive_304_ = lean_ctor_get(v_s_301_, 1);
v___x_305_ = lean_nat_add(v_startInclusive_304_, v_p_302_);
v___x_306_ = lean_string_get_byte_fast(v_str_303_, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT void l_String_Slice_getUTF8Byte___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_301_ = stack[0].m_obj;
lean_object* v_p_302_ = stack[1].m_obj;
uint8_t v_res_307_;
v_res_307_ = l_String_Slice_getUTF8Byte___redArg(v_s_301_, v_p_302_);
stack->m_num = v_res_307_;
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
uint8_t l_String_Slice_getUTF8Byte(lean_object* v_s_312_, lean_object* v_p_313_, lean_object* v_h_314_){
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
LEAN_EXPORT void l_String_Slice_getUTF8Byte_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_312_ = stack[0].m_obj;
lean_object* v_p_313_ = stack[1].m_obj;
uint8_t v_res_319_;
v_res_319_ = l_String_Slice_getUTF8Byte(v_s_312_, v_p_313_, lean_box(0));
stack->m_num = v_res_319_;
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* v_s_320_, lean_object* v_p_321_, lean_object* v_h_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_String_Slice_getUTF8Byte(v_s_320_, v_p_321_, v_h_322_);
lean_dec(v_p_321_);
lean_dec_ref(v_s_320_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* v_msg_325_){
_start:
{
uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_326_ = 0;
v___x_327_ = lean_box(v___x_326_);
v___x_328_ = lean_panic_fn_borrowed(v___x_327_, v_msg_325_);
lean_dec(v___x_327_);
v___x_329_ = lean_unbox(v___x_328_);
lean_dec(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT void l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_325_ = stack[0].m_obj;
uint8_t v_res_330_;
v_res_330_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_325_);
stack->m_num = v_res_330_;
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* v_msg_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_331_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__2));
v___x_338_ = lean_unsigned_to_nat(4u);
v___x_339_ = lean_unsigned_to_nat(536u);
v___x_340_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__1));
v___x_341_ = ((lean_object*)(l_String_Slice_getUTF8Byte_x21___closed__0));
v___x_342_ = l_mkPanicMessageWithDecl(v___x_341_, v___x_340_, v___x_339_, v___x_338_, v___x_337_);
return v___x_342_;
}
}
uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* v_s_343_, lean_object* v_p_344_){
_start:
{
lean_object* v_str_345_; lean_object* v_startInclusive_346_; lean_object* v_endExclusive_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_str_345_ = lean_ctor_get(v_s_343_, 0);
v_startInclusive_346_ = lean_ctor_get(v_s_343_, 1);
v_endExclusive_347_ = lean_ctor_get(v_s_343_, 2);
v___x_348_ = lean_nat_sub(v_endExclusive_347_, v_startInclusive_346_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_p_344_, v___x_349_);
v___x_351_ = lean_nat_dec_le(v___x_350_, v___x_348_);
lean_dec(v___x_348_);
lean_dec(v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_obj_once(&l_String_Slice_getUTF8Byte_x21___closed__3, &l_String_Slice_getUTF8Byte_x21___closed__3_once, _init_l_String_Slice_getUTF8Byte_x21___closed__3);
v___x_353_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_352_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_nat_add(v_startInclusive_346_, v_p_344_);
v___x_355_ = lean_string_get_byte_fast(v_str_345_, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT void l_String_Slice_getUTF8Byte_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_343_ = stack[0].m_obj;
lean_object* v_p_344_ = stack[1].m_obj;
uint8_t v_res_356_;
v_res_356_ = l_String_Slice_getUTF8Byte_x21(v_s_343_, v_p_344_);
stack->m_num = v_res_356_;
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* v_s_357_, lean_object* v_p_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_String_Slice_getUTF8Byte_x21(v_s_357_, v_p_358_);
lean_dec(v_p_358_);
lean_dec_ref(v_s_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_decide_363_; 
v_decide_363_ = lean_nat_dec_eq(v_x_361_, v_x_362_);
return v_decide_363_;
}
}
LEAN_EXPORT void l_String_Slice_instDecidableEqPos_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_361_ = stack[0].m_obj;
lean_object* v_x_362_ = stack[1].m_obj;
uint8_t v_res_364_;
v_res_364_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_361_, v_x_362_);
stack->m_num = v_res_364_;
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_365_, v_x_366_);
lean_dec(v_x_366_);
lean_dec(v_x_365_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* v_s_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_decide_372_; 
v_decide_372_ = lean_nat_dec_eq(v_x_370_, v_x_371_);
return v_decide_372_;
}
}
LEAN_EXPORT void l_String_Slice_instDecidableEqPos_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_369_ = stack[0].m_obj;
lean_object* v_x_370_ = stack[1].m_obj;
lean_object* v_x_371_ = stack[2].m_obj;
uint8_t v_res_373_;
v_res_373_ = l_String_Slice_instDecidableEqPos_decEq(v_s_369_, v_x_370_, v_x_371_);
stack->m_num = v_res_373_;
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* v_s_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_String_Slice_instDecidableEqPos_decEq(v_s_374_, v_x_375_, v_x_376_);
lean_dec(v_x_376_);
lean_dec(v_x_375_);
lean_dec_ref(v_s_374_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_decide_381_; 
v_decide_381_ = lean_nat_dec_eq(v_x_379_, v_x_380_);
return v_decide_381_;
}
}
LEAN_EXPORT void l_String_Slice_instDecidableEqPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_379_ = stack[0].m_obj;
lean_object* v_x_380_ = stack[1].m_obj;
uint8_t v_res_382_;
v_res_382_ = l_String_Slice_instDecidableEqPos___redArg(v_x_379_, v_x_380_);
stack->m_num = v_res_382_;
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_String_Slice_instDecidableEqPos___redArg(v_x_383_, v_x_384_);
lean_dec(v_x_384_);
lean_dec(v_x_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
uint8_t l_String_Slice_instDecidableEqPos(lean_object* v_s_387_, lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
uint8_t v_decide_390_; 
v_decide_390_ = lean_nat_dec_eq(v_x_388_, v_x_389_);
return v_decide_390_;
}
}
LEAN_EXPORT void l_String_Slice_instDecidableEqPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_387_ = stack[0].m_obj;
lean_object* v_x_388_ = stack[1].m_obj;
lean_object* v_x_389_ = stack[2].m_obj;
uint8_t v_res_391_;
v_res_391_ = l_String_Slice_instDecidableEqPos(v_s_387_, v_x_388_, v_x_389_);
stack->m_num = v_res_391_;
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* v_s_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_String_Slice_instDecidableEqPos(v_s_392_, v_x_393_, v_x_394_);
lean_dec(v_x_394_);
lean_dec(v_x_393_);
lean_dec_ref(v_s_392_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
lean_object* l_String_Slice_startPos___redArg(){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_unsigned_to_nat(0u);
return v___x_398_;
}
}
LEAN_EXPORT void l_String_Slice_startPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_399_;
v_res_399_ = l_String_Slice_startPos___redArg();
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___redArg___boxed(lean_object* v___dummy_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_String_Slice_startPos___redArg();
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* v_s_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_unsigned_to_nat(0u);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* v_s_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_String_Slice_startPos(v_s_404_);
lean_dec_ref(v_s_404_);
return v_res_405_;
}
}
lean_object* l_String_instInhabitedPos__1___redArg(){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_unsigned_to_nat(0u);
return v___x_407_;
}
}
LEAN_EXPORT void l_String_instInhabitedPos__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_408_;
v_res_408_ = l_String_instInhabitedPos__1___redArg();
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___redArg___boxed(lean_object* v___dummy_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_String_instInhabitedPos__1___redArg();
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* v_s_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lean_unsigned_to_nat(0u);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* v_s_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_String_instInhabitedPos__1(v_s_413_);
lean_dec_ref(v_s_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* v_s_415_){
_start:
{
lean_object* v_startInclusive_416_; lean_object* v_endExclusive_417_; lean_object* v___x_418_; 
v_startInclusive_416_ = lean_ctor_get(v_s_415_, 1);
v_endExclusive_417_ = lean_ctor_get(v_s_415_, 2);
v___x_418_ = lean_nat_sub(v_endExclusive_417_, v_startInclusive_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* v_s_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_String_Slice_endPos(v_s_419_);
lean_dec_ref(v_s_419_);
return v_res_420_;
}
}
lean_object* l_String_instLEPos__1___redArg(){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
LEAN_EXPORT void l_String_instLEPos__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_423_;
v_res_423_ = l_String_instLEPos__1___redArg();
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___redArg___boxed(lean_object* v___dummy_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_String_instLEPos__1___redArg();
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* v_s_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_box(0);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* v_s_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_String_instLEPos__1(v_s_428_);
lean_dec_ref(v_s_428_);
return v_res_429_;
}
}
lean_object* l_String_instLTPos__1___redArg(){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_box(0);
return v___x_431_;
}
}
LEAN_EXPORT void l_String_instLTPos__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_432_;
v_res_432_ = l_String_instLTPos__1___redArg();
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___redArg___boxed(lean_object* v___dummy_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_String_instLTPos__1___redArg();
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* v_s_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_box(0);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* v_s_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_String_instLTPos__1(v_s_437_);
lean_dec_ref(v_s_437_);
return v_res_438_;
}
}
uint8_t l_String_instDecidableLePos__1___redArg(lean_object* v_l_439_, lean_object* v_r_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = lean_nat_dec_le(v_l_439_, v_r_440_);
return v___x_441_;
}
}
LEAN_EXPORT void l_String_instDecidableLePos__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_439_ = stack[0].m_obj;
lean_object* v_r_440_ = stack[1].m_obj;
uint8_t v_res_442_;
v_res_442_ = l_String_instDecidableLePos__1___redArg(v_l_439_, v_r_440_);
stack->m_num = v_res_442_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* v_l_443_, lean_object* v_r_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_String_instDecidableLePos__1___redArg(v_l_443_, v_r_444_);
lean_dec(v_r_444_);
lean_dec(v_l_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
uint8_t l_String_instDecidableLePos__1(lean_object* v_s_447_, lean_object* v_l_448_, lean_object* v_r_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = lean_nat_dec_le(v_l_448_, v_r_449_);
return v___x_450_;
}
}
LEAN_EXPORT void l_String_instDecidableLePos__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_447_ = stack[0].m_obj;
lean_object* v_l_448_ = stack[1].m_obj;
lean_object* v_r_449_ = stack[2].m_obj;
uint8_t v_res_451_;
v_res_451_ = l_String_instDecidableLePos__1(v_s_447_, v_l_448_, v_r_449_);
stack->m_num = v_res_451_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* v_s_452_, lean_object* v_l_453_, lean_object* v_r_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_String_instDecidableLePos__1(v_s_452_, v_l_453_, v_r_454_);
lean_dec(v_r_454_);
lean_dec(v_l_453_);
lean_dec_ref(v_s_452_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* v_l_457_, lean_object* v_r_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_add(v_l_457_, v___x_459_);
v___x_461_ = lean_nat_dec_le(v___x_460_, v_r_458_);
lean_dec(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT void l_String_instDecidableLtPos__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_457_ = stack[0].m_obj;
lean_object* v_r_458_ = stack[1].m_obj;
uint8_t v_res_462_;
v_res_462_ = l_String_instDecidableLtPos__1___redArg(v_l_457_, v_r_458_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* v_l_463_, lean_object* v_r_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_String_instDecidableLtPos__1___redArg(v_l_463_, v_r_464_);
lean_dec(v_r_464_);
lean_dec(v_l_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
uint8_t l_String_instDecidableLtPos__1(lean_object* v_s_467_, lean_object* v_l_468_, lean_object* v_r_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = l_String_instDecidableLtPos__1___redArg(v_l_468_, v_r_469_);
return v___x_470_;
}
}
LEAN_EXPORT void l_String_instDecidableLtPos__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_467_ = stack[0].m_obj;
lean_object* v_l_468_ = stack[1].m_obj;
lean_object* v_r_469_ = stack[2].m_obj;
uint8_t v_res_471_;
v_res_471_ = l_String_instDecidableLtPos__1(v_s_467_, v_l_468_, v_r_469_);
stack->m_num = v_res_471_;
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* v_s_472_, lean_object* v_l_473_, lean_object* v_r_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_String_instDecidableLtPos__1(v_s_472_, v_l_473_, v_r_474_);
lean_dec(v_r_474_);
lean_dec(v_l_473_);
lean_dec_ref(v_s_472_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
uint8_t l_String_instDecidableIsAtEnd(lean_object* v_s_477_, lean_object* v_pos_478_){
_start:
{
lean_object* v___x_479_; uint8_t v_decide_480_; 
v___x_479_ = lean_string_utf8_byte_size(v_s_477_);
v_decide_480_ = lean_nat_dec_eq(v_pos_478_, v___x_479_);
return v_decide_480_;
}
}
LEAN_EXPORT void l_String_instDecidableIsAtEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_477_ = stack[0].m_obj;
lean_object* v_pos_478_ = stack[1].m_obj;
uint8_t v_res_481_;
v_res_481_ = l_String_instDecidableIsAtEnd(v_s_477_, v_pos_478_);
stack->m_num = v_res_481_;
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* v_s_482_, lean_object* v_pos_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_String_instDecidableIsAtEnd(v_s_482_, v_pos_483_);
lean_dec(v_pos_483_);
lean_dec_ref(v_s_482_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
uint8_t l_String_instDecidableIsAtEnd__1(lean_object* v_s_486_, lean_object* v_pos_487_){
_start:
{
lean_object* v_startInclusive_488_; lean_object* v_endExclusive_489_; lean_object* v___x_490_; uint8_t v_decide_491_; 
v_startInclusive_488_ = lean_ctor_get(v_s_486_, 1);
v_endExclusive_489_ = lean_ctor_get(v_s_486_, 2);
v___x_490_ = lean_nat_sub(v_endExclusive_489_, v_startInclusive_488_);
v_decide_491_ = lean_nat_dec_eq(v_pos_487_, v___x_490_);
lean_dec(v___x_490_);
return v_decide_491_;
}
}
LEAN_EXPORT void l_String_instDecidableIsAtEnd__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_486_ = stack[0].m_obj;
lean_object* v_pos_487_ = stack[1].m_obj;
uint8_t v_res_492_;
v_res_492_ = l_String_instDecidableIsAtEnd__1(v_s_486_, v_pos_487_);
stack->m_num = v_res_492_;
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* v_s_493_, lean_object* v_pos_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_String_instDecidableIsAtEnd__1(v_s_493_, v_pos_494_);
lean_dec(v_pos_494_);
lean_dec_ref(v_s_493_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
uint8_t l_String_Slice_Pos_byte___redArg(lean_object* v_s_497_, lean_object* v_pos_498_){
_start:
{
lean_object* v_str_499_; lean_object* v_startInclusive_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_str_499_ = lean_ctor_get(v_s_497_, 0);
v_startInclusive_500_ = lean_ctor_get(v_s_497_, 1);
v___x_501_ = lean_nat_add(v_startInclusive_500_, v_pos_498_);
v___x_502_ = lean_string_get_byte_fast(v_str_499_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT void l_String_Slice_Pos_byte___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_497_ = stack[0].m_obj;
lean_object* v_pos_498_ = stack[1].m_obj;
uint8_t v_res_503_;
v_res_503_ = l_String_Slice_Pos_byte___redArg(v_s_497_, v_pos_498_);
stack->m_num = v_res_503_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* v_s_504_, lean_object* v_pos_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l_String_Slice_Pos_byte___redArg(v_s_504_, v_pos_505_);
lean_dec(v_pos_505_);
lean_dec_ref(v_s_504_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
uint8_t l_String_Slice_Pos_byte(lean_object* v_s_508_, lean_object* v_pos_509_, lean_object* v_h_510_){
_start:
{
lean_object* v_str_511_; lean_object* v_startInclusive_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_str_511_ = lean_ctor_get(v_s_508_, 0);
v_startInclusive_512_ = lean_ctor_get(v_s_508_, 1);
v___x_513_ = lean_nat_add(v_startInclusive_512_, v_pos_509_);
v___x_514_ = lean_string_get_byte_fast(v_str_511_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT void l_String_Slice_Pos_byte_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_508_ = stack[0].m_obj;
lean_object* v_pos_509_ = stack[1].m_obj;
uint8_t v_res_515_;
v_res_515_ = l_String_Slice_Pos_byte(v_s_508_, v_pos_509_, lean_box(0));
stack->m_num = v_res_515_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* v_s_516_, lean_object* v_pos_517_, lean_object* v_h_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_String_Slice_Pos_byte(v_s_516_, v_pos_517_, v_h_518_);
lean_dec(v_pos_517_);
lean_dec_ref(v_s_516_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
uint8_t l_String_Slice_isEmpty(lean_object* v_s_521_){
_start:
{
lean_object* v_startInclusive_522_; lean_object* v_endExclusive_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_startInclusive_522_ = lean_ctor_get(v_s_521_, 1);
v_endExclusive_523_ = lean_ctor_get(v_s_521_, 2);
v___x_524_ = lean_nat_sub(v_endExclusive_523_, v_startInclusive_522_);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_nat_dec_eq(v___x_524_, v___x_525_);
lean_dec(v___x_524_);
return v___x_526_;
}
}
LEAN_EXPORT void l_String_Slice_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_521_ = stack[0].m_obj;
uint8_t v_res_527_;
v_res_527_ = l_String_Slice_isEmpty(v_s_521_);
stack->m_num = v_res_527_;
}
LEAN_EXPORT lean_object* l_String_Slice_isEmpty___boxed(lean_object* v_s_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_String_Slice_isEmpty(v_s_528_);
lean_dec_ref(v_s_528_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* v_s_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_string_utf8_byte_size(v_s_531_);
v___x_534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_534_, 0, v_s_531_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* v_s_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_String_toRawSubstring_x27(v_s_535_);
return v___x_536_;
}
}
lean_object* l_String_startValidPos___redArg(){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_unsigned_to_nat(0u);
return v___x_538_;
}
}
LEAN_EXPORT void l_String_startValidPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_539_;
v_res_539_ = l_String_startValidPos___redArg();
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l_String_startValidPos___redArg___boxed(lean_object* v___dummy_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_String_startValidPos___redArg();
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* v_s_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_unsigned_to_nat(0u);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* v_s_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_String_startValidPos(v_s_544_);
lean_dec_ref(v_s_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* v_s_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_string_utf8_byte_size(v_s_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* v_s_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_String_endValidPos(v_s_548_);
lean_dec_ref(v_s_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_String_bytes(lean_object* v_s_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_string_to_utf8(v_s_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii(lean_object* v_s_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_string_utf8_byte_size(v_s_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_String_lengthAssumingAscii___boxed(lean_object* v_s_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_String_lengthAssumingAscii(v_s_554_);
lean_dec_ref(v_s_554_);
return v_res_555_;
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
