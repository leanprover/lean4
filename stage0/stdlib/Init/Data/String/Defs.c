// Lean compiler output
// Module: Init.Data.String.Defs
// Imports: public import Init.Data.ByteArray.Basic public import Init.Data.String.PosRaw import Init.Data.ByteArray.Lemmas
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
LEAN_EXPORT lean_object* l_String_toSlice(lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_join(lean_object*);
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object*);
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_String_bytes(lean_object*);
static lean_object* l_String_instInhabitedSlice___closed__0;
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw;
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedSlice;
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startPos(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_instAppendString___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object*, lean_object*);
static lean_object* l_String_instHAddRawSlice___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_instHAddSliceRaw___closed__0;
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice;
LEAN_EXPORT lean_object* l_instAppendString;
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_string_isempty(lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object*);
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__2;
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_String_instHSubRawSlice___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedUInt8;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_instCoeSlice;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endPos(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object*, lean_object*);
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__3;
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object*, lean_object*);
static lean_object* l_String_instCoeSlice___closed__0;
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object*);
static lean_object* l_String_join___closed__0;
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__1;
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawSlice;
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_from_utf8_unchecked(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_from_utf8_unchecked(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_to_utf8(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_append(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_instAppendString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_append___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAppendString() {
_start:
{
lean_object* x_1; 
x_1 = l_instAppendString___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_rawStartPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_rawStartPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_pushn___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box_uint32(x_2);
x_5 = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), x_5, x_3, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_pushn(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_string_push(x_3, x_1);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_string_pushn(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isEmpty(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
lean_dec_ref(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_string_isempty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_String_join___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_instAppendString___closed__0;
x_3 = l_String_join___closed__0;
x_4 = l_List_foldl___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_string_append(x_1, x_2);
x_7 = lean_string_append(x_6, x_4);
x_1 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Defs_0__String_intercalate_go(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_join___closed__0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l___private_Init_Data_String_Defs_0__String_intercalate_go(x_4, x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_intercalate(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_intercalate(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableEqPos_decEq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableEqPos_decEq(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableEqPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableEqPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_startPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_startPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_startPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instInhabitedPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_endPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_endPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLEPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLTPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLePos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_le(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLePos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLtPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLtPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_String_instInhabitedSlice___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_join___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_instInhabitedSlice() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instInhabitedSlice___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_String_instCoeSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_toSlice), 1, 0);
return x_1;
}
}
static lean_object* _init_l_String_instCoeSlice() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instCoeSlice___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_utf8ByteSize(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_nat_sub(x_4, x_3);
x_6 = lean_nat_add(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddRawSlice___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_String_instHAddRawSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddRawSlice___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_String_instHAddRawSlice() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instHAddRawSlice___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_sub(x_4, x_3);
x_6 = lean_nat_add(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddSliceRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_String_instHAddSliceRaw___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddSliceRaw___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_String_instHAddSliceRaw() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instHAddSliceRaw___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_nat_sub(x_4, x_3);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHSubRawSlice___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_String_instHSubRawSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHSubRawSlice___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_String_instHSubRawSlice() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instHSubRawSlice___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_rawEndPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_string_get_byte_fast(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_getUTF8Byte___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_5, x_2);
x_7 = lean_string_get_byte_fast(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_getUTF8Byte(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_instInhabitedUInt8;
x_3 = lean_box(x_2);
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Defs", 21, 21);
return x_1;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Slice.getUTF8Byte!", 25, 25);
return x_1;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String slice access is out of bounds.", 37, 37);
return x_1;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_Slice_getUTF8Byte_x21___closed__2;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(504u);
x_4 = l_String_Slice_getUTF8Byte_x21___closed__1;
x_5 = l_String_Slice_getUTF8Byte_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_String_Slice_getUTF8Byte_x21___closed__3;
x_9 = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_nat_add(x_4, x_2);
x_11 = lean_string_get_byte_fast(x_3, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_getUTF8Byte_x21(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_instDecidableEqPos_decEq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_instDecidableEqPos_decEq(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_instDecidableEqPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_instDecidableEqPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_startPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instInhabitedPos__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_endPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLEPos__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLTPos__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLePos__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_le(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLePos__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLtPos__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLtPos__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableIsAtEnd(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsAtEnd__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_sub(x_4, x_3);
x_6 = lean_nat_dec_eq(x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsAtEnd__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableIsAtEnd__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_string_get_byte_fast(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pos_byte___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_5, x_2);
x_7 = lean_string_get_byte_fast(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_Pos_byte(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_toSubstring_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_startValidPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_endValidPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_String_bytes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_to_utf8(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_PosRaw(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instAppendString___closed__0 = _init_l_instAppendString___closed__0();
lean_mark_persistent(l_instAppendString___closed__0);
l_instAppendString = _init_l_instAppendString();
lean_mark_persistent(l_instAppendString);
l_String_join___closed__0 = _init_l_String_join___closed__0();
lean_mark_persistent(l_String_join___closed__0);
l_String_instInhabitedSlice___closed__0 = _init_l_String_instInhabitedSlice___closed__0();
lean_mark_persistent(l_String_instInhabitedSlice___closed__0);
l_String_instInhabitedSlice = _init_l_String_instInhabitedSlice();
lean_mark_persistent(l_String_instInhabitedSlice);
l_String_instCoeSlice___closed__0 = _init_l_String_instCoeSlice___closed__0();
lean_mark_persistent(l_String_instCoeSlice___closed__0);
l_String_instCoeSlice = _init_l_String_instCoeSlice();
lean_mark_persistent(l_String_instCoeSlice);
l_String_instHAddRawSlice___closed__0 = _init_l_String_instHAddRawSlice___closed__0();
lean_mark_persistent(l_String_instHAddRawSlice___closed__0);
l_String_instHAddRawSlice = _init_l_String_instHAddRawSlice();
lean_mark_persistent(l_String_instHAddRawSlice);
l_String_instHAddSliceRaw___closed__0 = _init_l_String_instHAddSliceRaw___closed__0();
lean_mark_persistent(l_String_instHAddSliceRaw___closed__0);
l_String_instHAddSliceRaw = _init_l_String_instHAddSliceRaw();
lean_mark_persistent(l_String_instHAddSliceRaw);
l_String_instHSubRawSlice___closed__0 = _init_l_String_instHSubRawSlice___closed__0();
lean_mark_persistent(l_String_instHSubRawSlice___closed__0);
l_String_instHSubRawSlice = _init_l_String_instHSubRawSlice();
lean_mark_persistent(l_String_instHSubRawSlice);
l_String_Slice_getUTF8Byte_x21___closed__0 = _init_l_String_Slice_getUTF8Byte_x21___closed__0();
lean_mark_persistent(l_String_Slice_getUTF8Byte_x21___closed__0);
l_String_Slice_getUTF8Byte_x21___closed__1 = _init_l_String_Slice_getUTF8Byte_x21___closed__1();
lean_mark_persistent(l_String_Slice_getUTF8Byte_x21___closed__1);
l_String_Slice_getUTF8Byte_x21___closed__2 = _init_l_String_Slice_getUTF8Byte_x21___closed__2();
lean_mark_persistent(l_String_Slice_getUTF8Byte_x21___closed__2);
l_String_Slice_getUTF8Byte_x21___closed__3 = _init_l_String_Slice_getUTF8Byte_x21___closed__3();
lean_mark_persistent(l_String_Slice_getUTF8Byte_x21___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
