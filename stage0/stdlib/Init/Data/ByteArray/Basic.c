// Lean compiler output
// Module: Init.Data.ByteArray.Basic
// Imports: Init.Data.Array.Basic Init.Data.Array.Subarray Init.Data.UInt.Basic Init.Data.Option.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__4;
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__1;
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6;
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at_ByteArray_toUInt64LE_x21___spec__1(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_atEnd___boxed(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_atEnd(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
static lean_object* l_List_toString___at_instToStringByteArray___spec__1___closed__2;
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_fset(lean_object*, lean_object*, uint8_t);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__10;
LEAN_EXPORT lean_object* l_ByteArray_mkIterator(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_mkEmpty___boxed(lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t lean_byte_array_hash(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__6;
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__20;
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__18;
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos(lean_object*);
static lean_object* l_List_foldl___at_instToStringByteArray___spec__2___closed__1;
LEAN_EXPORT uint8_t l_ByteArray_instGetElemUSizeUInt8LtNatValValSize(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__19;
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__3;
LEAN_EXPORT lean_object* l_ByteArray_append___boxed(lean_object*, lean_object*);
static lean_object* l_List_toString___at_instToStringByteArray___spec__1___closed__3;
static lean_object* l_ByteArray_toUInt64BE_x21___closed__1;
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_hash___boxed(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_ByteArray_toUInt64BE_x21___closed__2;
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasNext(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValValSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ByteArray_instHashable___closed__1;
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_byte_array_set(lean_object*, lean_object*, uint8_t);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__1;
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toByteArray_loop(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__13;
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_empty;
uint64_t lean_uint8_to_uint64(uint8_t);
size_t lean_sarray_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___rarg(lean_object*, lean_object*);
static uint8_t l_ByteArray_Iterator_curr___closed__1;
LEAN_EXPORT uint8_t l_ByteArray_instGetElemNatUInt8LtSize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop(lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toByteArray(lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__14;
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object*);
uint8_t lean_byte_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instInhabitedIterator;
LEAN_EXPORT lean_object* l_ByteArray_uget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_size___boxed(lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__5;
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__15;
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__12;
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object*);
static lean_object* l_ByteArray_instInhabitedIterator___closed__1;
static lean_object* l_ByteArray_empty___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringByteArray___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instHashable;
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140_;
LEAN_EXPORT lean_object* l_ByteArray_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_instToStringByteArray___spec__2(lean_object*, lean_object*);
static lean_object* l_List_toString___at_instToStringByteArray___spec__1___closed__1;
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__9;
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__8;
LEAN_EXPORT lean_object* l_ByteArray_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__11;
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringByteArray(lean_object*);
lean_object* lean_byte_array_data(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_558_;
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_uset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__21;
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__2;
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instGetElemNatUInt8LtSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_iter(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instInhabited;
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_push___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_473_;
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__5;
LEAN_EXPORT lean_object* l_ByteArray_instEmptyCollection;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__16;
static lean_object* l_ByteArray_instAppend___closed__1;
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instAppend;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* lean_byte_array_uset(lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21___boxed(lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22;
LEAN_EXPORT lean_object* l_ByteArray_foldl(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object*, lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__3;
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_268_;
LEAN_EXPORT lean_object* l_ByteArray_usize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasPrev(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__4;
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__7;
static lean_object* l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__17;
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1;
lean_object* lean_byte_array_size(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_instToStringByteArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_data___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_data(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_mkEmpty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_mk_empty_byte_array(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_ByteArray_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_byte_array(x_1);
return x_2;
}
}
static lean_object* _init_l_ByteArray_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_ByteArray_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
static lean_object* _init_l_ByteArray_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = lean_byte_array_push(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_size(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_usize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_sarray_size(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__1;
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__2;
x_3 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__3;
x_4 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__1;
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__2;
x_3 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__3;
x_4 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticGet_elem_tactic", 21, 21);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get_elem_tactic", 15, 15);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__13;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6;
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__12;
x_3 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__15;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6;
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__10;
x_3 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__17;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6;
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__8;
x_3 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__19;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6;
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__20;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__5;
x_3 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__21;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_uget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_byte_array_uget(x_1, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_byte_array_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_268_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_byte_array_fget(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instGetElemNatUInt8LtSize(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_byte_array_fget(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemNatUInt8LtSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ByteArray_instGetElemNatUInt8LtSize(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instGetElemUSizeUInt8LtNatValValSize(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_byte_array_uget(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValValSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_ByteArray_instGetElemUSizeUInt8LtNatValValSize(x_1, x_4, x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = lean_byte_array_set(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_473_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_byte_array_fset(x_1, x_2, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_558_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_uset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_byte_array_uset(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_byte_array_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_instHashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ByteArray_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_ByteArray_instHashable() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_instHashable___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_byte_array_copy_slice(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_nat_sub(x_3, x_2);
x_5 = l_ByteArray_empty;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 1;
x_8 = lean_byte_array_copy_slice(x_1, x_2, x_5, x_6, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_byte_array_copy_slice(x_2, x_5, x_1, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_append(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_instAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ByteArray_append___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_ByteArray_instAppend() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_instAppend___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_List_reverse___rarg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = lean_byte_array_get(x_1, x_2);
lean_dec(x_2);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_toList_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_ByteArray_toList_loop(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_toList(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_byte_array_get(x_1, x_3);
x_8 = lean_box(x_7);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f_loop(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
return x_10;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = l_ByteArray_forInUnsafe_loop___rarg(x_1, x_3, x_4, x_5, x_13, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_6);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_byte_array_uget(x_2, x_5);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_box(x_11);
lean_inc(x_3);
x_14 = lean_apply_2(x_3, x_13, x_6);
x_15 = lean_box_usize(x_5);
x_16 = lean_box_usize(x_4);
x_17 = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe_loop___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe_loop___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_ByteArray_forInUnsafe_loop___rarg___lambda__1(x_1, x_7, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_ByteArray_forInUnsafe_loop___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_sarray_size(x_2);
x_6 = 0;
x_7 = l_ByteArray_forInUnsafe_loop___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_ByteArray_forIn_loop___rarg(x_1, x_2, x_3, x_4, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_byte_array_size(x_2);
x_13 = lean_nat_sub(x_12, x_9);
lean_dec(x_12);
x_14 = lean_nat_sub(x_13, x_10);
lean_dec(x_13);
x_15 = lean_byte_array_fget(x_2, x_14);
lean_dec(x_14);
x_16 = lean_box(x_15);
lean_inc(x_3);
x_17 = lean_apply_2(x_3, x_16, x_6);
x_18 = lean_alloc_closure((void*)(l_ByteArray_forIn_loop___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_10);
x_19 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_6);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_forIn_loop___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ByteArray_forIn_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ByteArray_forIn_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_sarray_size(x_2);
x_6 = 0;
x_7 = l_ByteArray_forInUnsafe_loop___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_ByteArray_foldlMUnsafe_fold___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_byte_array_uget(x_3, x_4);
x_10 = lean_box(x_9);
lean_inc(x_2);
x_11 = lean_apply_2(x_2, x_6, x_10);
x_12 = lean_box_usize(x_4);
x_13 = lean_box_usize(x_5);
x_14 = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_ByteArray_foldlMUnsafe_fold___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_ByteArray_foldlMUnsafe_fold___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_byte_array_size(x_4);
x_12 = lean_nat_dec_le(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_5);
x_17 = lean_usize_of_nat(x_6);
x_18 = l_ByteArray_foldlMUnsafe_fold___rarg(x_1, x_2, x_4, x_16, x_17, x_3);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ByteArray_foldlMUnsafe___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
x_10 = l_ByteArray_foldlM_loop___rarg(x_2, x_3, x_4, x_5, lean_box(0), x_6, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_7, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_byte_array_fget(x_3, x_7);
x_19 = lean_box(x_18);
lean_inc(x_2);
x_20 = lean_apply_2(x_2, x_8, x_19);
x_21 = lean_alloc_closure((void*)(l_ByteArray_foldlM_loop___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_21, 0, x_7);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_16);
x_22 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_2(x_24, lean_box(0), x_8);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_foldlM_loop___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ByteArray_foldlM_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_ByteArray_foldlM_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_byte_array_uget(x_2, x_3);
x_8 = lean_box(x_7);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_byte_array_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ByteArray_foldl___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_ByteArray_foldlMUnsafe_fold___at_ByteArray_foldl___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ByteArray_foldl___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_instInhabitedIterator___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_mkIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_iter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_byte_array_size(x_2);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_instSizeOfIterator(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_Iterator_remainingBytes(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_Iterator_pos(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint8_t _init_l_ByteArray_Iterator_curr___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint8_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_ByteArray_Iterator_curr___closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_byte_array_fget(x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_Iterator_curr(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_atEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_le(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_atEnd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_Iterator_atEnd(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasNext(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_Iterator_hasNext(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_byte_array_fget(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ByteArray_Iterator_curr_x27(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasPrev(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_Iterator_hasPrev(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = lean_byte_array_size(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_byte_array_size(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_Iterator_forward(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_Iterator_nextn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_sub(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_nat_sub(x_7, x_2);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_Iterator_prevn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toByteArray_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_byte_array_push(x_2, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_empty;
x_3 = l_List_toByteArray_loop(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_foldl___at_instToStringByteArray___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_instToStringByteArray___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___at_instToStringByteArray___spec__2___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_uint8_to_nat(x_7);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_1 = x_10;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_List_toString___at_instToStringByteArray___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_instToStringByteArray___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_instToStringByteArray___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_instToStringByteArray___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_instToStringByteArray___spec__1___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_uint8_to_nat(x_5);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_8 = l_List_toString___at_instToStringByteArray___spec__1___closed__2;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_toString___at_instToStringByteArray___spec__1___closed__3;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = lean_uint8_to_nat(x_13);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_16 = l_List_toString___at_instToStringByteArray___spec__1___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_List_foldl___at_instToStringByteArray___spec__2(x_17, x_3);
x_19 = 93;
x_20 = lean_string_push(x_18, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_instToStringByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_toList(x_1);
x_3 = l_List_toString___at_instToStringByteArray___spec__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringByteArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringByteArray(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_instInhabitedUInt64;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_ByteArray_toUInt64LE_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bs.size == 8\n  ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__1;
x_2 = l_ByteArray_toUInt64LE_x21___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.ByteArray.Basic", 25, 25);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ByteArray.toUInt64LE!", 21, 21);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__4;
x_2 = l_ByteArray_toUInt64LE_x21___closed__5;
x_3 = lean_unsigned_to_nat(337u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_ByteArray_toUInt64LE_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_ByteArray_toUInt64LE_x21___closed__6;
x_6 = l_panic___at_ByteArray_toUInt64LE_x21___spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint8_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint8_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; 
x_7 = lean_unsigned_to_nat(7u);
x_8 = lean_byte_array_get(x_1, x_7);
x_9 = lean_uint8_to_uint64(x_8);
x_10 = 56;
x_11 = lean_uint64_shift_left(x_9, x_10);
x_12 = lean_unsigned_to_nat(6u);
x_13 = lean_byte_array_get(x_1, x_12);
x_14 = lean_uint8_to_uint64(x_13);
x_15 = 48;
x_16 = lean_uint64_shift_left(x_14, x_15);
x_17 = lean_uint64_lor(x_11, x_16);
x_18 = lean_unsigned_to_nat(5u);
x_19 = lean_byte_array_get(x_1, x_18);
x_20 = lean_uint8_to_uint64(x_19);
x_21 = 40;
x_22 = lean_uint64_shift_left(x_20, x_21);
x_23 = lean_uint64_lor(x_17, x_22);
x_24 = lean_unsigned_to_nat(4u);
x_25 = lean_byte_array_get(x_1, x_24);
x_26 = lean_uint8_to_uint64(x_25);
x_27 = 32;
x_28 = lean_uint64_shift_left(x_26, x_27);
x_29 = lean_uint64_lor(x_23, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_byte_array_get(x_1, x_30);
x_32 = lean_uint8_to_uint64(x_31);
x_33 = 24;
x_34 = lean_uint64_shift_left(x_32, x_33);
x_35 = lean_uint64_lor(x_29, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_byte_array_get(x_1, x_36);
x_38 = lean_uint8_to_uint64(x_37);
x_39 = 16;
x_40 = lean_uint64_shift_left(x_38, x_39);
x_41 = lean_uint64_lor(x_35, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_byte_array_get(x_1, x_42);
x_44 = lean_uint8_to_uint64(x_43);
x_45 = 8;
x_46 = lean_uint64_shift_left(x_44, x_45);
x_47 = lean_uint64_lor(x_41, x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_byte_array_get(x_1, x_48);
x_50 = lean_uint8_to_uint64(x_49);
x_51 = lean_uint64_lor(x_47, x_50);
x_52 = lean_box_uint64(x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_toUInt64LE_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_ByteArray_toUInt64BE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ByteArray.toUInt64BE!", 21, 21);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64BE_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__4;
x_2 = l_ByteArray_toUInt64BE_x21___closed__1;
x_3 = lean_unsigned_to_nat(349u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_ByteArray_toUInt64LE_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_ByteArray_toUInt64BE_x21___closed__2;
x_6 = l_panic___at_ByteArray_toUInt64LE_x21___spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint8_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint8_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_byte_array_get(x_1, x_7);
x_9 = lean_uint8_to_uint64(x_8);
x_10 = 56;
x_11 = lean_uint64_shift_left(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_byte_array_get(x_1, x_12);
x_14 = lean_uint8_to_uint64(x_13);
x_15 = 48;
x_16 = lean_uint64_shift_left(x_14, x_15);
x_17 = lean_uint64_lor(x_11, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_byte_array_get(x_1, x_18);
x_20 = lean_uint8_to_uint64(x_19);
x_21 = 40;
x_22 = lean_uint64_shift_left(x_20, x_21);
x_23 = lean_uint64_lor(x_17, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_byte_array_get(x_1, x_24);
x_26 = lean_uint8_to_uint64(x_25);
x_27 = 32;
x_28 = lean_uint64_shift_left(x_26, x_27);
x_29 = lean_uint64_lor(x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_byte_array_get(x_1, x_30);
x_32 = lean_uint8_to_uint64(x_31);
x_33 = 24;
x_34 = lean_uint64_shift_left(x_32, x_33);
x_35 = lean_uint64_lor(x_29, x_34);
x_36 = lean_unsigned_to_nat(5u);
x_37 = lean_byte_array_get(x_1, x_36);
x_38 = lean_uint8_to_uint64(x_37);
x_39 = 16;
x_40 = lean_uint64_shift_left(x_38, x_39);
x_41 = lean_uint64_lor(x_35, x_40);
x_42 = lean_unsigned_to_nat(6u);
x_43 = lean_byte_array_get(x_1, x_42);
x_44 = lean_uint8_to_uint64(x_43);
x_45 = 8;
x_46 = lean_uint64_shift_left(x_44, x_45);
x_47 = lean_uint64_lor(x_41, x_46);
x_48 = lean_unsigned_to_nat(7u);
x_49 = lean_byte_array_get(x_1, x_48);
x_50 = lean_uint8_to_uint64(x_49);
x_51 = lean_uint64_lor(x_47, x_50);
x_52 = lean_box_uint64(x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_toUInt64BE_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ByteArray_empty___closed__1 = _init_l_ByteArray_empty___closed__1();
lean_mark_persistent(l_ByteArray_empty___closed__1);
l_ByteArray_empty = _init_l_ByteArray_empty();
lean_mark_persistent(l_ByteArray_empty);
l_ByteArray_instInhabited = _init_l_ByteArray_instInhabited();
lean_mark_persistent(l_ByteArray_instInhabited);
l_ByteArray_instEmptyCollection = _init_l_ByteArray_instEmptyCollection();
lean_mark_persistent(l_ByteArray_instEmptyCollection);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__1 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__1();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__1);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__2 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__2();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__2);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__3 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__3();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__3);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__4 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__4();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__4);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__5 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__5();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__5);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__6);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__7 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__7();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__7);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__8 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__8();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__8);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__9 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__9();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__9);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__10 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__10();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__10);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__11 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__11();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__11);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__12 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__12();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__12);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__13 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__13();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__13);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__14 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__14();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__14);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__15 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__15();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__15);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__16 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__16();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__16);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__17 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__17();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__17);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__18 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__18();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__18);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__19 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__19();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__19);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__20 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__20();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__20);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__21 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__21();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__21);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22 = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140____closed__22);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_140_ = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_140_();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_140_);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_268_ = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_268_();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_268_);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_473_ = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_473_();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_473_);
l___auto____x40_Init_Data_ByteArray_Basic___hyg_558_ = _init_l___auto____x40_Init_Data_ByteArray_Basic___hyg_558_();
lean_mark_persistent(l___auto____x40_Init_Data_ByteArray_Basic___hyg_558_);
l_ByteArray_instHashable___closed__1 = _init_l_ByteArray_instHashable___closed__1();
lean_mark_persistent(l_ByteArray_instHashable___closed__1);
l_ByteArray_instHashable = _init_l_ByteArray_instHashable();
lean_mark_persistent(l_ByteArray_instHashable);
l_ByteArray_instAppend___closed__1 = _init_l_ByteArray_instAppend___closed__1();
lean_mark_persistent(l_ByteArray_instAppend___closed__1);
l_ByteArray_instAppend = _init_l_ByteArray_instAppend();
lean_mark_persistent(l_ByteArray_instAppend);
l_ByteArray_instInhabitedIterator___closed__1 = _init_l_ByteArray_instInhabitedIterator___closed__1();
lean_mark_persistent(l_ByteArray_instInhabitedIterator___closed__1);
l_ByteArray_instInhabitedIterator = _init_l_ByteArray_instInhabitedIterator();
lean_mark_persistent(l_ByteArray_instInhabitedIterator);
l_ByteArray_Iterator_curr___closed__1 = _init_l_ByteArray_Iterator_curr___closed__1();
l_List_foldl___at_instToStringByteArray___spec__2___closed__1 = _init_l_List_foldl___at_instToStringByteArray___spec__2___closed__1();
lean_mark_persistent(l_List_foldl___at_instToStringByteArray___spec__2___closed__1);
l_List_toString___at_instToStringByteArray___spec__1___closed__1 = _init_l_List_toString___at_instToStringByteArray___spec__1___closed__1();
lean_mark_persistent(l_List_toString___at_instToStringByteArray___spec__1___closed__1);
l_List_toString___at_instToStringByteArray___spec__1___closed__2 = _init_l_List_toString___at_instToStringByteArray___spec__1___closed__2();
lean_mark_persistent(l_List_toString___at_instToStringByteArray___spec__1___closed__2);
l_List_toString___at_instToStringByteArray___spec__1___closed__3 = _init_l_List_toString___at_instToStringByteArray___spec__1___closed__3();
lean_mark_persistent(l_List_toString___at_instToStringByteArray___spec__1___closed__3);
l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1 = _init_l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1();
lean_mark_persistent(l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1);
l_ByteArray_toUInt64LE_x21___closed__1 = _init_l_ByteArray_toUInt64LE_x21___closed__1();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__1);
l_ByteArray_toUInt64LE_x21___closed__2 = _init_l_ByteArray_toUInt64LE_x21___closed__2();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__2);
l_ByteArray_toUInt64LE_x21___closed__3 = _init_l_ByteArray_toUInt64LE_x21___closed__3();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__3);
l_ByteArray_toUInt64LE_x21___closed__4 = _init_l_ByteArray_toUInt64LE_x21___closed__4();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__4);
l_ByteArray_toUInt64LE_x21___closed__5 = _init_l_ByteArray_toUInt64LE_x21___closed__5();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__5);
l_ByteArray_toUInt64LE_x21___closed__6 = _init_l_ByteArray_toUInt64LE_x21___closed__6();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__6);
l_ByteArray_toUInt64BE_x21___closed__1 = _init_l_ByteArray_toUInt64BE_x21___closed__1();
lean_mark_persistent(l_ByteArray_toUInt64BE_x21___closed__1);
l_ByteArray_toUInt64BE_x21___closed__2 = _init_l_ByteArray_toUInt64BE_x21___closed__2();
lean_mark_persistent(l_ByteArray_toUInt64BE_x21___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
