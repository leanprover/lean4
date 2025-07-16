// Lean compiler output
// Module: Lean.Data.Json.Basic
// Imports: Init.Data.Range Init.Data.OfScientific Init.Data.Hashable Lean.Data.RBMap Init.Data.ToString.Macro
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
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__0;
uint8_t lean_float_isinf(double);
static lean_object* l_Lean_JsonNumber_normalize___closed__3;
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instDecidableLt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object*);
static double l_Lean_JsonNumber_fromFloat_x3f___closed__2;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
double lean_float_mul(double, double);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instCoeInt;
LEAN_EXPORT uint64_t l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t, lean_object*);
static lean_object* l_Lean_JsonNumber_toString___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instInhabited;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getArrVal_x3f___closed__0;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_JsonNumber_toString_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instBEq;
static lean_object* l_Lean_JsonNumber_normalize___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getArr_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_setObjVal_x21___closed__2;
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRBNodeStringStructured;
uint8_t lean_float_decLt(double, double);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg;
static lean_object* l_Lean_JsonNumber_toString___closed__2;
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Lean_Json_getArr_x3f___closed__0;
LEAN_EXPORT lean_object* l_panic___at___Lean_Json_setObjVal_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedJson;
static lean_object* l_Lean_Json_getObjVal_x3f___closed__0;
static lean_object* l_Lean_Json_getStr_x3f___closed__0;
static lean_object* l_Lean_Json_getNat_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2;
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__8;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(lean_object*);
double lean_float_negate(double);
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object*, lean_object*);
static uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hashJsonNumber____x40_Lean_Data_Json_Basic___hyg_173____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object*);
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__6;
static uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2;
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instOrd___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object*);
static lean_object* l_Lean_Json_getNat_x3f___closed__0;
static lean_object* l_Lean_Json_instBEq___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
static lean_object* l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_JsonNumber_toString___closed__4;
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObj_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getInt_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object*);
static lean_object* l_Lean_Json_setObjVal_x21___closed__1;
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object*);
static lean_object* l_Lean_Json_setObjVal_x21___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Json_getStr_x3f___closed__1;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_isnan(double);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_hashJsonNumber____x40_Lean_Data_Json_Basic___hyg_173_(lean_object*);
static lean_object* l_Lean_JsonNumber_instInhabited___closed__0;
static lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object*);
static lean_object* l_Lean_Json_getBool_x3f___closed__1;
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObj_x3f___closed__1;
static double l_Lean_JsonNumber_fromFloat_x3f___closed__0;
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRBNodeStringStructured___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_28____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_JsonNumber_toString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object*);
static lean_object* l_Lean_Json_getArrVal_x3f___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableJsonNumber;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_float_to_string(double);
static uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instCoeNat;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_instHashable;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_beq(double, double);
static lean_object* l_Lean_JsonNumber_toString___closed__0;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getNum_x3f___closed__1;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static double l_Lean_JsonNumber_toFloat___closed__1;
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_ltProp;
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_normalize___closed__2;
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat;
static lean_object* l_Lean_Json_getObjVal_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__3;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_normalize___closed__1;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getNum_x3f___closed__0;
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instToString;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static double l_Lean_JsonNumber_toFloat___closed__0;
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object*);
static lean_object* l_Lean_Json_instHashable___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_28_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_instCoeNat___closed__0;
static lean_object* l_Lean_Json_getInt_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_toString___closed__1;
static lean_object* l_Lean_JsonNumber_instCoeInt___closed__0;
LEAN_EXPORT uint8_t l_Lean_instDecidableEqJsonNumber(lean_object*, lean_object*);
static lean_object* l_Lean_JsonNumber_instToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString;
static lean_object* l_Lean_Json_getBool_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object*);
static lean_object* l_Lean_instHashableJsonNumber___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_mergeObj_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_28_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_int_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_28____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_28_(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqJsonNumber(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_28_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instDecidableEqJsonNumber(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_hashJsonNumber____x40_Lean_Data_Json_Basic___hyg_173_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; lean_object* x_10; uint8_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 0;
x_10 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_11 = lean_int_dec_lt(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; 
x_12 = lean_nat_abs(x_2);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_mul(x_13, x_12);
lean_dec(x_12);
x_15 = lean_uint64_of_nat(x_14);
lean_dec(x_14);
x_5 = x_15;
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; 
x_16 = lean_nat_abs(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_mul(x_19, x_18);
lean_dec(x_18);
x_21 = lean_nat_add(x_20, x_17);
lean_dec(x_20);
x_22 = lean_uint64_of_nat(x_21);
lean_dec(x_21);
x_5 = x_22;
goto block_9;
}
block_9:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_of_nat(x_3);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hashJsonNumber____x40_Lean_Data_Json_Basic___hyg_173____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_hashJsonNumber____x40_Lean_Data_Json_Basic___hyg_173_(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableJsonNumber___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashJsonNumber____x40_Lean_Data_Json_Basic___hyg_173____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableJsonNumber() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableJsonNumber___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_nat_to_int(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromInt(lean_object* x_1) {
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
static lean_object* _init_l_Lean_JsonNumber_instCoeNat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_fromNat), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instCoeNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_instCoeNat___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instCoeInt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_fromInt), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instCoeInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_instCoeInt___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(9u);
x_4 = lean_nat_dec_le(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(10u);
x_6 = lean_nat_div(x_1, x_5);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(10u);
x_6 = lean_nat_mod(x_3, x_5);
x_7 = lean_nat_dec_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_nat_div(x_3, x_5);
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_dec_lt(x_10, x_2);
if (x_11 == 0)
{
lean_dec(x_10);
return x_8;
}
else
{
x_3 = x_8;
x_4 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___redArg(x_1, x_6, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_normalize___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonNumber_normalize___closed__2;
x_2 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_normalize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_15; lean_object* x_16; lean_object* x_22; uint8_t x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_15 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_23 = lean_int_dec_eq(x_2, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_int_dec_lt(x_22, x_2);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Lean_JsonNumber_normalize___closed__1;
x_16 = x_25;
goto block_21;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_JsonNumber_normalize___closed__0;
x_16 = x_26;
goto block_21;
}
}
else
{
lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Lean_JsonNumber_normalize___closed__3;
return x_27;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_nat_to_int(x_3);
x_9 = lean_int_neg(x_8);
lean_dec(x_8);
x_10 = lean_nat_to_int(x_6);
x_11 = lean_int_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_4)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_4;
}
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
block_21:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_nat_abs(x_2);
lean_dec(x_2);
lean_inc(x_17);
x_18 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(x_17);
x_19 = lean_nat_dec_lt(x_15, x_18);
if (x_19 == 0)
{
x_5 = x_16;
x_6 = x_18;
x_7 = x_17;
goto block_14;
}
else
{
lean_object* x_20; 
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___redArg(x_15, x_18, x_17, x_15);
x_5 = x_16;
x_6 = x_18;
x_7 = x_20;
goto block_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_JsonNumber_normalize_spec__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_30 = l_Lean_JsonNumber_normalize(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_JsonNumber_normalize(x_2);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_42 = l_Lean_JsonNumber_normalize___closed__0;
x_43 = l_Lean_JsonNumber_normalize___closed__1;
x_44 = lean_int_dec_eq(x_31, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = lean_int_dec_eq(x_31, x_42);
if (x_45 == 0)
{
goto block_41;
}
else
{
uint8_t x_46; 
x_46 = lean_int_dec_eq(x_34, x_43);
if (x_46 == 0)
{
goto block_41;
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
return x_44;
}
}
}
else
{
uint8_t x_47; 
x_47 = lean_int_dec_eq(x_34, x_42);
if (x_47 == 0)
{
goto block_41;
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
return x_47;
}
}
block_10:
{
if (x_4 == 0)
{
uint8_t x_8; 
x_8 = lean_int_dec_lt(x_5, x_3);
lean_dec(x_3);
lean_dec(x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_4;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_4;
}
}
block_29:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec_ref(x_12);
lean_inc(x_13);
x_17 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(x_13);
lean_inc(x_15);
x_18 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(x_15);
x_19 = lean_int_dec_lt(x_14, x_16);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_unsigned_to_nat(10u);
x_22 = lean_nat_sub(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_nat_pow(x_21, x_22);
lean_dec(x_22);
x_24 = lean_nat_mul(x_15, x_23);
lean_dec(x_23);
lean_dec(x_15);
x_3 = x_14;
x_4 = x_19;
x_5 = x_16;
x_6 = x_13;
x_7 = x_24;
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_unsigned_to_nat(10u);
x_26 = lean_nat_sub(x_18, x_17);
lean_dec(x_17);
lean_dec(x_18);
x_27 = lean_nat_pow(x_25, x_26);
lean_dec(x_26);
x_28 = lean_nat_mul(x_13, x_27);
lean_dec(x_27);
lean_dec(x_13);
x_3 = x_14;
x_4 = x_19;
x_5 = x_16;
x_6 = x_28;
x_7 = x_15;
goto block_10;
}
}
block_37:
{
if (x_36 == 0)
{
x_11 = x_32;
x_12 = x_35;
goto block_29;
}
else
{
x_11 = x_35;
x_12 = x_32;
goto block_29;
}
}
block_41:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_JsonNumber_normalize___closed__1;
x_39 = lean_int_dec_eq(x_31, x_38);
lean_dec(x_31);
if (x_39 == 0)
{
lean_dec(x_34);
x_36 = x_39;
goto block_37;
}
else
{
uint8_t x_40; 
x_40 = lean_int_dec_eq(x_34, x_38);
lean_dec(x_34);
x_36 = x_40;
goto block_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonNumber_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonNumber_ltProp() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instDecidableLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_JsonNumber_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonNumber_instDecidableLt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instOrd___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = l_Lean_JsonNumber_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_JsonNumber_lt(x_2, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
}
else
{
uint8_t x_7; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = 0;
return x_7;
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonNumber_instOrd___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_JsonNumber_toString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_6 = lean_string_utf8_get(x_1, x_5);
x_7 = 48;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("e", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_36; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_13, x_14);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_51; uint8_t x_61; 
x_37 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_61 = lean_int_dec_le(x_37, x_12);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_JsonNumber_toString___closed__4;
x_51 = x_62;
goto block_60;
}
else
{
lean_object* x_63; 
x_63 = l_Lean_JsonNumber_toString___closed__2;
x_51 = x_63;
goto block_60;
}
block_50:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; 
x_41 = lean_unsigned_to_nat(10u);
x_42 = lean_nat_abs(x_40);
x_43 = lean_nat_sub(x_13, x_42);
lean_dec(x_42);
lean_dec(x_13);
x_44 = lean_nat_pow(x_41, x_43);
lean_dec(x_43);
x_45 = lean_nat_div(x_39, x_44);
x_46 = l_Nat_reprFast(x_45);
x_47 = lean_int_dec_eq(x_40, x_37);
x_48 = lean_nat_mod(x_39, x_44);
lean_dec(x_39);
x_49 = lean_nat_dec_eq(x_48, x_14);
if (x_49 == 0)
{
x_15 = x_38;
x_16 = x_40;
x_17 = x_48;
x_18 = x_46;
x_19 = x_47;
x_20 = x_44;
x_21 = x_49;
goto block_35;
}
else
{
x_15 = x_38;
x_16 = x_40;
x_17 = x_48;
x_18 = x_46;
x_19 = x_47;
x_20 = x_44;
x_21 = x_47;
goto block_35;
}
}
block_60:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_nat_abs(x_12);
lean_dec(x_12);
x_53 = l_Lean_JsonNumber_toString___closed__3;
lean_inc(x_52);
x_54 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(x_52);
x_55 = lean_nat_to_int(x_54);
x_56 = lean_int_add(x_53, x_55);
lean_dec(x_55);
lean_inc(x_13);
x_57 = lean_nat_to_int(x_13);
x_58 = lean_int_sub(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
x_59 = lean_int_dec_lt(x_58, x_37);
if (x_59 == 0)
{
lean_dec(x_58);
x_38 = x_51;
x_39 = x_52;
x_40 = x_37;
goto block_50;
}
else
{
x_38 = x_51;
x_39 = x_52;
x_40 = x_58;
goto block_50;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_13);
x_64 = l_Int_repr(x_12);
lean_dec(x_12);
return x_64;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_string_append(x_2, x_3);
lean_dec_ref(x_3);
x_7 = l_Lean_JsonNumber_toString___closed__0;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_4);
lean_dec_ref(x_4);
x_10 = lean_string_append(x_9, x_5);
lean_dec_ref(x_5);
return x_10;
}
block_35:
{
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_nat_add(x_20, x_17);
lean_dec(x_17);
lean_dec(x_20);
x_23 = l_Nat_reprFast(x_22);
x_24 = lean_string_utf8_byte_size(x_23);
lean_inc(x_24);
lean_inc_ref(x_23);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_Substring_nextn(x_25, x_26, x_14);
lean_dec_ref(x_25);
x_28 = l_Substring_takeRightWhileAux___at___Lean_JsonNumber_toString_spec__0(x_23, x_27, x_24);
x_29 = lean_string_utf8_extract(x_23, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_23);
if (x_19 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_JsonNumber_toString___closed__1;
x_31 = l_Int_repr(x_16);
lean_dec(x_16);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_2 = x_15;
x_3 = x_18;
x_4 = x_29;
x_5 = x_32;
goto block_11;
}
else
{
lean_object* x_33; 
lean_dec(x_16);
x_33 = l_Lean_JsonNumber_toString___closed__2;
x_2 = x_15;
x_3 = x_18;
x_4 = x_29;
x_5 = x_33;
goto block_11;
}
}
else
{
lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_34 = lean_string_append(x_15, x_18);
lean_dec_ref(x_18);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_JsonNumber_toString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lean_JsonNumber_toString_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(10u);
x_7 = lean_nat_sub(x_2, x_5);
x_8 = lean_nat_pow(x_6, x_7);
lean_dec(x_7);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_int_mul(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_5, x_2);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(10u);
x_15 = lean_nat_sub(x_2, x_13);
x_16 = lean_nat_pow(x_14, x_15);
lean_dec(x_15);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_mul(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_19 = lean_nat_sub(x_13, x_2);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonNumber_shiftl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonNumber_shiftr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonNumber_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_instToString___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟨", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_instRepr___lam__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟩", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_instRepr___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_instRepr___lam__0___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_23 = lean_int_dec_lt(x_3, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Int_repr(x_3);
lean_dec(x_3);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_6 = x_25;
goto block_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Int_repr(x_3);
lean_dec(x_3);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Repr_addAppParen(x_27, x_21);
x_6 = x_28;
goto block_20;
}
block_20:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_7 = l_Lean_JsonNumber_instRepr___lam__0___closed__2;
if (lean_is_scalar(x_5)) {
 x_8 = lean_alloc_ctor(5, 2, 0);
} else {
 x_8 = x_5;
 lean_ctor_set_tag(x_8, 5);
}
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Nat_reprFast(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_JsonNumber_normalize___closed__0;
x_13 = l_Lean_JsonNumber_instRepr___lam__0___closed__4;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_Lean_JsonNumber_instRepr___lam__0___closed__5;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = 0;
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
return x_19;
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_instRepr___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonNumber_instRepr___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_nat_pow(x_4, x_3);
lean_dec(x_3);
x_6 = lean_nat_mul(x_1, x_5);
lean_dec(x_5);
lean_dec(x_1);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_to_int(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instOfScientific() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_instOfScientific___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_JsonNumber_instOfScientific___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_int_neg(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_int_neg(x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instNeg() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonNumber_instNeg___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonNumber_instInhabited___closed__0;
return x_1;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(10u);
x_4 = l_Float_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__1() {
_start:
{
double x_1; double x_2; 
x_1 = l_Lean_JsonNumber_toFloat___closed__0;
x_2 = lean_float_negate(x_1);
return x_2;
}
}
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; double x_4; lean_object* x_10; uint8_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_10 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_11 = lean_int_dec_le(x_10, x_2);
if (x_11 == 0)
{
double x_12; 
x_12 = l_Lean_JsonNumber_toFloat___closed__1;
x_4 = x_12;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; double x_15; 
x_13 = lean_unsigned_to_nat(10u);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Float_ofScientific(x_13, x_11, x_14);
x_4 = x_15;
goto block_9;
}
block_9:
{
lean_object* x_5; uint8_t x_6; double x_7; double x_8; 
x_5 = lean_nat_abs(x_2);
lean_dec(x_2);
x_6 = 1;
x_7 = l_Float_ofScientific(x_5, x_6, x_3);
lean_dec(x_5);
x_8 = lean_float_mul(x_4, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_toFloat(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_instInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Data.Json.Basic", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Data.Json.Basic.0.Lean.JsonNumber.fromPositiveFloat!", 66, 66);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to parse ", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_float_to_string(x_1);
x_3 = l_Lean_Syntax_decodeScientificLitVal_x3f(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0;
x_5 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1;
x_6 = lean_unsigned_to_nat(152u);
x_7 = lean_unsigned_to_nat(12u);
x_8 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2;
x_9 = lean_string_append(x_8, x_2);
lean_dec_ref(x_2);
x_10 = l_mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_9);
lean_dec_ref(x_9);
x_11 = l_panic___at_____private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_pow(x_20, x_18);
lean_dec(x_18);
x_22 = lean_nat_mul(x_16, x_21);
lean_dec(x_21);
lean_dec(x_16);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_unsigned_to_nat(10u);
x_27 = lean_nat_pow(x_26, x_25);
lean_dec(x_25);
x_28 = lean_nat_mul(x_16, x_27);
lean_dec(x_27);
lean_dec(x_16);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_13, 0);
lean_dec(x_34);
x_35 = lean_nat_to_int(x_32);
lean_ctor_set(x_13, 0, x_35);
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_nat_to_int(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(x_2);
return x_3;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_instInhabited___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Infinity", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_fromFloat_x3f___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Infinity", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_fromFloat_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NaN", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_fromFloat_x3f___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_float_isnan(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_float_isinf(x_1);
if (x_3 == 0)
{
double x_4; uint8_t x_5; 
x_4 = l_Lean_JsonNumber_fromFloat_x3f___closed__0;
x_5 = lean_float_beq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_float_decLt(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
double x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_float_negate(x_1);
x_10 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_int_neg(x_15);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
x_20 = l_Lean_JsonNumber_fromFloat_x3f___closed__1;
return x_20;
}
}
else
{
double x_21; uint8_t x_22; 
x_21 = l_Lean_JsonNumber_fromFloat_x3f___closed__2;
x_22 = lean_float_decLt(x_21, x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_JsonNumber_fromFloat_x3f___closed__4;
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_JsonNumber_fromFloat_x3f___closed__6;
return x_24;
}
}
}
else
{
lean_object* x_25; 
x_25 = l_Lean_JsonNumber_fromFloat_x3f___closed__8;
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = l_Lean_JsonNumber_fromFloat_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_strLt(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget(x_1, x_7);
x_9 = lean_array_fget(x_2, x_7);
x_10 = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_string_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(x_1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_1, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_RBNode_all___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(x_1, x_4);
if (x_12 == 0)
{
return x_12;
}
else
{
x_2 = x_7;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, 0);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_2, 0);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
return x_5;
}
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, 0);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_28_(x_10, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_string_dec_eq(x_14, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_array_get_size(x_18);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(x_18, x_19, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
default: 
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(x_27, x_25);
x_29 = l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(x_27, x_26);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (x_30 == 0)
{
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Lean_RBNode_all___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(x_26, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_all___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_instBEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Json_instBEq___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint64_t l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(x_1, x_3);
x_8 = lean_string_hash(x_4);
x_9 = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(x_5);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0() {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = 13;
x_2 = lean_uint64_mix_hash(x_1, x_1);
return x_2;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 11;
x_2 = 13;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 7;
x_2 = 23;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = 11;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 0);
if (x_3 == 0)
{
uint64_t x_4; 
x_4 = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0;
return x_4;
}
else
{
uint64_t x_5; 
x_5 = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1;
return x_5;
}
}
case 2:
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 17;
x_8 = l_Lean_hashJsonNumber____x40_Lean_Data_Json_Basic___hyg_173_(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
case 3:
{
lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = 19;
x_12 = lean_string_hash(x_10);
x_13 = lean_uint64_mix_hash(x_11, x_12);
return x_13;
}
case 4:
{
lean_object* x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = 23;
x_16 = 7;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_14);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
uint64_t x_20; 
lean_dec(x_18);
x_20 = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
uint64_t x_22; 
lean_dec(x_18);
x_22 = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2;
return x_22;
}
else
{
size_t x_23; size_t x_24; uint64_t x_25; uint64_t x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(x_14, x_23, x_24, x_16);
x_26 = lean_uint64_mix_hash(x_15, x_25);
return x_26;
}
}
}
default: 
{
lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = 29;
x_29 = 7;
x_30 = l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(x_29, x_27);
x_31 = lean_uint64_mix_hash(x_28, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_RBNode_fold___at_____private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_instHashable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_instHashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Json_instHashable___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0(x_2, x_9);
switch (x_12) {
case 0:
{
lean_object* x_13; 
x_13 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
case 1:
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_19 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0(x_2, x_16);
switch (x_19) {
case 0:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_15, x_2, x_3);
x_21 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_6);
return x_21;
}
case 1:
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_18, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_29 = x_1;
} else {
 lean_dec_ref(x_1);
 x_29 = lean_box(0);
}
x_30 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0(x_2, x_26);
switch (x_30) {
case 0:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_25, x_2, x_3);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*4);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc(x_36);
if (x_32 == 0)
{
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_51; 
lean_dec(x_29);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_31, 3);
lean_dec(x_52);
x_53 = lean_ctor_get(x_31, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_31, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_31, 0);
lean_dec(x_55);
lean_ctor_set(x_31, 0, x_36);
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_31);
lean_ctor_set(x_56, 1, x_26);
lean_ctor_set(x_56, 2, x_27);
lean_ctor_set(x_56, 3, x_28);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_6);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_31);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_36);
lean_ctor_set(x_57, 1, x_34);
lean_ctor_set(x_57, 2, x_35);
lean_ctor_set(x_57, 3, x_36);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_26);
lean_ctor_set(x_58, 2, x_27);
lean_ctor_set(x_58, 3, x_28);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_6);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_31);
x_60 = lean_ctor_get(x_36, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_36, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_36, 3);
lean_inc(x_63);
lean_dec(x_36);
x_37 = x_33;
x_38 = x_34;
x_39 = x_35;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
uint8_t x_64; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
x_64 = !lean_is_exclusive(x_36);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_36, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_36, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_36, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_36, 0);
lean_dec(x_68);
lean_ctor_set(x_36, 3, x_28);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_6);
return x_36;
}
else
{
lean_object* x_69; 
lean_dec(x_36);
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_31);
lean_ctor_set(x_69, 1, x_26);
lean_ctor_set(x_69, 2, x_27);
lean_ctor_set(x_69, 3, x_28);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_6);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
x_70 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_31);
x_71 = lean_ctor_get(x_33, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_33, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_33, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_33, 3);
lean_inc(x_74);
lean_dec(x_33);
x_37 = x_71;
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_34;
x_42 = x_35;
x_43 = x_36;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_75; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
x_75 = !lean_is_exclusive(x_33);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_33, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_33, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_33, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_33, 0);
lean_dec(x_79);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_6);
return x_33;
}
else
{
lean_object* x_80; 
lean_dec(x_33);
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_31);
lean_ctor_set(x_80, 1, x_26);
lean_ctor_set(x_80, 2, x_27);
lean_ctor_set(x_80, 3, x_28);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_6);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_31);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_31, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_31, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_31, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_31, 0);
lean_dec(x_85);
x_86 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_free_object(x_31);
x_87 = lean_ctor_get(x_36, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_36, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_36, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_36, 3);
lean_inc(x_90);
lean_dec(x_36);
x_37 = x_33;
x_38 = x_34;
x_39 = x_35;
x_40 = x_87;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
uint8_t x_91; 
lean_dec(x_29);
x_91 = !lean_is_exclusive(x_33);
if (x_91 == 0)
{
lean_object* x_92; 
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_86);
x_92 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_28);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_6);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_33, 0);
x_94 = lean_ctor_get(x_33, 1);
x_95 = lean_ctor_get(x_33, 2);
x_96 = lean_ctor_get(x_33, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_33);
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_86);
lean_ctor_set(x_31, 0, x_97);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_31);
lean_ctor_set(x_98, 1, x_26);
lean_ctor_set(x_98, 2, x_27);
lean_ctor_set(x_98, 3, x_28);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_6);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_31);
x_99 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_36, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_36, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_36, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_36, 3);
lean_inc(x_103);
lean_dec(x_36);
x_37 = x_33;
x_38 = x_34;
x_39 = x_35;
x_40 = x_100;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_29);
x_104 = lean_ctor_get(x_33, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_33, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_33, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_33, 3);
lean_inc(x_107);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_108 = x_33;
} else {
 lean_dec_ref(x_33);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_99);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_34);
lean_ctor_set(x_110, 2, x_35);
lean_ctor_set(x_110, 3, x_36);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_32);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_26);
lean_ctor_set(x_111, 2, x_27);
lean_ctor_set(x_111, 3, x_28);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_6);
return x_111;
}
}
}
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_31);
lean_ctor_set(x_112, 1, x_26);
lean_ctor_set(x_112, 2, x_27);
lean_ctor_set(x_112, 3, x_28);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_6);
return x_112;
}
block_50:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
if (lean_is_scalar(x_29)) {
 x_47 = lean_alloc_ctor(1, 4, 1);
} else {
 x_47 = x_29;
}
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_47, 2, x_39);
lean_ctor_set(x_47, 3, x_40);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_6);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_6);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_42);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_32);
return x_49;
}
}
case 1:
{
lean_object* x_113; 
lean_dec(x_27);
lean_dec(x_26);
if (lean_is_scalar(x_29)) {
 x_113 = lean_alloc_ctor(1, 4, 1);
} else {
 x_113 = x_29;
}
lean_ctor_set(x_113, 0, x_25);
lean_ctor_set(x_113, 1, x_2);
lean_ctor_set(x_113, 2, x_3);
lean_ctor_set(x_113, 3, x_28);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_6);
return x_113;
}
default: 
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_114 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_28, x_2, x_3);
x_115 = lean_ctor_get_uint8(x_114, sizeof(void*)*4);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 3);
lean_inc(x_119);
if (x_115 == 0)
{
if (lean_obj_tag(x_116) == 0)
{
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_134; 
lean_dec(x_29);
x_134 = !lean_is_exclusive(x_114);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_114, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_114, 2);
lean_dec(x_136);
x_137 = lean_ctor_get(x_114, 1);
lean_dec(x_137);
x_138 = lean_ctor_get(x_114, 0);
lean_dec(x_138);
lean_ctor_set(x_114, 0, x_119);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_25);
lean_ctor_set(x_139, 1, x_26);
lean_ctor_set(x_139, 2, x_27);
lean_ctor_set(x_139, 3, x_114);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_6);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_114);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_119);
lean_ctor_set(x_140, 1, x_117);
lean_ctor_set(x_140, 2, x_118);
lean_ctor_set(x_140, 3, x_119);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_25);
lean_ctor_set(x_141, 1, x_26);
lean_ctor_set(x_141, 2, x_27);
lean_ctor_set(x_141, 3, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_6);
return x_141;
}
}
else
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_119, sizeof(void*)*4);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_114);
x_143 = lean_ctor_get(x_119, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_119, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_119, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_119, 3);
lean_inc(x_146);
lean_dec(x_119);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_116;
x_124 = x_117;
x_125 = x_118;
x_126 = x_143;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
goto block_133;
}
else
{
uint8_t x_147; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_29);
x_147 = !lean_is_exclusive(x_119);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_119, 3);
lean_dec(x_148);
x_149 = lean_ctor_get(x_119, 2);
lean_dec(x_149);
x_150 = lean_ctor_get(x_119, 1);
lean_dec(x_150);
x_151 = lean_ctor_get(x_119, 0);
lean_dec(x_151);
lean_ctor_set(x_119, 3, x_114);
lean_ctor_set(x_119, 2, x_27);
lean_ctor_set(x_119, 1, x_26);
lean_ctor_set(x_119, 0, x_25);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_6);
return x_119;
}
else
{
lean_object* x_152; 
lean_dec(x_119);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_25);
lean_ctor_set(x_152, 1, x_26);
lean_ctor_set(x_152, 2, x_27);
lean_ctor_set(x_152, 3, x_114);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_6);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
x_153 = lean_ctor_get_uint8(x_116, sizeof(void*)*4);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_114);
x_154 = lean_ctor_get(x_116, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_116, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_116, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_116, 3);
lean_inc(x_157);
lean_dec(x_116);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_154;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_117;
x_128 = x_118;
x_129 = x_119;
goto block_133;
}
else
{
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_158; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_29);
x_158 = !lean_is_exclusive(x_116);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_116, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_116, 2);
lean_dec(x_160);
x_161 = lean_ctor_get(x_116, 1);
lean_dec(x_161);
x_162 = lean_ctor_get(x_116, 0);
lean_dec(x_162);
lean_ctor_set(x_116, 3, x_114);
lean_ctor_set(x_116, 2, x_27);
lean_ctor_set(x_116, 1, x_26);
lean_ctor_set(x_116, 0, x_25);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_6);
return x_116;
}
else
{
lean_object* x_163; 
lean_dec(x_116);
x_163 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_163, 0, x_25);
lean_ctor_set(x_163, 1, x_26);
lean_ctor_set(x_163, 2, x_27);
lean_ctor_set(x_163, 3, x_114);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_6);
return x_163;
}
}
else
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_114);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_165 = lean_ctor_get(x_114, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_114, 2);
lean_dec(x_166);
x_167 = lean_ctor_get(x_114, 1);
lean_dec(x_167);
x_168 = lean_ctor_get(x_114, 0);
lean_dec(x_168);
x_169 = lean_ctor_get_uint8(x_119, sizeof(void*)*4);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_114);
x_170 = lean_ctor_get(x_119, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_119, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_119, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_119, 3);
lean_inc(x_173);
lean_dec(x_119);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_116;
x_124 = x_117;
x_125 = x_118;
x_126 = x_170;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
goto block_133;
}
else
{
uint8_t x_174; 
lean_dec(x_29);
x_174 = !lean_is_exclusive(x_116);
if (x_174 == 0)
{
lean_object* x_175; 
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_169);
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_25);
lean_ctor_set(x_175, 1, x_26);
lean_ctor_set(x_175, 2, x_27);
lean_ctor_set(x_175, 3, x_114);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_6);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_116, 0);
x_177 = lean_ctor_get(x_116, 1);
x_178 = lean_ctor_get(x_116, 2);
x_179 = lean_ctor_get(x_116, 3);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_116);
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_178);
lean_ctor_set(x_180, 3, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_169);
lean_ctor_set(x_114, 0, x_180);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_25);
lean_ctor_set(x_181, 1, x_26);
lean_ctor_set(x_181, 2, x_27);
lean_ctor_set(x_181, 3, x_114);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_6);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_114);
x_182 = lean_ctor_get_uint8(x_119, sizeof(void*)*4);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_119, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_119, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_119, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_119, 3);
lean_inc(x_186);
lean_dec(x_119);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_116;
x_124 = x_117;
x_125 = x_118;
x_126 = x_183;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
goto block_133;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_29);
x_187 = lean_ctor_get(x_116, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_116, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_116, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_116, 3);
lean_inc(x_190);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 x_191 = x_116;
} else {
 lean_dec_ref(x_116);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 4, 1);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_188);
lean_ctor_set(x_192, 2, x_189);
lean_ctor_set(x_192, 3, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_182);
x_193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_117);
lean_ctor_set(x_193, 2, x_118);
lean_ctor_set(x_193, 3, x_119);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_115);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_25);
lean_ctor_set(x_194, 1, x_26);
lean_ctor_set(x_194, 2, x_27);
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_6);
return x_194;
}
}
}
}
}
}
else
{
lean_object* x_195; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_29);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_25);
lean_ctor_set(x_195, 1, x_26);
lean_ctor_set(x_195, 2, x_27);
lean_ctor_set(x_195, 3, x_114);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_6);
return x_195;
}
block_133:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
if (lean_is_scalar(x_29)) {
 x_130 = lean_alloc_ctor(1, 4, 1);
} else {
 x_130 = x_29;
}
lean_ctor_set(x_130, 0, x_120);
lean_ctor_set(x_130, 1, x_121);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_123);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_6);
x_131 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 3, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_6);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_124);
lean_ctor_set(x_132, 2, x_125);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_115);
return x_132;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_2, x_5, x_6);
x_1 = x_4;
x_2 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2___redArg(x_1, x_2);
x_4 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0_spec__0___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Json_mkObj_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_instCoeNat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_instCoeNat___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromInt(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_instCoeInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_instCoeInt___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_instCoeString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_instCoeString___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_instCoeBool() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_instCoeBool___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Json_instCoeBool___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Json_isNull(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_getObj_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("object expected", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObj_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getObj_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Json_getObj_x3f___closed__1;
return x_5;
}
}
}
static lean_object* _init_l_Lean_Json_getArr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("array expected", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getArr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getArr_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Json_getArr_x3f___closed__1;
return x_5;
}
}
}
static lean_object* _init_l_Lean_Json_getStr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String expected", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getStr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getStr_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Json_getStr_x3f___closed__1;
return x_5;
}
}
}
static lean_object* _init_l_Lean_Json_getNat_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Natural number expected", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getNat_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getNat_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_10 = lean_int_dec_lt(x_6, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_11 == 0)
{
lean_dec(x_6);
lean_free_object(x_1);
goto block_3;
}
else
{
lean_object* x_12; 
x_12 = lean_nat_abs(x_6);
lean_dec(x_6);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
goto block_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_;
x_18 = lean_int_dec_lt(x_14, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_19 == 0)
{
lean_dec(x_14);
goto block_3;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_nat_abs(x_14);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
goto block_3;
}
}
}
else
{
lean_dec(x_1);
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getNat_x3f___closed__1;
return x_2;
}
}
}
static lean_object* _init_l_Lean_Json_getInt_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Integer expected", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getInt_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getInt_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_6);
lean_free_object(x_1);
goto block_3;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_11);
goto block_3;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
}
}
else
{
lean_dec(x_1);
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getInt_x3f___closed__1;
return x_2;
}
}
}
static lean_object* _init_l_Lean_Json_getBool_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getBool_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getBool_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get_uint8(x_1, 0);
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Json_getBool_x3f___closed__1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getBool_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_getNum_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("number expected", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getNum_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getNum_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Json_getNum_x3f___closed__1;
return x_5;
}
}
}
static lean_object* _init_l_Lean_Json_getObjVal_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjVal_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getObj_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_4, x_2);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Json_getObjVal_x3f___closed__0;
x_7 = lean_string_append(x_6, x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
uint8_t x_8; 
lean_free_object(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_11, x_2);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Json_getObjVal_x3f___closed__0;
x_14 = lean_string_append(x_13, x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(1, 1, 0);
} else {
 x_18 = x_17;
}
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = l_Lean_Json_getObjVal_x3f___closed__1;
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_getArrVal_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("index out of bounds: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getArrVal_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getArr_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_4);
x_7 = l_Lean_Json_getArrVal_x3f___closed__0;
x_8 = l_Nat_reprFast(x_2);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_4, x_2);
lean_dec(x_2);
lean_dec_ref(x_4);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_11);
x_14 = l_Lean_Json_getArrVal_x3f___closed__0;
x_15 = l_Nat_reprFast(x_2);
x_16 = lean_string_append(x_14, x_15);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_11, x_2);
lean_dec(x_2);
lean_dec_ref(x_11);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Json_getArrVal_x3f___closed__1;
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Json_setObjVal_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Json.setObjVal!", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Json.setObjVal!: not an object: {j}", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Json_setObjVal_x21___closed__1;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(285u);
x_4 = l_Lean_Json_setObjVal_x21___closed__0;
x_5 = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_5, x_2, x_3);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_7, x_2, x_3);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = l_Lean_Json_setObjVal_x21___closed__2;
x_11 = l_panic___at___Lean_Json_setObjVal_x21_spec__0(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_mergeObj_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at___Lean_Json_mergeObj_spec__0(x_1, x_3);
x_8 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_7, x_4, x_5);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_RBNode_fold___at___Lean_Json_mergeObj_spec__0(x_3, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_RBNode_fold___at___Lean_Json_mergeObj_spec__0(x_3, x_7);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_instCoeArrayStructured() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_instCoeArrayStructured___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRBNodeStringStructured___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_instCoeRBNodeStringStructured() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_instCoeRBNodeStringStructured___lam__0), 1, 0);
return x_1;
}
}
lean_object* initialize_Init_Data_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_OfScientific(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_ = _init_l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_();
lean_mark_persistent(l_Lean_hashJsonNumber___closed__0____x40_Lean_Data_Json_Basic___hyg_173_);
l_Lean_instHashableJsonNumber___closed__0 = _init_l_Lean_instHashableJsonNumber___closed__0();
lean_mark_persistent(l_Lean_instHashableJsonNumber___closed__0);
l_Lean_instHashableJsonNumber = _init_l_Lean_instHashableJsonNumber();
lean_mark_persistent(l_Lean_instHashableJsonNumber);
l_Lean_JsonNumber_instCoeNat___closed__0 = _init_l_Lean_JsonNumber_instCoeNat___closed__0();
lean_mark_persistent(l_Lean_JsonNumber_instCoeNat___closed__0);
l_Lean_JsonNumber_instCoeNat = _init_l_Lean_JsonNumber_instCoeNat();
lean_mark_persistent(l_Lean_JsonNumber_instCoeNat);
l_Lean_JsonNumber_instCoeInt___closed__0 = _init_l_Lean_JsonNumber_instCoeInt___closed__0();
lean_mark_persistent(l_Lean_JsonNumber_instCoeInt___closed__0);
l_Lean_JsonNumber_instCoeInt = _init_l_Lean_JsonNumber_instCoeInt();
lean_mark_persistent(l_Lean_JsonNumber_instCoeInt);
l_Lean_JsonNumber_normalize___closed__0 = _init_l_Lean_JsonNumber_normalize___closed__0();
lean_mark_persistent(l_Lean_JsonNumber_normalize___closed__0);
l_Lean_JsonNumber_normalize___closed__1 = _init_l_Lean_JsonNumber_normalize___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_normalize___closed__1);
l_Lean_JsonNumber_normalize___closed__2 = _init_l_Lean_JsonNumber_normalize___closed__2();
lean_mark_persistent(l_Lean_JsonNumber_normalize___closed__2);
l_Lean_JsonNumber_normalize___closed__3 = _init_l_Lean_JsonNumber_normalize___closed__3();
lean_mark_persistent(l_Lean_JsonNumber_normalize___closed__3);
l_Lean_JsonNumber_ltProp = _init_l_Lean_JsonNumber_ltProp();
lean_mark_persistent(l_Lean_JsonNumber_ltProp);
l_Lean_JsonNumber_instOrd = _init_l_Lean_JsonNumber_instOrd();
lean_mark_persistent(l_Lean_JsonNumber_instOrd);
l_Lean_JsonNumber_toString___closed__0 = _init_l_Lean_JsonNumber_toString___closed__0();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__0);
l_Lean_JsonNumber_toString___closed__1 = _init_l_Lean_JsonNumber_toString___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__1);
l_Lean_JsonNumber_toString___closed__2 = _init_l_Lean_JsonNumber_toString___closed__2();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__2);
l_Lean_JsonNumber_toString___closed__3 = _init_l_Lean_JsonNumber_toString___closed__3();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__3);
l_Lean_JsonNumber_toString___closed__4 = _init_l_Lean_JsonNumber_toString___closed__4();
lean_mark_persistent(l_Lean_JsonNumber_toString___closed__4);
l_Lean_JsonNumber_instToString___closed__0 = _init_l_Lean_JsonNumber_instToString___closed__0();
lean_mark_persistent(l_Lean_JsonNumber_instToString___closed__0);
l_Lean_JsonNumber_instToString = _init_l_Lean_JsonNumber_instToString();
lean_mark_persistent(l_Lean_JsonNumber_instToString);
l_Lean_JsonNumber_instRepr___lam__0___closed__0 = _init_l_Lean_JsonNumber_instRepr___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonNumber_instRepr___lam__0___closed__0);
l_Lean_JsonNumber_instRepr___lam__0___closed__1 = _init_l_Lean_JsonNumber_instRepr___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_instRepr___lam__0___closed__1);
l_Lean_JsonNumber_instRepr___lam__0___closed__2 = _init_l_Lean_JsonNumber_instRepr___lam__0___closed__2();
lean_mark_persistent(l_Lean_JsonNumber_instRepr___lam__0___closed__2);
l_Lean_JsonNumber_instRepr___lam__0___closed__3 = _init_l_Lean_JsonNumber_instRepr___lam__0___closed__3();
lean_mark_persistent(l_Lean_JsonNumber_instRepr___lam__0___closed__3);
l_Lean_JsonNumber_instRepr___lam__0___closed__4 = _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4();
lean_mark_persistent(l_Lean_JsonNumber_instRepr___lam__0___closed__4);
l_Lean_JsonNumber_instRepr___lam__0___closed__5 = _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5();
lean_mark_persistent(l_Lean_JsonNumber_instRepr___lam__0___closed__5);
l_Lean_JsonNumber_instRepr = _init_l_Lean_JsonNumber_instRepr();
lean_mark_persistent(l_Lean_JsonNumber_instRepr);
l_Lean_JsonNumber_instOfScientific = _init_l_Lean_JsonNumber_instOfScientific();
lean_mark_persistent(l_Lean_JsonNumber_instOfScientific);
l_Lean_JsonNumber_instNeg = _init_l_Lean_JsonNumber_instNeg();
lean_mark_persistent(l_Lean_JsonNumber_instNeg);
l_Lean_JsonNumber_instInhabited___closed__0 = _init_l_Lean_JsonNumber_instInhabited___closed__0();
lean_mark_persistent(l_Lean_JsonNumber_instInhabited___closed__0);
l_Lean_JsonNumber_instInhabited = _init_l_Lean_JsonNumber_instInhabited();
lean_mark_persistent(l_Lean_JsonNumber_instInhabited);
l_Lean_JsonNumber_toFloat___closed__0 = _init_l_Lean_JsonNumber_toFloat___closed__0();
l_Lean_JsonNumber_toFloat___closed__1 = _init_l_Lean_JsonNumber_toFloat___closed__1();
l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0 = _init_l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0();
lean_mark_persistent(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0);
l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1 = _init_l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1();
lean_mark_persistent(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1);
l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2 = _init_l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2();
lean_mark_persistent(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2);
l_Lean_JsonNumber_fromFloat_x3f___closed__0 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0();
l_Lean_JsonNumber_fromFloat_x3f___closed__1 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1();
lean_mark_persistent(l_Lean_JsonNumber_fromFloat_x3f___closed__1);
l_Lean_JsonNumber_fromFloat_x3f___closed__2 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2();
l_Lean_JsonNumber_fromFloat_x3f___closed__3 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__3();
lean_mark_persistent(l_Lean_JsonNumber_fromFloat_x3f___closed__3);
l_Lean_JsonNumber_fromFloat_x3f___closed__4 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__4();
lean_mark_persistent(l_Lean_JsonNumber_fromFloat_x3f___closed__4);
l_Lean_JsonNumber_fromFloat_x3f___closed__5 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__5();
lean_mark_persistent(l_Lean_JsonNumber_fromFloat_x3f___closed__5);
l_Lean_JsonNumber_fromFloat_x3f___closed__6 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__6();
lean_mark_persistent(l_Lean_JsonNumber_fromFloat_x3f___closed__6);
l_Lean_JsonNumber_fromFloat_x3f___closed__7 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__7();
lean_mark_persistent(l_Lean_JsonNumber_fromFloat_x3f___closed__7);
l_Lean_JsonNumber_fromFloat_x3f___closed__8 = _init_l_Lean_JsonNumber_fromFloat_x3f___closed__8();
lean_mark_persistent(l_Lean_JsonNumber_fromFloat_x3f___closed__8);
l_Lean_instInhabitedJson = _init_l_Lean_instInhabitedJson();
lean_mark_persistent(l_Lean_instInhabitedJson);
l_Lean_Json_instBEq___closed__0 = _init_l_Lean_Json_instBEq___closed__0();
lean_mark_persistent(l_Lean_Json_instBEq___closed__0);
l_Lean_Json_instBEq = _init_l_Lean_Json_instBEq();
lean_mark_persistent(l_Lean_Json_instBEq);
l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0 = _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0();
l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1 = _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1();
l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2 = _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2();
l_Lean_Json_instHashable___closed__0 = _init_l_Lean_Json_instHashable___closed__0();
lean_mark_persistent(l_Lean_Json_instHashable___closed__0);
l_Lean_Json_instHashable = _init_l_Lean_Json_instHashable();
lean_mark_persistent(l_Lean_Json_instHashable);
l_Lean_Json_instCoeNat = _init_l_Lean_Json_instCoeNat();
lean_mark_persistent(l_Lean_Json_instCoeNat);
l_Lean_Json_instCoeInt = _init_l_Lean_Json_instCoeInt();
lean_mark_persistent(l_Lean_Json_instCoeInt);
l_Lean_Json_instCoeString = _init_l_Lean_Json_instCoeString();
lean_mark_persistent(l_Lean_Json_instCoeString);
l_Lean_Json_instCoeBool = _init_l_Lean_Json_instCoeBool();
lean_mark_persistent(l_Lean_Json_instCoeBool);
l_Lean_Json_getObj_x3f___closed__0 = _init_l_Lean_Json_getObj_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getObj_x3f___closed__0);
l_Lean_Json_getObj_x3f___closed__1 = _init_l_Lean_Json_getObj_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getObj_x3f___closed__1);
l_Lean_Json_getArr_x3f___closed__0 = _init_l_Lean_Json_getArr_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getArr_x3f___closed__0);
l_Lean_Json_getArr_x3f___closed__1 = _init_l_Lean_Json_getArr_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getArr_x3f___closed__1);
l_Lean_Json_getStr_x3f___closed__0 = _init_l_Lean_Json_getStr_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getStr_x3f___closed__0);
l_Lean_Json_getStr_x3f___closed__1 = _init_l_Lean_Json_getStr_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getStr_x3f___closed__1);
l_Lean_Json_getNat_x3f___closed__0 = _init_l_Lean_Json_getNat_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getNat_x3f___closed__0);
l_Lean_Json_getNat_x3f___closed__1 = _init_l_Lean_Json_getNat_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getNat_x3f___closed__1);
l_Lean_Json_getInt_x3f___closed__0 = _init_l_Lean_Json_getInt_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getInt_x3f___closed__0);
l_Lean_Json_getInt_x3f___closed__1 = _init_l_Lean_Json_getInt_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getInt_x3f___closed__1);
l_Lean_Json_getBool_x3f___closed__0 = _init_l_Lean_Json_getBool_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getBool_x3f___closed__0);
l_Lean_Json_getBool_x3f___closed__1 = _init_l_Lean_Json_getBool_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getBool_x3f___closed__1);
l_Lean_Json_getNum_x3f___closed__0 = _init_l_Lean_Json_getNum_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getNum_x3f___closed__0);
l_Lean_Json_getNum_x3f___closed__1 = _init_l_Lean_Json_getNum_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getNum_x3f___closed__1);
l_Lean_Json_getObjVal_x3f___closed__0 = _init_l_Lean_Json_getObjVal_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getObjVal_x3f___closed__0);
l_Lean_Json_getObjVal_x3f___closed__1 = _init_l_Lean_Json_getObjVal_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getObjVal_x3f___closed__1);
l_Lean_Json_getArrVal_x3f___closed__0 = _init_l_Lean_Json_getArrVal_x3f___closed__0();
lean_mark_persistent(l_Lean_Json_getArrVal_x3f___closed__0);
l_Lean_Json_getArrVal_x3f___closed__1 = _init_l_Lean_Json_getArrVal_x3f___closed__1();
lean_mark_persistent(l_Lean_Json_getArrVal_x3f___closed__1);
l_Lean_Json_setObjVal_x21___closed__0 = _init_l_Lean_Json_setObjVal_x21___closed__0();
lean_mark_persistent(l_Lean_Json_setObjVal_x21___closed__0);
l_Lean_Json_setObjVal_x21___closed__1 = _init_l_Lean_Json_setObjVal_x21___closed__1();
lean_mark_persistent(l_Lean_Json_setObjVal_x21___closed__1);
l_Lean_Json_setObjVal_x21___closed__2 = _init_l_Lean_Json_setObjVal_x21___closed__2();
lean_mark_persistent(l_Lean_Json_setObjVal_x21___closed__2);
l_Lean_Json_instCoeArrayStructured = _init_l_Lean_Json_instCoeArrayStructured();
lean_mark_persistent(l_Lean_Json_instCoeArrayStructured);
l_Lean_Json_instCoeRBNodeStringStructured = _init_l_Lean_Json_instCoeRBNodeStringStructured();
lean_mark_persistent(l_Lean_Json_instCoeRBNodeStringStructured);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
