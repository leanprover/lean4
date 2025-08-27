// Lean compiler output
// Module: Init.Data.Repr
// Imports: Init.Data.Format.Basic
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
static lean_object* l_instReprIterator___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Prod_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Sum_repr___redArg___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reprStr___redArg(lean_object*, lean_object*);
lean_object* l_List_asString(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Bool_repr___redArg___closed__2;
static lean_object* l_List_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Char_quoteCore___closed__2;
LEAN_EXPORT lean_object* l_reprSourceInfo____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_(lean_object*, lean_object*);
static lean_object* l_Option_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_instReprString___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reprStr(lean_object*, lean_object*, lean_object*);
static lean_object* l_Decidable_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Char_quoteCore___closed__1;
static lean_object* l_reprSourceInfo___closed__4____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
LEAN_EXPORT lean_object* l_instReprPUnit;
static lean_object* l_Option_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(lean_object*);
static lean_object* l_instReprDecidable___closed__0;
lean_object* l_Std_Format_fill(lean_object*);
static lean_object* l_Prod_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr___redArg(lean_object*, lean_object*);
static lean_object* l_instReprULift___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int_repr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Decidable_repr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSuperscriptString(lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_reprStr___redArg___closed__0;
static lean_object* l_instReprUnit___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instReprULift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reprFast___closed__1;
LEAN_EXPORT lean_object* l_instReprSigma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprSum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprFin___lam__0(lean_object*, lean_object*);
static lean_object* l_instReprPos___lam__0___closed__2;
static lean_object* l_Int_repr___closed__0;
LEAN_EXPORT lean_object* l_instReprString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSuperDigits(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_instReprPos___lam__0___closed__1;
LEAN_EXPORT lean_object* l_String_quote___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt8;
LEAN_EXPORT lean_object* l_instReprPos;
LEAN_EXPORT lean_object* l_Decidable_repr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprChar;
static lean_object* l_Sum_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Bool_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprList(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(uint32_t);
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_instReprSubstring___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSigma(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Repr_addAppParen___closed__2;
static lean_object* l_List_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_instNatCastInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple___redArg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Sigma_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instReprSourceInfo___closed__0;
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0(uint32_t, lean_object*);
static lean_object* l_instReprBool___closed__0;
static lean_object* l_Repr_addAppParen___closed__3;
LEAN_EXPORT lean_object* l_Option_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sigma_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSubstring;
LEAN_EXPORT uint32_t l_Nat_digitChar(lean_object*);
LEAN_EXPORT lean_object* l_instReprDecidable(lean_object*);
static lean_object* l_List_repr___redArg___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprChar___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Char_quoteCore___closed__0;
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_quoteCore___boxed(lean_object*, lean_object*);
static lean_object* l_instReprSubstring___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instReprAtomUInt16;
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_instReprPos___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Repr_addAppParen___closed__1;
LEAN_EXPORT lean_object* l_instReprUnit;
LEAN_EXPORT lean_object* l_Bool_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt64;
static lean_object* l_Decidable_repr___redArg___closed__0;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray___closed__0;
LEAN_EXPORT lean_object* l_Repr_ctorIdx(lean_object*, lean_object*);
static lean_object* l_String_quote___closed__1;
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprBool;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray;
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object*);
static lean_object* l_Repr_addAppParen___closed__4;
LEAN_EXPORT uint32_t l_Nat_superDigitChar(lean_object*);
static lean_object* l_Sigma_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_quote(uint32_t);
LEAN_EXPORT lean_object* l_reprArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprAtomUSize;
LEAN_EXPORT lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Repr_addAppParen___boxed(lean_object*, lean_object*);
static lean_object* l_Option_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_instReprNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Repr_addAppParen_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_instReprChar___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___redArg(lean_object*, lean_object*);
static lean_object* l_Nat_reprFast___closed__0;
extern lean_object* l_System_Platform_numBits;
static lean_object* l_instReprIterator___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Nat_toSubDigits(lean_object*);
static lean_object* l_Sigma_repr___redArg___closed__3;
static lean_object* l_instReprIterator___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instReprUSize;
LEAN_EXPORT lean_object* l_instReprList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0(uint16_t, lean_object*);
static lean_object* l_Decidable_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Decidable_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSubstring___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Repr_addAppParen___closed__0;
static lean_object* l_Char_quoteCore___closed__5;
static lean_object* l_Int_repr___closed__1;
LEAN_EXPORT lean_object* l_List_repr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_instReprListOfReprAtom___redArg(lean_object*, lean_object*);
static lean_object* l_reprSourceInfo___closed__1____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
LEAN_EXPORT lean_object* l_List_repr_x27___redArg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprUnit___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_instReprPos___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Char_repr(uint32_t);
LEAN_EXPORT lean_object* l_instReprULift___redArg(lean_object*);
static lean_object* l_Sigma_repr___redArg___closed__4;
static lean_object* l_Prod_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ReprTuple_ctorIdx___boxed(lean_object*, lean_object*);
static lean_object* l_instReprIterator___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Repr_ctorIdx___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubtype(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_quote___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprFin___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0(uint64_t, lean_object*);
static lean_object* l_Bool_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_instReprOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprAtomUInt32;
LEAN_EXPORT lean_object* l_Option_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_superDigitChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprTupleOfRepr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reprSourceInfo____x40_Init_Data_Repr_413755464____hygCtx___hyg_3____boxed(lean_object*, lean_object*);
static lean_object* l_Decidable_repr___redArg___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Char_quoteCore___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_reprSourceInfo___closed__2____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
LEAN_EXPORT lean_object* l_instReprAtomBool;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Char_quote___closed__0;
LEAN_EXPORT lean_object* l_instReprIterator;
LEAN_EXPORT lean_object* l_instReprFin___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSourceInfo;
static lean_object* l_instReprPUnit___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instReprInt;
static lean_object* l_List_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_instReprAtomChar;
LEAN_EXPORT lean_object* l_instReprNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSuperDigitsAux(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
LEAN_EXPORT lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprListOfReprAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprAtomNat;
static lean_object* l_List_repr___redArg___closed__0;
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprAtomUInt8;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Sigma_repr___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Sigma_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_quote_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_instReprPos___lam__0___closed__3;
static lean_object* l_instReprPUnit___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Sum_repr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt32;
static lean_object* l_reprSourceInfo___closed__3____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
LEAN_EXPORT lean_object* l_instReprUSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ReprAtom_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_reprTuple___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUnit___lam__0(lean_object*, lean_object*);
static lean_object* l_Prod_repr___redArg___closed__3;
static lean_object* l_Sigma_repr___redArg___closed__0;
static lean_object* l_List_repr___redArg___closed__3;
static lean_object* l_Prod_repr___redArg___closed__2;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_instReprFin(lean_object*);
static lean_object* l_Sum_repr___redArg___closed__0;
lean_object* lean_uint8_to_nat(uint8_t);
static lean_object* l_Option_repr___redArg___closed__1;
static lean_object* l_instReprULift___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instReprSubtype___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprUSize___lam__0(size_t, lean_object*);
static lean_object* l_Bool_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Nat_subDigitChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubtype___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_reprSourceInfo___closed__0____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
LEAN_EXPORT lean_object* l_reprArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSubDigitsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_repr___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_instReprInt___lam__0(lean_object*, lean_object*);
static lean_object* l_instReprUnit___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Decidable_repr___redArg(uint8_t, lean_object*);
lean_object* lean_string_of_usize(size_t);
LEAN_EXPORT lean_object* l_instReprAtomUInt64;
LEAN_EXPORT lean_object* l_instReprPos___lam__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
static lean_object* l_Sum_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_instReprAtomInt;
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprEmpty;
static lean_object* l_String_quote___closed__0;
LEAN_EXPORT lean_object* l_instReprId__1___redArg___boxed(lean_object*);
static lean_object* l_Sigma_repr___redArg___closed__1;
static lean_object* l_reprSourceInfo___closed__8____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_quote_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSubscriptString(lean_object*);
LEAN_EXPORT lean_object* l_Char_quoteCore(uint32_t, uint8_t);
LEAN_EXPORT lean_object* l_instReprNat;
LEAN_EXPORT lean_object* l_instReprId__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprString;
LEAN_EXPORT lean_object* l_Prod_reprTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt16;
static lean_object* l_hexDigitRepr___closed__0;
LEAN_EXPORT lean_object* l_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0(uint8_t, lean_object*);
static lean_object* l_Bool_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_ReprTuple_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Prod_repr___redArg___closed__0;
static lean_object* l_reprSourceInfo___closed__7____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
LEAN_EXPORT uint32_t l_Nat_subDigitChar(lean_object*);
static lean_object* l_Char_quoteCore___closed__4;
LEAN_EXPORT lean_object* l_Bool_repr(uint8_t, lean_object*);
static lean_object* l_reprSourceInfo___closed__6____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
LEAN_EXPORT lean_object* l_instReprAtomString;
LEAN_EXPORT lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Repr_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Repr_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Repr_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_reprStr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_reprStr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = l_reprStr___redArg___closed__0;
x_6 = lean_format_pretty(x_4, x_5, x_3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_reprStr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = l_reprStr___redArg___closed__0;
x_7 = lean_format_pretty(x_5, x_6, x_4, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_reprArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_reprArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReprAtom_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprId___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprId__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprId__1___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprId__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_internal_panic_unreachable();
}
}
static lean_object* _init_l_instReprEmpty() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprEmpty___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprEmpty___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Bool_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Bool_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Bool_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Bool_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Bool_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Bool_repr___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Bool_repr___redArg___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Bool_repr___redArg___closed__3;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Bool_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Bool_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Bool_repr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Bool_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprBool___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Bool_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instReprBool() {
_start:
{
lean_object* x_1; 
x_1 = l_instReprBool___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Repr_addAppParen_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Repr_addAppParen___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Repr_addAppParen___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = l_Repr_addAppParen___closed__2;
x_6 = l_Repr_addAppParen___closed__3;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_Repr_addAppParen___closed__4;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Repr_addAppParen(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Decidable_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isFalse _", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Decidable_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Decidable_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Decidable_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isTrue _", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Decidable_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Decidable_repr___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Decidable_repr___redArg___closed__1;
x_4 = l_Repr_addAppParen(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Decidable_repr___redArg___closed__3;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Decidable_repr(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Decidable_repr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Decidable_repr___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Decidable_repr(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_instReprDecidable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Decidable_repr___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprDecidable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprDecidable___closed__0;
return x_2;
}
}
static lean_object* _init_l_instReprPUnit___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PUnit.unit", 10, 10);
return x_1;
}
}
static lean_object* _init_l_instReprPUnit___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprPUnit___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprPUnit___lam__0___closed__1;
return x_3;
}
}
static lean_object* _init_l_instReprPUnit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprPUnit___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprPUnit___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_instReprULift___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ULift.up ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_instReprULift___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprULift___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_instReprULift___redArg___lam__0___closed__1;
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_apply_2(x_1, x_2, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprULift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprULift___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instReprULift___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_instReprUnit___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("()", 2, 2);
return x_1;
}
}
static lean_object* _init_l_instReprUnit___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprUnit___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprUnit___lam__0___closed__1;
return x_3;
}
}
static lean_object* _init_l_instReprUnit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprUnit___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprUnit___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Option_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Option_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Option_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("some ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Option_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_repr___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = l_Option_repr___redArg___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Option_repr___redArg___closed__3;
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Option_repr___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_repr___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Option_repr(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Sum_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sum.inl ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Sum_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Sum_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Sum_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sum.inr ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Sum_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Sum_repr___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Sum_repr___redArg___closed__1;
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l_Sum_repr___redArg___closed__3;
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_apply_2(x_2, x_11, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sum_repr___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Sum_repr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sum_repr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprSum___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReprTuple_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReprTuple_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ReprTuple_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprTupleOfRepr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_2(x_1, x_6, x_8);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
x_10 = lean_apply_2(x_2, x_7, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_apply_2(x_1, x_11, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_apply_2(x_2, x_12, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Prod_reprTuple___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_instToFormatFormat___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Prod_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_instNatCastInt___lam__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Prod_repr___redArg___closed__0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_9);
x_11 = lean_apply_2(x_2, x_6, x_3);
x_12 = l_List_reverse___redArg(x_11);
x_13 = l_Prod_repr___redArg___closed__3;
x_14 = l_Std_Format_joinSep___redArg(x_7, x_12, x_13);
x_15 = l_Prod_repr___redArg___closed__4;
x_16 = l_Repr_addAppParen___closed__3;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = l_Repr_addAppParen___closed__4;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = 0;
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = l_Prod_repr___redArg___closed__0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_apply_2(x_1, x_23, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_apply_2(x_2, x_24, x_29);
x_31 = l_List_reverse___redArg(x_30);
x_32 = l_Prod_repr___redArg___closed__3;
x_33 = l_Std_Format_joinSep___redArg(x_25, x_31, x_32);
x_34 = l_Prod_repr___redArg___closed__4;
x_35 = l_Repr_addAppParen___closed__3;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = l_Repr_addAppParen___closed__4;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Prod_repr___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Prod_repr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟨", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Sigma_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟩", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Sigma_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Sigma_repr___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = l_Sigma_repr___redArg___closed__2;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
x_10 = lean_apply_3(x_2, x_5, x_6, x_7);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Prod_repr___redArg___closed__4;
x_13 = l_Sigma_repr___redArg___closed__4;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_Sigma_repr___redArg___closed__5;
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
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_20);
x_23 = lean_apply_2(x_1, x_20, x_22);
x_24 = l_Sigma_repr___redArg___closed__2;
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_3(x_2, x_20, x_21, x_22);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Prod_repr___redArg___closed__4;
x_29 = l_Sigma_repr___redArg___closed__4;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = l_Sigma_repr___redArg___closed__5;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Sigma_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sigma_repr___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sigma_repr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprSigma___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprSigma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instReprSubtype___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Nat_digitChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(10u);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(11u);
x_25 = lean_nat_dec_eq(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(12u);
x_27 = lean_nat_dec_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(13u);
x_29 = lean_nat_dec_eq(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(14u);
x_31 = lean_nat_dec_eq(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(15u);
x_33 = lean_nat_dec_eq(x_1, x_32);
if (x_33 == 0)
{
uint32_t x_34; 
x_34 = 42;
return x_34;
}
else
{
uint32_t x_35; 
x_35 = 102;
return x_35;
}
}
else
{
uint32_t x_36; 
x_36 = 101;
return x_36;
}
}
else
{
uint32_t x_37; 
x_37 = 100;
return x_37;
}
}
else
{
uint32_t x_38; 
x_38 = 99;
return x_38;
}
}
else
{
uint32_t x_39; 
x_39 = 98;
return x_39;
}
}
else
{
uint32_t x_40; 
x_40 = 97;
return x_40;
}
}
else
{
uint32_t x_41; 
x_41 = 57;
return x_41;
}
}
else
{
uint32_t x_42; 
x_42 = 56;
return x_42;
}
}
else
{
uint32_t x_43; 
x_43 = 55;
return x_43;
}
}
else
{
uint32_t x_44; 
x_44 = 54;
return x_44;
}
}
else
{
uint32_t x_45; 
x_45 = 53;
return x_45;
}
}
else
{
uint32_t x_46; 
x_46 = 52;
return x_46;
}
}
else
{
uint32_t x_47; 
x_47 = 51;
return x_47;
}
}
else
{
uint32_t x_48; 
x_48 = 50;
return x_48;
}
}
else
{
uint32_t x_49; 
x_49 = 49;
return x_49;
}
}
else
{
uint32_t x_50; 
x_50 = 48;
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_digitChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_nat_mod(x_3, x_1);
x_8 = l_Nat_digitChar(x_7);
lean_dec(x_7);
x_9 = lean_nat_div(x_3, x_1);
lean_dec(x_3);
x_10 = lean_nat_dec_eq(x_9, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_13 = lean_box_uint32(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_2 = x_12;
x_3 = x_9;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_2);
x_16 = lean_box_uint32(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_toDigitsCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Nat_toDigitsCore(x_1, x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_toDigits(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_string_of_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_8 = lean_string_of_usize(x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_13 = lean_string_of_usize(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = l_List_range(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Data_Repr_0__Nat_reprArray___closed__0;
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_____private_Init_Data_Repr_0__Nat_reprArray_spec__0(x_1, x_2);
x_4 = lean_array_mk(x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reprFast___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Repr_0__Nat_reprArray;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_reprFast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reprFast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Init_Data_Repr_0__Nat_reprArray;
x_3 = l_Nat_reprFast___closed__0;
x_4 = lean_nat_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Nat_reprFast___closed__1;
x_6 = lean_nat_dec_lt(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(10u);
x_8 = l_Nat_toDigits(x_7, x_1);
x_9 = l_List_asString(x_8);
return x_9;
}
else
{
size_t x_10; lean_object* x_11; 
x_10 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_11 = lean_string_of_usize(x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_2, x_1);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT uint32_t l_Nat_superDigitChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint32_t x_22; 
x_22 = 42;
return x_22;
}
else
{
uint32_t x_23; 
x_23 = 8313;
return x_23;
}
}
else
{
uint32_t x_24; 
x_24 = 8312;
return x_24;
}
}
else
{
uint32_t x_25; 
x_25 = 8311;
return x_25;
}
}
else
{
uint32_t x_26; 
x_26 = 8310;
return x_26;
}
}
else
{
uint32_t x_27; 
x_27 = 8309;
return x_27;
}
}
else
{
uint32_t x_28; 
x_28 = 8308;
return x_28;
}
}
else
{
uint32_t x_29; 
x_29 = 179;
return x_29;
}
}
else
{
uint32_t x_30; 
x_30 = 178;
return x_30;
}
}
else
{
uint32_t x_31; 
x_31 = 185;
return x_31;
}
}
else
{
uint32_t x_32; 
x_32 = 8304;
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Nat_superDigitChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_superDigitChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigitsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = lean_nat_mod(x_1, x_3);
x_5 = l_Nat_superDigitChar(x_4);
lean_dec(x_4);
x_6 = lean_nat_div(x_1, x_3);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box_uint32(x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_box_uint32(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Nat_toSuperDigitsAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperscriptString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_toSuperDigits(x_1);
x_3 = l_List_asString(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Nat_subDigitChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint32_t x_22; 
x_22 = 42;
return x_22;
}
else
{
uint32_t x_23; 
x_23 = 8329;
return x_23;
}
}
else
{
uint32_t x_24; 
x_24 = 8328;
return x_24;
}
}
else
{
uint32_t x_25; 
x_25 = 8327;
return x_25;
}
}
else
{
uint32_t x_26; 
x_26 = 8326;
return x_26;
}
}
else
{
uint32_t x_27; 
x_27 = 8325;
return x_27;
}
}
else
{
uint32_t x_28; 
x_28 = 8324;
return x_28;
}
}
else
{
uint32_t x_29; 
x_29 = 8323;
return x_29;
}
}
else
{
uint32_t x_30; 
x_30 = 8322;
return x_30;
}
}
else
{
uint32_t x_31; 
x_31 = 8321;
return x_31;
}
}
else
{
uint32_t x_32; 
x_32 = 8320;
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Nat_subDigitChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_subDigitChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigitsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = lean_nat_mod(x_1, x_3);
x_5 = l_Nat_subDigitChar(x_4);
lean_dec(x_4);
x_6 = lean_nat_div(x_1, x_3);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box_uint32(x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_box_uint32(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Nat_toSubDigitsAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubscriptString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_toSubDigits(x_1);
x_3 = l_List_asString(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_instReprNat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprNat___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprNat___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_repr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_repr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_repr___closed__0;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = l_Nat_reprFast(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = l_Int_repr___closed__1;
x_10 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_11 = l_Nat_reprFast(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Int_repr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_repr(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_repr___closed__0;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Int_repr(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Int_repr(x_1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Repr_addAppParen(x_8, x_2);
return x_9;
}
}
}
static lean_object* _init_l_instReprInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprInt___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprInt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_hexDigitRepr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = l_hexDigitRepr___closed__0;
x_4 = lean_string_push(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_hexDigitRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_shiftr(x_2, x_4);
x_6 = lean_nat_mod(x_2, x_3);
lean_dec(x_2);
x_7 = l_hexDigitRepr(x_5);
lean_dec(x_5);
x_8 = l_hexDigitRepr(x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(x_2);
return x_3;
}
}
static lean_object* _init_l_Char_quoteCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Char_quoteCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\'", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Char_quoteCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\"", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Char_quoteCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\\", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Char_quoteCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\t", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Char_quoteCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore(uint32_t x_1, uint8_t x_2) {
_start:
{
uint32_t x_15; uint8_t x_16; 
x_15 = 10;
x_16 = lean_uint32_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 9;
x_18 = lean_uint32_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 92;
x_20 = lean_uint32_dec_eq(x_1, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 34;
x_22 = lean_uint32_dec_eq(x_1, x_21);
if (x_22 == 0)
{
if (x_2 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 39;
x_24 = lean_uint32_dec_eq(x_1, x_23);
if (x_24 == 0)
{
goto block_14;
}
else
{
lean_object* x_25; 
x_25 = l_Char_quoteCore___closed__1;
return x_25;
}
}
else
{
goto block_14;
}
}
else
{
lean_object* x_26; 
x_26 = l_Char_quoteCore___closed__2;
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = l_Char_quoteCore___closed__3;
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = l_Char_quoteCore___closed__4;
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = l_Char_quoteCore___closed__5;
return x_29;
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Char_quoteCore___closed__0;
x_4 = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(x_1);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
block_14:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_uint32_to_nat(x_1);
x_8 = lean_unsigned_to_nat(31u);
x_9 = lean_nat_dec_le(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 127;
x_11 = lean_uint32_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_hexDigitRepr___closed__0;
x_13 = lean_string_push(x_12, x_1);
return x_13;
}
else
{
goto block_6;
}
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Char_quoteCore(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Char_quote___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Char_quote(uint32_t x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Char_quote___closed__0;
x_3 = 0;
x_4 = l_Char_quoteCore(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = lean_string_append(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Char_quote___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_quote(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_quote(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_instReprChar() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprChar___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_instReprChar___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Char_repr(uint32_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Char_quote(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Char_repr___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_repr(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_quote_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_utf8_next(x_2, x_4);
x_8 = lean_string_utf8_get(x_2, x_4);
lean_dec(x_4);
x_9 = l_Char_quoteCore(x_8, x_1);
x_10 = lean_string_append(x_5, x_9);
lean_dec_ref(x_9);
x_4 = x_7;
x_5 = x_10;
goto _start;
}
}
}
static lean_object* _init_l_String_quote___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_String_quote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"\"", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_quote(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 1;
x_6 = l_String_quote___closed__0;
x_7 = l_String_foldlAux___at___String_quote_spec__0(x_5, x_1, x_2, x_3, x_6);
lean_dec(x_2);
x_8 = lean_string_append(x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_String_quote___closed__1;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_quote_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_String_foldlAux___at___String_quote_spec__0(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_quote___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_quote(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_quote(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_instReprString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprString___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprString___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_instReprPos___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ byteIdx := ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_instReprPos___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprPos___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprPos___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_instReprPos___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprPos___lam__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprPos___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_instReprPos___lam__0___closed__1;
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_instReprPos___lam__0___closed__3;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_instReprPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprPos___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprPos___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprPos___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_instReprSubstring___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".toSubstring", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprSubstring___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_string_utf8_extract(x_3, x_4, x_5);
x_7 = l_String_quote(x_6);
lean_dec_ref(x_6);
x_8 = l_instReprSubstring___lam__0___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
static lean_object* _init_l_instReprSubstring() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprSubstring___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprSubstring___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprSubstring___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Iterator.mk ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprIterator___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprIterator___lam__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_instReprIterator___lam__0___closed__1;
x_7 = l_String_quote(x_4);
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
x_9 = l_instReprIterator___lam__0___closed__3;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_instReprPos___lam__0___closed__1;
x_12 = l_Nat_reprFast(x_5);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_instReprPos___lam__0___closed__3;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l_instReprIterator___lam__0___closed__1;
x_22 = l_String_quote(x_19);
lean_dec_ref(x_19);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_instReprIterator___lam__0___closed__3;
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_instReprPos___lam__0___closed__1;
x_28 = l_Nat_reprFast(x_20);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_instReprPos___lam__0___closed__3;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Repr_addAppParen(x_33, x_2);
return x_34;
}
}
}
static lean_object* _init_l_instReprIterator() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprIterator___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprIterator___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instReprFin___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprFin___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprFin(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint8_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_instReprUInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprUInt8___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprUInt8___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint16_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_instReprUInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprUInt16___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprUInt16___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint32_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_instReprUInt32() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprUInt32___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_instReprUInt32___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint64_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_instReprUInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprUInt64___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_instReprUInt64___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_usize_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_instReprUSize() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprUSize___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_instReprUSize___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_List_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_List_repr___redArg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
x_5 = l_Prod_repr___redArg___closed__3;
x_6 = l_Std_Format_joinSep___redArg(x_4, x_2, x_5);
x_7 = l_Prod_repr___redArg___closed__4;
x_8 = l_List_repr___redArg___closed__4;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = l_List_repr___redArg___closed__5;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_repr___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_repr(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_List_repr___redArg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
x_5 = l_Prod_repr___redArg___closed__3;
x_6 = l_Std_Format_joinSep___redArg(x_4, x_2, x_5);
x_7 = l_Prod_repr___redArg___closed__4;
x_8 = l_List_repr___redArg___closed__4;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = l_List_repr___redArg___closed__5;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Format_fill(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_repr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_repr_x27___redArg(x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_repr_x27(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
lean_closure_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_instReprAtomBool() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomNat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomChar() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomString() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt32() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUSize() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_reprSourceInfo___closed__0____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.SourceInfo.none", 20, 20);
return x_1;
}
}
static lean_object* _init_l_reprSourceInfo___closed__1____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_reprSourceInfo___closed__0____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_reprSourceInfo___closed__2____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.SourceInfo.original", 24, 24);
return x_1;
}
}
static lean_object* _init_l_reprSourceInfo___closed__3____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_reprSourceInfo___closed__2____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_reprSourceInfo___closed__4____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_reprSourceInfo___closed__3____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_reprSourceInfo___closed__6____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.SourceInfo.synthetic", 25, 25);
return x_1;
}
}
static lean_object* _init_l_reprSourceInfo___closed__7____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_reprSourceInfo___closed__6____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_reprSourceInfo___closed__8____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_reprSourceInfo___closed__7____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_reprSourceInfo____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_54; uint8_t x_55; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec_ref(x_1);
x_54 = lean_unsigned_to_nat(1024u);
x_55 = lean_nat_dec_le(x_54, x_2);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_14 = x_56;
goto block_53;
}
else
{
lean_object* x_57; 
x_57 = l_Repr_addAppParen___closed__2;
x_14 = x_57;
goto block_53;
}
block_53:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
lean_dec_ref(x_10);
x_18 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 2);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_box(1);
x_22 = l_reprSourceInfo___closed__4____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_23 = lean_string_utf8_extract(x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
x_24 = l_String_quote(x_23);
lean_dec_ref(x_23);
x_25 = l_instReprSubstring___lam__0___closed__0;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
x_30 = l_instReprPos___lam__0___closed__1;
x_31 = l_Nat_reprFast(x_11);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_instReprPos___lam__0___closed__3;
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
x_38 = lean_string_utf8_extract(x_18, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
x_39 = l_String_quote(x_38);
lean_dec_ref(x_38);
x_40 = lean_string_append(x_39, x_25);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_21);
x_44 = l_Nat_reprFast(x_13);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_30);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set(x_49, 1, x_48);
x_50 = 0;
x_51 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = l_Repr_addAppParen(x_51, x_2);
return x_52;
}
}
case 1:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_85; uint8_t x_86; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_85 = lean_unsigned_to_nat(1024u);
x_86 = lean_nat_dec_le(x_85, x_2);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_61 = x_87;
goto block_84;
}
else
{
lean_object* x_88; 
x_88 = l_Repr_addAppParen___closed__2;
x_61 = x_88;
goto block_84;
}
block_84:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_62 = lean_box(1);
x_63 = l_reprSourceInfo___closed__8____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_64 = l_instReprPos___lam__0___closed__1;
x_65 = l_Nat_reprFast(x_58);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_instReprPos___lam__0___closed__3;
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
x_72 = l_Nat_reprFast(x_59);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_62);
x_78 = l_Bool_repr___redArg(x_60);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_79);
x_81 = 0;
x_82 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_83 = l_Repr_addAppParen(x_82, x_2);
return x_83;
}
}
default: 
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_unsigned_to_nat(1024u);
x_90 = lean_nat_dec_le(x_89, x_2);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_3 = x_91;
goto block_9;
}
else
{
lean_object* x_92; 
x_92 = l_Repr_addAppParen___closed__2;
x_3 = x_92;
goto block_9;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_reprSourceInfo___closed__1____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_reprSourceInfo____x40_Init_Data_Repr_413755464____hygCtx___hyg_3____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_reprSourceInfo____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_instReprSourceInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_reprSourceInfo____x40_Init_Data_Repr_413755464____hygCtx___hyg_3____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instReprSourceInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_instReprSourceInfo___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_Format_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Repr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Format_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_reprStr___redArg___closed__0 = _init_l_reprStr___redArg___closed__0();
lean_mark_persistent(l_reprStr___redArg___closed__0);
l_instReprEmpty = _init_l_instReprEmpty();
lean_mark_persistent(l_instReprEmpty);
l_Bool_repr___redArg___closed__0 = _init_l_Bool_repr___redArg___closed__0();
lean_mark_persistent(l_Bool_repr___redArg___closed__0);
l_Bool_repr___redArg___closed__1 = _init_l_Bool_repr___redArg___closed__1();
lean_mark_persistent(l_Bool_repr___redArg___closed__1);
l_Bool_repr___redArg___closed__2 = _init_l_Bool_repr___redArg___closed__2();
lean_mark_persistent(l_Bool_repr___redArg___closed__2);
l_Bool_repr___redArg___closed__3 = _init_l_Bool_repr___redArg___closed__3();
lean_mark_persistent(l_Bool_repr___redArg___closed__3);
l_instReprBool___closed__0 = _init_l_instReprBool___closed__0();
lean_mark_persistent(l_instReprBool___closed__0);
l_instReprBool = _init_l_instReprBool();
lean_mark_persistent(l_instReprBool);
l_Repr_addAppParen___closed__0 = _init_l_Repr_addAppParen___closed__0();
lean_mark_persistent(l_Repr_addAppParen___closed__0);
l_Repr_addAppParen___closed__1 = _init_l_Repr_addAppParen___closed__1();
lean_mark_persistent(l_Repr_addAppParen___closed__1);
l_Repr_addAppParen___closed__2 = _init_l_Repr_addAppParen___closed__2();
lean_mark_persistent(l_Repr_addAppParen___closed__2);
l_Repr_addAppParen___closed__3 = _init_l_Repr_addAppParen___closed__3();
lean_mark_persistent(l_Repr_addAppParen___closed__3);
l_Repr_addAppParen___closed__4 = _init_l_Repr_addAppParen___closed__4();
lean_mark_persistent(l_Repr_addAppParen___closed__4);
l_Decidable_repr___redArg___closed__0 = _init_l_Decidable_repr___redArg___closed__0();
lean_mark_persistent(l_Decidable_repr___redArg___closed__0);
l_Decidable_repr___redArg___closed__1 = _init_l_Decidable_repr___redArg___closed__1();
lean_mark_persistent(l_Decidable_repr___redArg___closed__1);
l_Decidable_repr___redArg___closed__2 = _init_l_Decidable_repr___redArg___closed__2();
lean_mark_persistent(l_Decidable_repr___redArg___closed__2);
l_Decidable_repr___redArg___closed__3 = _init_l_Decidable_repr___redArg___closed__3();
lean_mark_persistent(l_Decidable_repr___redArg___closed__3);
l_instReprDecidable___closed__0 = _init_l_instReprDecidable___closed__0();
lean_mark_persistent(l_instReprDecidable___closed__0);
l_instReprPUnit___lam__0___closed__0 = _init_l_instReprPUnit___lam__0___closed__0();
lean_mark_persistent(l_instReprPUnit___lam__0___closed__0);
l_instReprPUnit___lam__0___closed__1 = _init_l_instReprPUnit___lam__0___closed__1();
lean_mark_persistent(l_instReprPUnit___lam__0___closed__1);
l_instReprPUnit = _init_l_instReprPUnit();
lean_mark_persistent(l_instReprPUnit);
l_instReprULift___redArg___lam__0___closed__0 = _init_l_instReprULift___redArg___lam__0___closed__0();
lean_mark_persistent(l_instReprULift___redArg___lam__0___closed__0);
l_instReprULift___redArg___lam__0___closed__1 = _init_l_instReprULift___redArg___lam__0___closed__1();
lean_mark_persistent(l_instReprULift___redArg___lam__0___closed__1);
l_instReprUnit___lam__0___closed__0 = _init_l_instReprUnit___lam__0___closed__0();
lean_mark_persistent(l_instReprUnit___lam__0___closed__0);
l_instReprUnit___lam__0___closed__1 = _init_l_instReprUnit___lam__0___closed__1();
lean_mark_persistent(l_instReprUnit___lam__0___closed__1);
l_instReprUnit = _init_l_instReprUnit();
lean_mark_persistent(l_instReprUnit);
l_Option_repr___redArg___closed__0 = _init_l_Option_repr___redArg___closed__0();
lean_mark_persistent(l_Option_repr___redArg___closed__0);
l_Option_repr___redArg___closed__1 = _init_l_Option_repr___redArg___closed__1();
lean_mark_persistent(l_Option_repr___redArg___closed__1);
l_Option_repr___redArg___closed__2 = _init_l_Option_repr___redArg___closed__2();
lean_mark_persistent(l_Option_repr___redArg___closed__2);
l_Option_repr___redArg___closed__3 = _init_l_Option_repr___redArg___closed__3();
lean_mark_persistent(l_Option_repr___redArg___closed__3);
l_Sum_repr___redArg___closed__0 = _init_l_Sum_repr___redArg___closed__0();
lean_mark_persistent(l_Sum_repr___redArg___closed__0);
l_Sum_repr___redArg___closed__1 = _init_l_Sum_repr___redArg___closed__1();
lean_mark_persistent(l_Sum_repr___redArg___closed__1);
l_Sum_repr___redArg___closed__2 = _init_l_Sum_repr___redArg___closed__2();
lean_mark_persistent(l_Sum_repr___redArg___closed__2);
l_Sum_repr___redArg___closed__3 = _init_l_Sum_repr___redArg___closed__3();
lean_mark_persistent(l_Sum_repr___redArg___closed__3);
l_Prod_repr___redArg___closed__0 = _init_l_Prod_repr___redArg___closed__0();
lean_mark_persistent(l_Prod_repr___redArg___closed__0);
l_Prod_repr___redArg___closed__1 = _init_l_Prod_repr___redArg___closed__1();
lean_mark_persistent(l_Prod_repr___redArg___closed__1);
l_Prod_repr___redArg___closed__2 = _init_l_Prod_repr___redArg___closed__2();
lean_mark_persistent(l_Prod_repr___redArg___closed__2);
l_Prod_repr___redArg___closed__3 = _init_l_Prod_repr___redArg___closed__3();
lean_mark_persistent(l_Prod_repr___redArg___closed__3);
l_Prod_repr___redArg___closed__4 = _init_l_Prod_repr___redArg___closed__4();
lean_mark_persistent(l_Prod_repr___redArg___closed__4);
l_Sigma_repr___redArg___closed__0 = _init_l_Sigma_repr___redArg___closed__0();
lean_mark_persistent(l_Sigma_repr___redArg___closed__0);
l_Sigma_repr___redArg___closed__1 = _init_l_Sigma_repr___redArg___closed__1();
lean_mark_persistent(l_Sigma_repr___redArg___closed__1);
l_Sigma_repr___redArg___closed__2 = _init_l_Sigma_repr___redArg___closed__2();
lean_mark_persistent(l_Sigma_repr___redArg___closed__2);
l_Sigma_repr___redArg___closed__3 = _init_l_Sigma_repr___redArg___closed__3();
lean_mark_persistent(l_Sigma_repr___redArg___closed__3);
l_Sigma_repr___redArg___closed__4 = _init_l_Sigma_repr___redArg___closed__4();
lean_mark_persistent(l_Sigma_repr___redArg___closed__4);
l_Sigma_repr___redArg___closed__5 = _init_l_Sigma_repr___redArg___closed__5();
lean_mark_persistent(l_Sigma_repr___redArg___closed__5);
l___private_Init_Data_Repr_0__Nat_reprArray___closed__0 = _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0();
lean_mark_persistent(l___private_Init_Data_Repr_0__Nat_reprArray___closed__0);
l___private_Init_Data_Repr_0__Nat_reprArray = _init_l___private_Init_Data_Repr_0__Nat_reprArray();
lean_mark_persistent(l___private_Init_Data_Repr_0__Nat_reprArray);
l_Nat_reprFast___closed__0 = _init_l_Nat_reprFast___closed__0();
lean_mark_persistent(l_Nat_reprFast___closed__0);
l_Nat_reprFast___closed__1 = _init_l_Nat_reprFast___closed__1();
lean_mark_persistent(l_Nat_reprFast___closed__1);
l_instReprNat = _init_l_instReprNat();
lean_mark_persistent(l_instReprNat);
l_Int_repr___closed__0 = _init_l_Int_repr___closed__0();
lean_mark_persistent(l_Int_repr___closed__0);
l_Int_repr___closed__1 = _init_l_Int_repr___closed__1();
lean_mark_persistent(l_Int_repr___closed__1);
l_instReprInt = _init_l_instReprInt();
lean_mark_persistent(l_instReprInt);
l_hexDigitRepr___closed__0 = _init_l_hexDigitRepr___closed__0();
lean_mark_persistent(l_hexDigitRepr___closed__0);
l_Char_quoteCore___closed__0 = _init_l_Char_quoteCore___closed__0();
lean_mark_persistent(l_Char_quoteCore___closed__0);
l_Char_quoteCore___closed__1 = _init_l_Char_quoteCore___closed__1();
lean_mark_persistent(l_Char_quoteCore___closed__1);
l_Char_quoteCore___closed__2 = _init_l_Char_quoteCore___closed__2();
lean_mark_persistent(l_Char_quoteCore___closed__2);
l_Char_quoteCore___closed__3 = _init_l_Char_quoteCore___closed__3();
lean_mark_persistent(l_Char_quoteCore___closed__3);
l_Char_quoteCore___closed__4 = _init_l_Char_quoteCore___closed__4();
lean_mark_persistent(l_Char_quoteCore___closed__4);
l_Char_quoteCore___closed__5 = _init_l_Char_quoteCore___closed__5();
lean_mark_persistent(l_Char_quoteCore___closed__5);
l_Char_quote___closed__0 = _init_l_Char_quote___closed__0();
lean_mark_persistent(l_Char_quote___closed__0);
l_instReprChar = _init_l_instReprChar();
lean_mark_persistent(l_instReprChar);
l_String_quote___closed__0 = _init_l_String_quote___closed__0();
lean_mark_persistent(l_String_quote___closed__0);
l_String_quote___closed__1 = _init_l_String_quote___closed__1();
lean_mark_persistent(l_String_quote___closed__1);
l_instReprString = _init_l_instReprString();
lean_mark_persistent(l_instReprString);
l_instReprPos___lam__0___closed__0 = _init_l_instReprPos___lam__0___closed__0();
lean_mark_persistent(l_instReprPos___lam__0___closed__0);
l_instReprPos___lam__0___closed__1 = _init_l_instReprPos___lam__0___closed__1();
lean_mark_persistent(l_instReprPos___lam__0___closed__1);
l_instReprPos___lam__0___closed__2 = _init_l_instReprPos___lam__0___closed__2();
lean_mark_persistent(l_instReprPos___lam__0___closed__2);
l_instReprPos___lam__0___closed__3 = _init_l_instReprPos___lam__0___closed__3();
lean_mark_persistent(l_instReprPos___lam__0___closed__3);
l_instReprPos = _init_l_instReprPos();
lean_mark_persistent(l_instReprPos);
l_instReprSubstring___lam__0___closed__0 = _init_l_instReprSubstring___lam__0___closed__0();
lean_mark_persistent(l_instReprSubstring___lam__0___closed__0);
l_instReprSubstring = _init_l_instReprSubstring();
lean_mark_persistent(l_instReprSubstring);
l_instReprIterator___lam__0___closed__0 = _init_l_instReprIterator___lam__0___closed__0();
lean_mark_persistent(l_instReprIterator___lam__0___closed__0);
l_instReprIterator___lam__0___closed__1 = _init_l_instReprIterator___lam__0___closed__1();
lean_mark_persistent(l_instReprIterator___lam__0___closed__1);
l_instReprIterator___lam__0___closed__2 = _init_l_instReprIterator___lam__0___closed__2();
lean_mark_persistent(l_instReprIterator___lam__0___closed__2);
l_instReprIterator___lam__0___closed__3 = _init_l_instReprIterator___lam__0___closed__3();
lean_mark_persistent(l_instReprIterator___lam__0___closed__3);
l_instReprIterator = _init_l_instReprIterator();
lean_mark_persistent(l_instReprIterator);
l_instReprUInt8 = _init_l_instReprUInt8();
lean_mark_persistent(l_instReprUInt8);
l_instReprUInt16 = _init_l_instReprUInt16();
lean_mark_persistent(l_instReprUInt16);
l_instReprUInt32 = _init_l_instReprUInt32();
lean_mark_persistent(l_instReprUInt32);
l_instReprUInt64 = _init_l_instReprUInt64();
lean_mark_persistent(l_instReprUInt64);
l_instReprUSize = _init_l_instReprUSize();
lean_mark_persistent(l_instReprUSize);
l_List_repr___redArg___closed__0 = _init_l_List_repr___redArg___closed__0();
lean_mark_persistent(l_List_repr___redArg___closed__0);
l_List_repr___redArg___closed__1 = _init_l_List_repr___redArg___closed__1();
lean_mark_persistent(l_List_repr___redArg___closed__1);
l_List_repr___redArg___closed__2 = _init_l_List_repr___redArg___closed__2();
lean_mark_persistent(l_List_repr___redArg___closed__2);
l_List_repr___redArg___closed__3 = _init_l_List_repr___redArg___closed__3();
lean_mark_persistent(l_List_repr___redArg___closed__3);
l_List_repr___redArg___closed__4 = _init_l_List_repr___redArg___closed__4();
lean_mark_persistent(l_List_repr___redArg___closed__4);
l_List_repr___redArg___closed__5 = _init_l_List_repr___redArg___closed__5();
lean_mark_persistent(l_List_repr___redArg___closed__5);
l_instReprAtomBool = _init_l_instReprAtomBool();
lean_mark_persistent(l_instReprAtomBool);
l_instReprAtomNat = _init_l_instReprAtomNat();
lean_mark_persistent(l_instReprAtomNat);
l_instReprAtomInt = _init_l_instReprAtomInt();
lean_mark_persistent(l_instReprAtomInt);
l_instReprAtomChar = _init_l_instReprAtomChar();
lean_mark_persistent(l_instReprAtomChar);
l_instReprAtomString = _init_l_instReprAtomString();
lean_mark_persistent(l_instReprAtomString);
l_instReprAtomUInt8 = _init_l_instReprAtomUInt8();
lean_mark_persistent(l_instReprAtomUInt8);
l_instReprAtomUInt16 = _init_l_instReprAtomUInt16();
lean_mark_persistent(l_instReprAtomUInt16);
l_instReprAtomUInt32 = _init_l_instReprAtomUInt32();
lean_mark_persistent(l_instReprAtomUInt32);
l_instReprAtomUInt64 = _init_l_instReprAtomUInt64();
lean_mark_persistent(l_instReprAtomUInt64);
l_instReprAtomUSize = _init_l_instReprAtomUSize();
lean_mark_persistent(l_instReprAtomUSize);
l_reprSourceInfo___closed__0____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__0____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__0____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__1____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__1____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__1____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__2____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__2____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__2____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__3____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__3____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__3____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__4____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__4____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__4____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__5____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__6____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__6____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__6____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__7____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__7____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__7____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_reprSourceInfo___closed__8____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_ = _init_l_reprSourceInfo___closed__8____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_();
lean_mark_persistent(l_reprSourceInfo___closed__8____x40_Init_Data_Repr_413755464____hygCtx___hyg_3_);
l_instReprSourceInfo___closed__0 = _init_l_instReprSourceInfo___closed__0();
lean_mark_persistent(l_instReprSourceInfo___closed__0);
l_instReprSourceInfo = _init_l_instReprSourceInfo();
lean_mark_persistent(l_instReprSourceInfo);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
