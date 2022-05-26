// Lean compiler output
// Module: Lean.Elab.BindersUtil
// Imports: Init Lean.Parser.Term
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
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_nullKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__9;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6;
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2;
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isNone(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_mkHole(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandOptType(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Syntax_getArg(x_6, x_2);
lean_dec(x_6);
x_8 = l_Lean_Syntax_getSepArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_box(2);
x_12 = l_Lean_nullKind;
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_15 = l_Lean_Syntax_setArg(x_1, x_14, x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_8, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_nat_dec_le(x_5, x_2);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = l_Lean_Syntax_getSepArgs(x_3);
lean_dec(x_3);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1(x_1, x_9, x_10, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1;
x_13 = lean_array_push(x_12, x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_shouldExpandMatchAlt(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Term_shouldExpandMatchAlt(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Elab_Term_expandMatchAlt(x_6);
x_8 = l_Array_append___rarg(x_4, x_7);
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
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlts", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("match", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
x_3 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__8;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1;
x_14 = lean_name_mk_string(x_2, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
lean_dec(x_12);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_18, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_31 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1(x_20, x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_34 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2;
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(x_20, x_29, x_30, x_34);
lean_dec(x_20);
x_36 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_7, x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
lean_inc(x_37);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_append___rarg(x_34, x_21);
x_43 = lean_box(2);
x_44 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
x_46 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__6;
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_append___rarg(x_34, x_35);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_48);
x_50 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1;
x_51 = lean_array_push(x_50, x_49);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_14);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__7;
x_54 = lean_array_push(x_53, x_41);
if (lean_obj_tag(x_4) == 0)
{
x_55 = x_34;
goto block_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 0);
lean_inc(x_90);
lean_dec(x_4);
x_91 = lean_array_push(x_50, x_90);
x_55 = x_91;
goto block_89;
}
block_89:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Array_append___rarg(x_34, x_55);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_array_push(x_54, x_57);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__9;
x_60 = lean_array_push(x_58, x_59);
x_61 = lean_array_push(x_60, x_45);
x_62 = lean_array_push(x_61, x_47);
x_63 = lean_array_push(x_62, x_52);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_43);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_39)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_39;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_38);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_6);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_6, 0);
x_69 = lean_array_push(x_50, x_68);
x_70 = l_Array_append___rarg(x_34, x_69);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_43);
lean_ctor_set(x_71, 1, x_44);
lean_ctor_set(x_71, 2, x_70);
x_72 = lean_array_push(x_58, x_71);
x_73 = lean_array_push(x_72, x_45);
x_74 = lean_array_push(x_73, x_47);
x_75 = lean_array_push(x_74, x_52);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_43);
lean_ctor_set(x_76, 1, x_3);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_6, 0, x_76);
if (lean_is_scalar(x_39)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_39;
}
lean_ctor_set(x_77, 0, x_6);
lean_ctor_set(x_77, 1, x_38);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_ctor_get(x_6, 0);
lean_inc(x_78);
lean_dec(x_6);
x_79 = lean_array_push(x_50, x_78);
x_80 = l_Array_append___rarg(x_34, x_79);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_43);
lean_ctor_set(x_81, 1, x_44);
lean_ctor_set(x_81, 2, x_80);
x_82 = lean_array_push(x_58, x_81);
x_83 = lean_array_push(x_82, x_45);
x_84 = lean_array_push(x_83, x_47);
x_85 = lean_array_push(x_84, x_52);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_43);
lean_ctor_set(x_86, 1, x_3);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_39)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_39;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_38);
return x_88;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_nullKind;
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_13 = l_Lean_Syntax_isNodeOf(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(x_1, x_2, x_3, x_5, x_19, x_18, x_6, x_7);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(x_1, x_2, x_3, x_5, x_22, x_21, x_6, x_7);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2;
x_2 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4;
x_2 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6;
x_2 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_nullKind;
lean_inc(x_9);
x_12 = l_Lean_Syntax_isNodeOf(x_9, x_11, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_9, x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6;
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(x_1, x_18, x_4, x_19, x_17, x_2, x_3);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6;
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(x_1, x_22, x_4, x_23, x_21, x_2, x_3);
lean_dec(x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BindersUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__1___closed__1);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__6 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__6);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__7 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__7);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__8 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__8);
l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__9 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__9);
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1);
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2);
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3);
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4);
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5);
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6);
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
