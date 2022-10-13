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
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__1;
static lean_object* l_Lean_Elab_Term_clearInMatchAlt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__9;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__4;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__4;
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__8;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
static uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Term_expandMatchAlt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_clearInMatch___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__7;
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__3;
lean_object* l_Array_mkArray4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___rarg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlt___closed__6;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt___lambda__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__2;
lean_object* l_Array_mkArray6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Term_expandMatchAlt___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_clearInMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_clearInMatchAlt___closed__1;
static lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__1;
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
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_mkHole(x_1, x_8);
return x_9;
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
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Term_expandMatchAlt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_1, x_4);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_16);
x_3 = x_12;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_Term_expandMatchAlt___spec__2(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("|", 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_11 = lean_array_uget(x_6, x_5);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_6, x_5, x_12);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_14, x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__1;
lean_inc(x_16);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = l_Array_append___rarg(x_2, x_11);
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3;
lean_inc(x_16);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
x_22 = l_Array_mkArray1___rarg(x_21);
lean_inc(x_16);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__4;
lean_inc(x_16);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_3);
x_26 = l_Array_mkArray4___rarg(x_18, x_23, x_25, x_3);
lean_inc(x_1);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_30 = lean_array_uset(x_13, x_5, x_27);
x_5 = x_29;
x_6 = x_30;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_getArgs(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlt", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandMatchAlt___closed__1;
x_2 = l_Lean_Elab_Term_expandMatchAlt___closed__2;
x_3 = l_Lean_Elab_Term_expandMatchAlt___closed__3;
x_4 = l_Lean_Elab_Term_expandMatchAlt___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlt___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAlt___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_expandMatchAlt___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_expandMatchAlt___closed__6;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
x_34 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
x_15 = x_34;
goto block_33;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_12, x_12);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_12);
lean_dec(x_11);
x_36 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
x_15 = x_36;
goto block_33;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_39 = l_Lean_Elab_Term_expandMatchAlt___closed__8;
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_11, x_37, x_38, x_39);
lean_dec(x_11);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_15 = x_41;
goto block_33;
}
}
block_33:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Elab_Term_expandMatchAlt___closed__9;
x_17 = l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1(x_15, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_18 = l_Lean_Elab_Term_expandMatchAlt___closed__6;
x_19 = lean_array_push(x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_le(x_24, x_9);
if (x_25 == 0)
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_26 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_27 = 0;
x_28 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
x_29 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3(x_4, x_28, x_23, x_26, x_27, x_21, x_2, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_30 = l_Lean_Elab_Term_expandMatchAlt___closed__6;
x_31 = lean_array_push(x_30, x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_Term_expandMatchAlt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_Term_expandMatchAlt___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_expandMatchAlt___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
x_2 = l_Lean_Elab_Term_expandMatchAlt___closed__9;
x_3 = l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1;
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Term_expandMatchAlt___closed__5;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
x_13 = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2;
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Lean_Elab_Term_expandMatchAlt___closed__8;
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_7, x_14, x_15, x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Term_expandMatchAlt___closed__9;
x_20 = l_Array_sequenceMap___at_Lean_Elab_Term_expandMatchAlt___spec__1(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_lt(x_5, x_23);
lean_dec(x_23);
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_shouldExpandMatchAlt(x_1);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lean_Elab_Term_expandMatchAlt(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Array_append___rarg(x_4, x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_12;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandMatchAlt___closed__1;
x_2 = l_Lean_Elab_Term_expandMatchAlt___closed__2;
x_3 = l_Lean_Elab_Term_expandMatchAlt___closed__3;
x_4 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
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
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(5u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_11, x_16);
lean_dec(x_11);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_lt(x_16, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_20, x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_29 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__1(x_18, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
lean_inc(x_6);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(x_18, x_27, x_28, x_32, x_6, x_7);
lean_dec(x_18);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_6, 5);
lean_inc(x_36);
lean_dec(x_6);
x_37 = 0;
x_38 = l_Lean_SourceInfo_fromRef(x_36, x_37);
x_39 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
lean_inc(x_38);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Array_append___rarg(x_32, x_19);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3;
lean_inc(x_38);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_41);
x_44 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4;
lean_inc(x_38);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Array_append___rarg(x_32, x_35);
lean_inc(x_38);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Array_mkArray1___rarg(x_47);
lean_inc(x_38);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_12);
lean_ctor_set(x_49, 2, x_48);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
lean_inc(x_38);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_50);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_51);
x_52 = l_Array_mkArray6___rarg(x_40, x_51, x_51, x_43, x_45, x_49);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_33, 0, x_54);
return x_33;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_5);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_5, 0);
x_57 = l_Array_mkArray1___rarg(x_56);
x_58 = l_Array_append___rarg(x_32, x_57);
lean_inc(x_38);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_42);
lean_ctor_set(x_59, 2, x_58);
x_60 = l_Array_mkArray6___rarg(x_40, x_51, x_59, x_43, x_45, x_49);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_38);
lean_ctor_set(x_61, 1, x_3);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_5, 0, x_61);
lean_ctor_set(x_33, 0, x_5);
return x_33;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_5, 0);
lean_inc(x_62);
lean_dec(x_5);
x_63 = l_Array_mkArray1___rarg(x_62);
x_64 = l_Array_append___rarg(x_32, x_63);
lean_inc(x_38);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_38);
lean_ctor_set(x_65, 1, x_42);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Array_mkArray6___rarg(x_40, x_51, x_65, x_43, x_45, x_49);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_38);
lean_ctor_set(x_67, 1, x_3);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_33, 0, x_68);
return x_33;
}
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_2, 0);
x_71 = l_Array_mkArray1___rarg(x_70);
x_72 = l_Array_append___rarg(x_32, x_71);
lean_inc(x_38);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_38);
lean_ctor_set(x_73, 1, x_42);
lean_ctor_set(x_73, 2, x_72);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
lean_inc(x_38);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_38);
lean_ctor_set(x_75, 1, x_42);
lean_ctor_set(x_75, 2, x_74);
x_76 = l_Array_mkArray6___rarg(x_40, x_73, x_75, x_43, x_45, x_49);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_38);
lean_ctor_set(x_77, 1, x_3);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_2, 0, x_77);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
else
{
uint8_t x_78; 
lean_free_object(x_2);
x_78 = !lean_is_exclusive(x_5);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_5, 0);
x_80 = l_Array_mkArray1___rarg(x_79);
x_81 = l_Array_append___rarg(x_32, x_80);
lean_inc(x_38);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_38);
lean_ctor_set(x_82, 1, x_42);
lean_ctor_set(x_82, 2, x_81);
x_83 = l_Array_mkArray6___rarg(x_40, x_73, x_82, x_43, x_45, x_49);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_38);
lean_ctor_set(x_84, 1, x_3);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_5, 0, x_84);
lean_ctor_set(x_33, 0, x_5);
return x_33;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_5, 0);
lean_inc(x_85);
lean_dec(x_5);
x_86 = l_Array_mkArray1___rarg(x_85);
x_87 = l_Array_append___rarg(x_32, x_86);
lean_inc(x_38);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_42);
lean_ctor_set(x_88, 2, x_87);
x_89 = l_Array_mkArray6___rarg(x_40, x_73, x_88, x_43, x_45, x_49);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_38);
lean_ctor_set(x_90, 1, x_3);
lean_ctor_set(x_90, 2, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_33, 0, x_91);
return x_33;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
x_93 = l_Array_mkArray1___rarg(x_92);
x_94 = l_Array_append___rarg(x_32, x_93);
lean_inc(x_38);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_38);
lean_ctor_set(x_95, 1, x_42);
lean_ctor_set(x_95, 2, x_94);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
lean_inc(x_38);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_38);
lean_ctor_set(x_97, 1, x_42);
lean_ctor_set(x_97, 2, x_96);
x_98 = l_Array_mkArray6___rarg(x_40, x_95, x_97, x_43, x_45, x_49);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_38);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_33, 0, x_100);
return x_33;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_5, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_102 = x_5;
} else {
 lean_dec_ref(x_5);
 x_102 = lean_box(0);
}
x_103 = l_Array_mkArray1___rarg(x_101);
x_104 = l_Array_append___rarg(x_32, x_103);
lean_inc(x_38);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_38);
lean_ctor_set(x_105, 1, x_42);
lean_ctor_set(x_105, 2, x_104);
x_106 = l_Array_mkArray6___rarg(x_40, x_95, x_105, x_43, x_45, x_49);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_38);
lean_ctor_set(x_107, 1, x_3);
lean_ctor_set(x_107, 2, x_106);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_33, 0, x_108);
return x_33;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_109 = lean_ctor_get(x_33, 0);
x_110 = lean_ctor_get(x_33, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_33);
x_111 = lean_ctor_get(x_6, 5);
lean_inc(x_111);
lean_dec(x_6);
x_112 = 0;
x_113 = l_Lean_SourceInfo_fromRef(x_111, x_112);
x_114 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
lean_inc(x_113);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Array_append___rarg(x_32, x_19);
x_117 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3;
lean_inc(x_113);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_116);
x_119 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4;
lean_inc(x_113);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Array_append___rarg(x_32, x_109);
lean_inc(x_113);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_117);
lean_ctor_set(x_122, 2, x_121);
x_123 = l_Array_mkArray1___rarg(x_122);
lean_inc(x_113);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_113);
lean_ctor_set(x_124, 1, x_12);
lean_ctor_set(x_124, 2, x_123);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
lean_inc(x_113);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_113);
lean_ctor_set(x_126, 1, x_117);
lean_ctor_set(x_126, 2, x_125);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_inc(x_126);
x_127 = l_Array_mkArray6___rarg(x_115, x_126, x_126, x_118, x_120, x_124);
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_113);
lean_ctor_set(x_128, 1, x_3);
lean_ctor_set(x_128, 2, x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_110);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_131 = lean_ctor_get(x_5, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_132 = x_5;
} else {
 lean_dec_ref(x_5);
 x_132 = lean_box(0);
}
x_133 = l_Array_mkArray1___rarg(x_131);
x_134 = l_Array_append___rarg(x_32, x_133);
lean_inc(x_113);
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_113);
lean_ctor_set(x_135, 1, x_117);
lean_ctor_set(x_135, 2, x_134);
x_136 = l_Array_mkArray6___rarg(x_115, x_126, x_135, x_118, x_120, x_124);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_113);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_136);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_110);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_2, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_141 = x_2;
} else {
 lean_dec_ref(x_2);
 x_141 = lean_box(0);
}
x_142 = l_Array_mkArray1___rarg(x_140);
x_143 = l_Array_append___rarg(x_32, x_142);
lean_inc(x_113);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_113);
lean_ctor_set(x_144, 1, x_117);
lean_ctor_set(x_144, 2, x_143);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
lean_inc(x_113);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_113);
lean_ctor_set(x_146, 1, x_117);
lean_ctor_set(x_146, 2, x_145);
x_147 = l_Array_mkArray6___rarg(x_115, x_144, x_146, x_118, x_120, x_124);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_113);
lean_ctor_set(x_148, 1, x_3);
lean_ctor_set(x_148, 2, x_147);
if (lean_is_scalar(x_141)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_141;
}
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_110);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_141);
x_151 = lean_ctor_get(x_5, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_152 = x_5;
} else {
 lean_dec_ref(x_5);
 x_152 = lean_box(0);
}
x_153 = l_Array_mkArray1___rarg(x_151);
x_154 = l_Array_append___rarg(x_32, x_153);
lean_inc(x_113);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_113);
lean_ctor_set(x_155, 1, x_117);
lean_ctor_set(x_155, 2, x_154);
x_156 = l_Array_mkArray6___rarg(x_115, x_144, x_155, x_118, x_120, x_124);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_113);
lean_ctor_set(x_157, 1, x_3);
lean_ctor_set(x_157, 2, x_156);
if (lean_is_scalar(x_152)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_152;
}
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_110);
return x_159;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_11 = l_Lean_Syntax_matchesNull(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_8, x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(x_1, x_4, x_2, x_17, x_16, x_5, x_6);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(x_1, x_4, x_2, x_20, x_19, x_5, x_6);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandMatchAlt___closed__1;
x_2 = l_Lean_Elab_Term_expandMatchAlt___closed__2;
x_3 = l_Lean_Elab_Term_expandMatchAlt___closed__3;
x_4 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1;
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
uint8_t x_11; 
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(x_1, x_4, x_17, x_16, x_2, x_3);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(x_1, x_4, x_20, x_19, x_2, x_3);
lean_dec(x_1);
return x_21;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandMatchAlts_x3f___spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("clear", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandMatchAlt___closed__1;
x_2 = l_Lean_Elab_Term_expandMatchAlt___closed__2;
x_3 = l_Lean_Elab_Term_expandMatchAlt___closed__3;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("clear%", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(";", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_9 = lean_array_uget(x_1, x_3);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__3;
lean_inc(x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__4;
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Array_mkArray4___rarg(x_14, x_9, x_16, x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__2;
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_4 = x_19;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_firstFrontendMacroScope;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_clearInMatchAlt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_array_fget(x_4, x_6);
x_9 = lean_box(0);
x_10 = lean_array_fset(x_4, x_6, x_9);
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Lean_Elab_Term_clearInMatchAlt___closed__1;
x_15 = l_Lean_Elab_Term_clearInMatchAlt___closed__2;
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1(x_2, x_12, x_13, x_8, x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_fset(x_10, x_6, x_17);
lean_ctor_set(x_1, 2, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_dec_lt(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_array_fget(x_21, x_23);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_21, x_23, x_27);
x_29 = lean_array_get_size(x_2);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = l_Lean_Elab_Term_clearInMatchAlt___closed__1;
x_33 = l_Lean_Elab_Term_clearInMatchAlt___closed__2;
x_34 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1(x_2, x_30, x_31, x_26, x_32, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_array_fset(x_28, x_23, x_35);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_20);
lean_ctor_set(x_37, 2, x_36);
return x_37;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_clearInMatchAlt(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_clearInMatch___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Elab_Term_clearInMatchAlt(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_12, x_16);
lean_dec(x_12);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_20 = lean_array_get_size(x_18);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_clearInMatch___spec__1(x_2, x_21, x_22, x_18);
x_24 = lean_ctor_get(x_7, 5);
lean_inc(x_24);
lean_dec(x_7);
x_25 = 0;
x_26 = l_Lean_SourceInfo_fromRef(x_24, x_25);
x_27 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__3;
lean_inc(x_26);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Term_expandMatchAlt___closed__7;
x_30 = l_Array_append___rarg(x_29, x_19);
x_31 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3;
lean_inc(x_26);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_30);
x_33 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__4;
lean_inc(x_26);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Array_append___rarg(x_29, x_23);
lean_inc(x_26);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_Array_mkArray1___rarg(x_36);
lean_inc(x_26);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_13);
lean_ctor_set(x_38, 2, x_37);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
lean_inc(x_26);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_39);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_40);
x_41 = l_Array_mkArray6___rarg(x_28, x_40, x_40, x_32, x_34, x_38);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_4);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_6, 0);
lean_inc(x_44);
lean_dec(x_6);
x_45 = l_Array_mkArray1___rarg(x_44);
x_46 = l_Array_append___rarg(x_29, x_45);
lean_inc(x_26);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_31);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Array_mkArray6___rarg(x_28, x_40, x_47, x_32, x_34, x_38);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_26);
lean_ctor_set(x_49, 1, x_4);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_8);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
lean_dec(x_3);
x_52 = l_Array_mkArray1___rarg(x_51);
x_53 = l_Array_append___rarg(x_29, x_52);
lean_inc(x_26);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_31);
lean_ctor_set(x_54, 2, x_53);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = l_Lean_Elab_Term_expandMatchAlts_x3f___lambda__1___closed__5;
lean_inc(x_26);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_26);
lean_ctor_set(x_56, 1, x_31);
lean_ctor_set(x_56, 2, x_55);
x_57 = l_Array_mkArray6___rarg(x_28, x_54, x_56, x_32, x_34, x_38);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_4);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_8);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_6, 0);
lean_inc(x_60);
lean_dec(x_6);
x_61 = l_Array_mkArray1___rarg(x_60);
x_62 = l_Array_append___rarg(x_29, x_61);
lean_inc(x_26);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_31);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Array_mkArray6___rarg(x_28, x_54, x_63, x_32, x_34, x_38);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_26);
lean_ctor_set(x_65, 1, x_4);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = l_Lean_Syntax_matchesNull(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_clearInMatch___lambda__1(x_1, x_2, x_5, x_3, x_17, x_16, x_6, x_7);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_clearInMatch___lambda__1(x_1, x_2, x_5, x_3, x_20, x_19, x_6, x_7);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNone(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_10);
x_12 = l_Lean_Syntax_matchesNull(x_10, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_10, x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_clearInMatch___lambda__2(x_1, x_2, x_6, x_17, x_16, x_4, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_clearInMatch___lambda__2(x_1, x_2, x_6, x_20, x_19, x_4, x_5);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Term_clearInMatch___lambda__3(x_1, x_2, x_6, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_clearInMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_clearInMatch___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_clearInMatch___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_clearInMatch___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_clearInMatch___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_clearInMatch(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAlt___spec__3___closed__4);
l_Lean_Elab_Term_expandMatchAlt___closed__1 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__1);
l_Lean_Elab_Term_expandMatchAlt___closed__2 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__2);
l_Lean_Elab_Term_expandMatchAlt___closed__3 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__3);
l_Lean_Elab_Term_expandMatchAlt___closed__4 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__4);
l_Lean_Elab_Term_expandMatchAlt___closed__5 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__5);
l_Lean_Elab_Term_expandMatchAlt___closed__6 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__6);
l_Lean_Elab_Term_expandMatchAlt___closed__7 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__7);
l_Lean_Elab_Term_expandMatchAlt___closed__8 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__8);
l_Lean_Elab_Term_expandMatchAlt___closed__9 = _init_l_Lean_Elab_Term_expandMatchAlt___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlt___closed__9);
l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1 = _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1);
l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2 = _init_l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2();
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
l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1 = _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_clearInMatchAlt___spec__1___closed__4);
l_Lean_Elab_Term_clearInMatchAlt___closed__1 = _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_clearInMatchAlt___closed__1);
l_Lean_Elab_Term_clearInMatchAlt___closed__2 = _init_l_Lean_Elab_Term_clearInMatchAlt___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_clearInMatchAlt___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
