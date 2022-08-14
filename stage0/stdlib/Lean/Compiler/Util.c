// Lean compiler output
// Module: Lean.Compiler.Util
// Imports: Init Lean.Meta.Match.MatcherInfo
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
LEAN_EXPORT uint8_t l_Lean_Compiler_isRuntimeBultinType(lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__6;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isLCProof(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__21;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__38;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_isLcCast_x3f(lean_object*);
static lean_object* l_Lean_Compiler_isCasesApp_x3f___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__42;
static lean_object* l_Lean_Compiler_isLcUnreachable___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_isLcUnreachable___boxed(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__33;
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_isLcCast_x3f___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__18;
static lean_object* l_Lean_Compiler_isLcUnreachable___closed__1;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isLcUnreachable(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_getCtorArity_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__14;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__5;
static lean_object* l_Lean_Compiler_isCasesApp_x3f___closed__4;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__30;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__28;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_isCasesApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__17;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__25;
static lean_object* l_Lean_Compiler_isCasesApp_x3f___closed__1;
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_mkLcProof___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_geNumDiscrs___boxed(lean_object*);
static lean_object* l_Lean_Compiler_isLcCast_x3f___closed__1;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isLcCast_x3f___boxed(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__29;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__24;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__15;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType_go(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__37;
LEAN_EXPORT lean_object* l_Lean_Compiler_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__20;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__32;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__10;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__16;
lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_getCasesInfo_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getCtorArity_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isRuntimeBultinType___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_geNumDiscrs(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__2;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__1;
uint8_t l_Lean_Expr_isLambda(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__39;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_isSimpleLCNF(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__31;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_isLCProof___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isCompilerRelevantMData(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_builtinRuntimeTypes;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__36;
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_isCasesApp_x3f___closed__3;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__40;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__9;
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1___closed__1;
static lean_object* l_Lean_Compiler_isLCProof___closed__2;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__13;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__23;
static lean_object* l_Lean_Compiler_isLCProof___closed__1;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__41;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__34;
lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange(lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__35;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_isCasesApp_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType_go___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__4;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__27;
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__26;
uint8_t l_Lean_Expr_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_getCasesInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_builtinRuntimeTypes___closed__1;
LEAN_EXPORT uint8_t l_Lean_Compiler_isCompilerRelevantMData(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantMData___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isCompilerRelevantMData(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_isLCProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcProof", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isLCProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_isLCProof___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isLCProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Compiler_isLCProof___closed__2;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isLCProof___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isLCProof(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_isLcUnreachable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcUnreachable", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isLcUnreachable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_isLcUnreachable___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isLcUnreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Compiler_isLcUnreachable___closed__2;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isLcUnreachable___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isLcUnreachable(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_isLcCast_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcCast", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isLcCast_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_isLcCast_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isLcCast_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Compiler_isLcCast_x3f___closed__2;
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isLcCast_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_isLcCast_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_isLCProof___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkLcProof___closed__1;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_getPrefix(x_1);
x_7 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 5)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = l_Lean_isCasesOnRecursor(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_5);
x_12 = lean_box(0);
x_13 = l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f___lambda__1(x_1, x_12, x_2, x_3, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_isCasesOnRecursor(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f___lambda__1(x_1, x_20, x_2, x_3, x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1___closed__1;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Util", 18);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Compiler.Util.0.Lean.Compiler.getCasesOnInfo?", 59);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(72u);
x_4 = lean_unsigned_to_nat(48u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_24; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_24 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 6)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 4);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_24, 0, x_29);
x_12 = x_24;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_31, 4);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_12 = x_33;
goto block_23;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__4;
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1(x_35, x_4, x_5, x_34);
x_12 = x_36;
goto block_23;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
x_12 = x_24;
goto block_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_12 = x_40;
goto block_23;
}
}
block_23:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_11, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInductiveVal_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_16, x_19);
x_21 = lean_nat_add(x_20, x_17);
lean_dec(x_17);
x_22 = lean_nat_add(x_21, x_19);
lean_dec(x_21);
x_23 = l_Lean_InductiveVal_numCtors(x_14);
lean_dec(x_14);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_23);
lean_inc(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_19);
lean_inc(x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_19);
x_27 = l_List_redLength___rarg(x_18);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_dec(x_27);
x_29 = l_List_toArrayAux___rarg(x_18, x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2(x_31, x_32, x_29, x_2, x_3, x_15);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_16);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_26);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_16);
lean_ctor_set(x_6, 0, x_36);
lean_ctor_set(x_33, 0, x_6);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
lean_inc(x_16);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_16);
lean_ctor_set(x_39, 2, x_25);
lean_ctor_set(x_39, 3, x_26);
lean_ctor_set(x_39, 4, x_37);
lean_ctor_set(x_39, 5, x_16);
lean_ctor_set(x_6, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_free_object(x_6);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 4);
lean_inc(x_49);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_47, x_50);
x_52 = lean_nat_add(x_51, x_48);
lean_dec(x_48);
x_53 = lean_nat_add(x_52, x_50);
lean_dec(x_52);
x_54 = l_Lean_InductiveVal_numCtors(x_45);
lean_dec(x_45);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_inc(x_53);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_50);
lean_inc(x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_50);
x_58 = l_List_redLength___rarg(x_49);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec(x_58);
x_60 = l_List_toArrayAux___rarg(x_49, x_59);
x_61 = lean_array_get_size(x_60);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = 0;
x_64 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2(x_62, x_63, x_60, x_2, x_3, x_46);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
lean_inc(x_47);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_47);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_68, 3, x_57);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_47);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_47);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_73 = x_64;
} else {
 lean_dec_ref(x_64);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_5);
if (x_75 == 0)
{
return x_5;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_5, 0);
x_77 = lean_ctor_get(x_5, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_5);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_getCasesInfo_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_8, x_1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_12, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getCasesInfo_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_getCasesInfo_x3f___spec__1(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f(x_1, x_2, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = l_Lean_Meta_Match_MatcherInfo_arity(x_12);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(x_12);
x_16 = l_Lean_Meta_Match_MatcherInfo_getAltRange(x_12);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
lean_dec(x_12);
lean_inc(x_14);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_14);
lean_ctor_set(x_6, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_Lean_Meta_Match_MatcherInfo_arity(x_19);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(x_19);
x_23 = l_Lean_Meta_Match_MatcherInfo_getAltRange(x_19);
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
lean_dec(x_19);
lean_inc(x_21);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_29 = x_6;
} else {
 lean_dec_ref(x_6);
 x_29 = lean_box(0);
}
x_30 = l_Lean_Meta_Match_MatcherInfo_arity(x_28);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(x_28);
x_33 = l_Lean_Meta_Match_MatcherInfo_getAltRange(x_28);
x_34 = lean_ctor_get(x_28, 2);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_31);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_31);
if (lean_is_scalar(x_29)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_29;
}
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_getCasesInfo_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_getCasesInfo_x3f___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_geNumDiscrs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_sub(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_geNumDiscrs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_CasesInfo_geNumDiscrs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_7 = l_Lean_Compiler_CasesInfo_updateResultingType_go(x_1, x_5);
x_8 = l_Lean_Expr_lam___override(x_3, x_4, x_7, x_6);
return x_8;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_CasesInfo_updateResultingType_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 5);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_box(0);
x_9 = lean_array_fset(x_2, x_4, x_8);
x_10 = l_Lean_Compiler_CasesInfo_updateResultingType_go(x_3, x_7);
x_11 = lean_array_fset(x_9, x_4, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CasesInfo_updateResultingType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_CasesInfo_updateResultingType(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_isCasesApp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1___closed__1;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_isCasesApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isCasesApp_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info.arity == e.getAppNumArgs\n    ", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isCasesApp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_isCasesApp_x3f___closed__1;
x_2 = l_Lean_Compiler_isCasesApp_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_isCasesApp_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.isCasesApp?", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isCasesApp_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__1;
x_2 = l_Lean_Compiler_isCasesApp_x3f___closed__4;
x_3 = lean_unsigned_to_nat(103u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Compiler_isCasesApp_x3f___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Compiler_getCasesInfo_x3f(x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_21);
lean_dec(x_1);
x_23 = lean_nat_dec_eq(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_8);
lean_dec(x_19);
lean_free_object(x_7);
x_24 = l_Lean_Compiler_isCasesApp_x3f___closed__5;
x_25 = l_panic___at_Lean_Compiler_isCasesApp_x3f___spec__1(x_24, x_2, x_3, x_16);
return x_25;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_28);
lean_dec(x_1);
x_30 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
lean_free_object(x_7);
x_31 = l_Lean_Compiler_isCasesApp_x3f___closed__5;
x_32 = l_panic___at_Lean_Compiler_isCasesApp_x3f___spec__1(x_31, x_2, x_3, x_16);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_7, 0, x_33);
return x_7;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_36 = x_8;
} else {
 lean_dec_ref(x_8);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_38);
lean_dec(x_1);
x_40 = lean_nat_dec_eq(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_35);
x_41 = l_Lean_Compiler_isCasesApp_x3f___closed__5;
x_42 = l_panic___at_Lean_Compiler_isCasesApp_x3f___spec__1(x_41, x_2, x_3, x_34);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_35);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getCtorArity_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 6)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 4);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 4);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_5, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getCtorArity_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_getCtorArity_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isSimpleLCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isLet(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Expr_isLambda(x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 1;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("String", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UInt8", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UInt16", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UInt32", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UInt64", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("USize", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Float", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Thunk", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Task", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Array", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ByteArray", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FloatArray", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__25;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Int", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__27;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__28;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__26;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__29;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__24;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__30;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__22;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__20;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__32;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__18;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__16;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__34;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__14;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__35;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__12;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__36;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__10;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__37;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__8;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__38;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__6;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__39;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__4;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__40;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__2;
x_2 = l_Lean_Compiler_builtinRuntimeTypes___closed__41;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_builtinRuntimeTypes() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_builtinRuntimeTypes___closed__42;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isRuntimeBultinType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Compiler_builtinRuntimeTypes;
x_3 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isRuntimeBultinType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isRuntimeBultinType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_isLCProof___closed__1 = _init_l_Lean_Compiler_isLCProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_isLCProof___closed__1);
l_Lean_Compiler_isLCProof___closed__2 = _init_l_Lean_Compiler_isLCProof___closed__2();
lean_mark_persistent(l_Lean_Compiler_isLCProof___closed__2);
l_Lean_Compiler_isLcUnreachable___closed__1 = _init_l_Lean_Compiler_isLcUnreachable___closed__1();
lean_mark_persistent(l_Lean_Compiler_isLcUnreachable___closed__1);
l_Lean_Compiler_isLcUnreachable___closed__2 = _init_l_Lean_Compiler_isLcUnreachable___closed__2();
lean_mark_persistent(l_Lean_Compiler_isLcUnreachable___closed__2);
l_Lean_Compiler_isLcCast_x3f___closed__1 = _init_l_Lean_Compiler_isLcCast_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_isLcCast_x3f___closed__1);
l_Lean_Compiler_isLcCast_x3f___closed__2 = _init_l_Lean_Compiler_isLcCast_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_isLcCast_x3f___closed__2);
l_Lean_Compiler_mkLcProof___closed__1 = _init_l_Lean_Compiler_mkLcProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcProof___closed__1);
l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1___closed__1 = _init_l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Compiler_Util_0__Lean_Compiler_getCasesOnInfo_x3f___spec__2___closed__4);
l_Lean_Compiler_isCasesApp_x3f___closed__1 = _init_l_Lean_Compiler_isCasesApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_isCasesApp_x3f___closed__1);
l_Lean_Compiler_isCasesApp_x3f___closed__2 = _init_l_Lean_Compiler_isCasesApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_isCasesApp_x3f___closed__2);
l_Lean_Compiler_isCasesApp_x3f___closed__3 = _init_l_Lean_Compiler_isCasesApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_isCasesApp_x3f___closed__3);
l_Lean_Compiler_isCasesApp_x3f___closed__4 = _init_l_Lean_Compiler_isCasesApp_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_isCasesApp_x3f___closed__4);
l_Lean_Compiler_isCasesApp_x3f___closed__5 = _init_l_Lean_Compiler_isCasesApp_x3f___closed__5();
lean_mark_persistent(l_Lean_Compiler_isCasesApp_x3f___closed__5);
l_Lean_Compiler_builtinRuntimeTypes___closed__1 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__1();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__1);
l_Lean_Compiler_builtinRuntimeTypes___closed__2 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__2();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__2);
l_Lean_Compiler_builtinRuntimeTypes___closed__3 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__3();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__3);
l_Lean_Compiler_builtinRuntimeTypes___closed__4 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__4();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__4);
l_Lean_Compiler_builtinRuntimeTypes___closed__5 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__5();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__5);
l_Lean_Compiler_builtinRuntimeTypes___closed__6 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__6();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__6);
l_Lean_Compiler_builtinRuntimeTypes___closed__7 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__7();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__7);
l_Lean_Compiler_builtinRuntimeTypes___closed__8 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__8();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__8);
l_Lean_Compiler_builtinRuntimeTypes___closed__9 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__9();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__9);
l_Lean_Compiler_builtinRuntimeTypes___closed__10 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__10();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__10);
l_Lean_Compiler_builtinRuntimeTypes___closed__11 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__11();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__11);
l_Lean_Compiler_builtinRuntimeTypes___closed__12 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__12();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__12);
l_Lean_Compiler_builtinRuntimeTypes___closed__13 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__13();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__13);
l_Lean_Compiler_builtinRuntimeTypes___closed__14 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__14();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__14);
l_Lean_Compiler_builtinRuntimeTypes___closed__15 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__15();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__15);
l_Lean_Compiler_builtinRuntimeTypes___closed__16 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__16();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__16);
l_Lean_Compiler_builtinRuntimeTypes___closed__17 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__17();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__17);
l_Lean_Compiler_builtinRuntimeTypes___closed__18 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__18();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__18);
l_Lean_Compiler_builtinRuntimeTypes___closed__19 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__19();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__19);
l_Lean_Compiler_builtinRuntimeTypes___closed__20 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__20();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__20);
l_Lean_Compiler_builtinRuntimeTypes___closed__21 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__21();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__21);
l_Lean_Compiler_builtinRuntimeTypes___closed__22 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__22();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__22);
l_Lean_Compiler_builtinRuntimeTypes___closed__23 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__23();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__23);
l_Lean_Compiler_builtinRuntimeTypes___closed__24 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__24();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__24);
l_Lean_Compiler_builtinRuntimeTypes___closed__25 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__25();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__25);
l_Lean_Compiler_builtinRuntimeTypes___closed__26 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__26();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__26);
l_Lean_Compiler_builtinRuntimeTypes___closed__27 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__27();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__27);
l_Lean_Compiler_builtinRuntimeTypes___closed__28 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__28();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__28);
l_Lean_Compiler_builtinRuntimeTypes___closed__29 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__29();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__29);
l_Lean_Compiler_builtinRuntimeTypes___closed__30 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__30();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__30);
l_Lean_Compiler_builtinRuntimeTypes___closed__31 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__31();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__31);
l_Lean_Compiler_builtinRuntimeTypes___closed__32 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__32();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__32);
l_Lean_Compiler_builtinRuntimeTypes___closed__33 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__33();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__33);
l_Lean_Compiler_builtinRuntimeTypes___closed__34 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__34();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__34);
l_Lean_Compiler_builtinRuntimeTypes___closed__35 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__35();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__35);
l_Lean_Compiler_builtinRuntimeTypes___closed__36 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__36();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__36);
l_Lean_Compiler_builtinRuntimeTypes___closed__37 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__37();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__37);
l_Lean_Compiler_builtinRuntimeTypes___closed__38 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__38();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__38);
l_Lean_Compiler_builtinRuntimeTypes___closed__39 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__39();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__39);
l_Lean_Compiler_builtinRuntimeTypes___closed__40 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__40();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__40);
l_Lean_Compiler_builtinRuntimeTypes___closed__41 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__41();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__41);
l_Lean_Compiler_builtinRuntimeTypes___closed__42 = _init_l_Lean_Compiler_builtinRuntimeTypes___closed__42();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes___closed__42);
l_Lean_Compiler_builtinRuntimeTypes = _init_l_Lean_Compiler_builtinRuntimeTypes();
lean_mark_persistent(l_Lean_Compiler_builtinRuntimeTypes);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
