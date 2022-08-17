// Lean compiler output
// Module: Lean.Compiler.JoinPoints
// Imports: Init Lean.Compiler.CompilerM
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
lean_object* l_Lean_Compiler_visitLetImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_findDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__5;
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_jpArity(lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getLambdaArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__8;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__5;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__9;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__2;
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_jpArity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__3;
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isJp(lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__3;
static lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__5;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__8;
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__9;
lean_object* l_Lean_Compiler_visitMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__4;
static lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__4;
static lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_jpArity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_value(x_1);
x_3 = l_Lean_Compiler_getLambdaArity(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_jpArity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_JoinPointChecker_jpArity(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__2;
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_4(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__3;
x_3 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__4;
x_4 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 2);
x_18 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_3, 2);
x_26 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6;
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
lean_inc(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_5(x_2, x_8, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_withNewScopeImp___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.JoinPoints", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.JoinPointChecker.containsNoJp", 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1;
x_2 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__2;
x_3 = lean_unsigned_to_nat(37u);
x_4 = lean_unsigned_to_nat(39u);
x_5 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1;
x_2 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__2;
x_3 = lean_unsigned_to_nat(33u);
x_4 = lean_unsigned_to_nat(39u);
x_5 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Join point ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" in forbidden position", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_JoinPointChecker_containsNoJp___lambda__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_JoinPointChecker_containsNoJp___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_JoinPointChecker_containsNoJp), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_containsNoJp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_consumeMData(x_1);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_7 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4;
x_8 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Compiler_findDecl_x3f(x_9, x_2, x_3, x_4, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__5;
x_14 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_13, x_2, x_3, x_4, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_Lean_LocalDecl_isJp(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_10);
x_21 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_21, x_22);
x_24 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__7;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2(x_29, x_2, x_3, x_4, x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
lean_dec(x_11);
x_33 = l_Lean_LocalDecl_isJp(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = l_Lean_LocalDecl_userName(x_32);
lean_dec(x_32);
x_37 = 1;
x_38 = l_Lean_Name_toString(x_36, x_37);
x_39 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__7;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2(x_44, x_2, x_3, x_4, x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
}
}
case 2:
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_1);
x_46 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4;
x_47 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_46, x_2, x_3, x_4, x_5);
return x_47;
}
case 5:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_6, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_48, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_1 = x_49;
x_5 = x_51;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_49);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 6:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
x_57 = lean_alloc_closure((void*)(l_Lean_Compiler_visitLambda___boxed), 5, 1);
lean_closure_set(x_57, 0, x_1);
x_58 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__8;
x_59 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg), 6, 2);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_58);
x_60 = l_Lean_Compiler_withNewScopeImp___rarg(x_59, x_2, x_3, x_4, x_5);
return x_60;
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
x_61 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__9;
x_62 = lean_alloc_closure((void*)(l_Lean_Compiler_visitLetImp), 6, 2);
lean_closure_set(x_62, 0, x_1);
lean_closure_set(x_62, 1, x_61);
x_63 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__10;
x_64 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg), 6, 2);
lean_closure_set(x_64, 0, x_62);
lean_closure_set(x_64, 1, x_63);
x_65 = l_Lean_Compiler_withNewScopeImp___rarg(x_64, x_2, x_3, x_4, x_5);
return x_65;
}
case 10:
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_6);
lean_dec(x_1);
x_66 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4;
x_67 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_66, x_2, x_3, x_4, x_5);
return x_67;
}
case 11:
{
lean_object* x_68; 
lean_dec(x_1);
x_68 = lean_ctor_get(x_6, 2);
lean_inc(x_68);
lean_dec(x_6);
x_1 = x_68;
goto _start;
}
default: 
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___lambda__1___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_visitLambda___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___closed__1;
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg), 6, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Compiler_withNewScopeImp___rarg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go(x_10, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_8 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_8 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 2);
x_18 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_3, 2);
x_26 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6;
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
lean_inc(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_12 = x_10;
} else {
 lean_dec_ref(x_10);
 x_12 = lean_box(0);
}
x_13 = lean_array_get_size(x_8);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_8);
x_16 = x_11;
goto block_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_13, x_13);
if (x_29 == 0)
{
lean_dec(x_13);
lean_dec(x_8);
x_16 = x_11;
goto block_28;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_32 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__2(x_8, x_30, x_31, x_32, x_2, x_3, x_4, x_11);
lean_dec(x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_16 = x_34;
goto block_28;
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
block_28:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_9);
x_18 = lean_nat_dec_lt(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_12;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_12;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
x_24 = 0;
x_25 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__1(x_9, x_24, x_25, x_26, x_2, x_3, x_4, x_16);
lean_dec(x_9);
return x_27;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLetValue(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.JoinPointChecker.checkJoinPoints.go", 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1;
x_2 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__1;
x_3 = lean_unsigned_to_nat(85u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1;
x_2 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__1;
x_3 = lean_unsigned_to_nat(66u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not fully applied in ", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__3), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_consumeMData(x_1);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2;
x_8 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2;
x_10 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
case 5:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_findDecl_x3f(x_13, x_2, x_3, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__4;
x_18 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_17, x_2, x_3, x_4, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_LocalDecl_isJp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_6);
x_22 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_12, x_2, x_3, x_4, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_6, x_23);
x_25 = l_Lean_Compiler_JoinPointChecker_jpArity(x_20);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_12);
x_27 = l_Lean_LocalDecl_userName(x_20);
x_28 = 1;
x_29 = l_Lean_Name_toString(x_27, x_28);
x_30 = l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__5;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lean_LocalDecl_type(x_20);
lean_dec(x_20);
x_35 = lean_expr_dbg_to_string(x_34);
lean_dec(x_34);
x_36 = lean_string_append(x_33, x_35);
lean_dec(x_35);
x_37 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__6;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__7;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__3(x_44, x_2, x_3, x_4, x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_20);
lean_dec(x_6);
x_50 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_12, x_2, x_3, x_4, x_19);
return x_50;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_6);
x_51 = l_Lean_Compiler_isCasesApp_x3f(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_6, x_2, x_3, x_4, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_alloc_closure((void*)(l_Lean_Compiler_visitMatch___boxed), 6, 2);
lean_closure_set(x_57, 0, x_6);
lean_closure_set(x_57, 1, x_56);
x_58 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__3;
x_59 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg), 6, 2);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_58);
x_60 = l_Lean_Compiler_withNewScopeImp___rarg(x_59, x_2, x_3, x_4, x_55);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
case 6:
{
lean_object* x_65; 
x_65 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_6, x_2, x_3, x_4, x_5);
return x_65;
}
case 8:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__8;
x_67 = lean_alloc_closure((void*)(l_Lean_Compiler_visitLetImp), 6, 2);
lean_closure_set(x_67, 0, x_6);
lean_closure_set(x_67, 1, x_66);
x_68 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__9;
x_69 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__3___rarg), 6, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
x_70 = l_Lean_Compiler_withNewScopeImp___rarg(x_69, x_2, x_3, x_4, x_5);
return x_70;
}
case 10:
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_6);
x_71 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2;
x_72 = l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1(x_71, x_2, x_3, x_4, x_5);
return x_72;
}
case 11:
{
lean_object* x_73; 
x_73 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_6, x_2, x_3, x_4, x_5);
return x_73;
}
default: 
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_JoinPointChecker_containsNoJp(x_6, x_2, x_3, x_4, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__1(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__2(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_JoinPointChecker_checkJoinPoints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_JoinPoints(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__1);
l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__1___closed__2);
l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__1);
l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__2);
l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__3);
l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__4 = _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__4();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__4);
l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__5 = _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__5();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__5);
l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6 = _init_l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_JoinPointChecker_containsNoJp___spec__2___closed__6);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__1);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__2 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__2();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__2);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__3);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__4);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__5 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__5();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__5);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__6);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__7 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__7();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__7);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__8 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__8();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__8);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__9 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__9();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__9);
l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__10 = _init_l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__10();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_containsNoJp___closed__10);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___closed__1 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_goLambda___closed__1);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__1 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__1);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__2);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__3 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__3);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__4 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__4);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__5 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__5();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__5);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__6 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__6();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__6);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__7 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__7();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__7);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__8 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__8();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__8);
l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__9 = _init_l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__9();
lean_mark_persistent(l_Lean_Compiler_JoinPointChecker_checkJoinPoints_go___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
