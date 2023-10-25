// Lean compiler output
// Module: Lean.Compiler.LCNF.FixedParams
// Imports: Init Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.Types
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_FixedParams_evalFVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_hashAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_118____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__15(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FixedParams_abort___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5(lean_object*, size_t, size_t, uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue;
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_FixedParams_evalFVar___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_mkInitialValues___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_FixedParams_State_visited___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_mkAssignment___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_inMutualBlock___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_mkInitialValues___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_FixedParams_State_visited___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__9___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__10(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue;
static lean_object* l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_hashAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_118_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_inMutualBlock___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_mkAssignment___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_State_visited___default;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__16(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___rarg(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FixedParams_abort___spec__1(size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__15___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__1;
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23_(lean_object* x_1, lean_object* x_2) {
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
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_nat_dec_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_hashAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_118_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 2;
x_6 = lean_uint64_of_nat(x_4);
x_7 = lean_uint64_mix_hash(x_5, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_hashAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_118____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_hashAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_118_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_hashAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_118____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_FixedParams_State_visited___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_State_visited___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_FixedParams_State_visited___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSet___at_Lean_Compiler_LCNF_FixedParams_State_visited___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FixedParams_abort___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_array_uset(x_6, x_2, x_10);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FixedParams_abort___spec__1(x_5, x_6, x_3);
lean_ctor_set(x_1, 1, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FixedParams_abort___spec__1(x_13, x_14, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FixedParams_abort___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FixedParams_abort___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FixedParams_abort___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_FixedParams_abort(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_FixedParams_evalFVar___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_FixedParams_evalFVar___spec__1(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_FixedParams_evalFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_FixedParams_evalFVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_FixedParams_evalFVar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_Compiler_LCNF_FixedParams_evalFVar(x_6, x_2, x_3);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_Lean_Compiler_LCNF_FixedParams_evalFVar(x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_FixedParams_evalArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_inMutualBlock___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_inMutualBlock___spec__1(x_1, x_4, x_11, x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_inMutualBlock___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_inMutualBlock___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_mkAssignment___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
return x_4;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_15 = lean_ctor_get(x_8, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_array_fget(x_10, x_11);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_11, x_19);
lean_dec(x_11);
lean_ctor_set(x_8, 1, x_20);
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_9, x_21, x_18);
lean_ctor_set(x_4, 1, x_22);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_8);
x_26 = lean_array_fget(x_10, x_11);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_12);
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
x_31 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_9, x_30, x_26);
lean_ctor_set(x_4, 1, x_31);
lean_ctor_set(x_4, 0, x_29);
x_32 = 1;
x_33 = lean_usize_add(x_3, x_32);
x_3 = x_33;
goto _start;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_4, 0);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_4);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 2);
lean_inc(x_39);
x_40 = lean_nat_dec_lt(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_6);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_42 = x_35;
} else {
 lean_dec_ref(x_35);
 x_42 = lean_box(0);
}
x_43 = lean_array_fget(x_37, x_38);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_38, x_44);
lean_dec(x_38);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_39);
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
lean_dec(x_6);
x_48 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_36, x_47, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_3, x_50);
x_3 = x_51;
x_4 = x_49;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_box(0);
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_toSubarray___rarg(x_2, x_5, x_4);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_array_get_size(x_7);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_mkAssignment___spec__1(x_7, x_10, x_11, x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_mkAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_mkAssignment___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Compiler_LCNF_FixedParams_evalApp(x_4, x_5, x_2, x_3);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_3, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(0);
x_17 = lean_array_push(x_6, x_16);
x_18 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_13;
x_3 = x_18;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_array_fget(x_1, x_3);
x_21 = l_Lean_Compiler_LCNF_FixedParams_evalArg(x_20, x_7, x_8);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_push(x_6, x_22);
x_25 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_13;
x_3 = x_25;
x_6 = x_24;
x_8 = x_23;
goto _start;
}
}
else
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23_(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_name_eq(x_6, x_8);
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_7);
x_13 = lean_array_get_size(x_9);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__4(x_7, x_9, lean_box(0), x_7, x_9, x_16);
if (x_17 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
}
}
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_hashAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_118_(x_6);
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
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_Name_hash___override(x_5);
lean_dec(x_5);
x_8 = 7;
x_9 = lean_array_get_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
uint64_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_6);
x_12 = lean_uint64_mix_hash(x_7, x_8);
x_13 = lean_hashset_mk_idx(x_4, x_12);
x_14 = lean_array_uget(x_3, x_13);
lean_dec(x_3);
x_15 = l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3(x_2, x_14);
lean_dec(x_14);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_9, x_9);
if (x_16 == 0)
{
uint64_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_6);
x_17 = lean_uint64_mix_hash(x_7, x_8);
x_18 = lean_hashset_mk_idx(x_4, x_17);
x_19 = lean_array_uget(x_3, x_18);
lean_dec(x_3);
x_20 = l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3(x_2, x_19);
lean_dec(x_19);
lean_dec(x_2);
return x_20;
}
else
{
size_t x_21; size_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5(x_6, x_21, x_22, x_8);
lean_dec(x_6);
x_24 = lean_uint64_mix_hash(x_7, x_23);
x_25 = lean_hashset_mk_idx(x_4, x_24);
x_26 = lean_array_uget(x_3, x_25);
lean_dec(x_3);
x_27 = l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3(x_2, x_26);
lean_dec(x_26);
lean_dec(x_2);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__9___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
x_10 = 7;
x_11 = lean_array_get_size(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint64_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_8);
x_14 = lean_uint64_mix_hash(x_9, x_10);
x_15 = lean_hashset_mk_idx(x_6, x_14);
x_16 = lean_array_uget(x_1, x_15);
lean_ctor_set(x_2, 1, x_16);
x_17 = lean_array_uset(x_1, x_15, x_2);
x_1 = x_17;
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_11, x_11);
if (x_19 == 0)
{
uint64_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_8);
x_20 = lean_uint64_mix_hash(x_9, x_10);
x_21 = lean_hashset_mk_idx(x_6, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 1, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
size_t x_25; size_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5(x_8, x_25, x_26, x_10);
lean_dec(x_8);
x_28 = lean_uint64_mix_hash(x_9, x_27);
x_29 = lean_hashset_mk_idx(x_6, x_28);
x_30 = lean_array_uget(x_1, x_29);
lean_ctor_set(x_2, 1, x_30);
x_31 = lean_array_uset(x_1, x_29, x_2);
x_1 = x_31;
x_2 = x_5;
goto _start;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_array_get_size(x_1);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
x_38 = l_Lean_Name_hash___override(x_36);
lean_dec(x_36);
x_39 = 7;
x_40 = lean_array_get_size(x_37);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_lt(x_41, x_40);
if (x_42 == 0)
{
uint64_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_40);
lean_dec(x_37);
x_43 = lean_uint64_mix_hash(x_38, x_39);
x_44 = lean_hashset_mk_idx(x_35, x_43);
x_45 = lean_array_uget(x_1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_uset(x_1, x_44, x_46);
x_1 = x_47;
x_2 = x_34;
goto _start;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_40, x_40);
if (x_49 == 0)
{
uint64_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_40);
lean_dec(x_37);
x_50 = lean_uint64_mix_hash(x_38, x_39);
x_51 = lean_hashset_mk_idx(x_35, x_50);
x_52 = lean_array_uget(x_1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_33);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_uset(x_1, x_51, x_53);
x_1 = x_54;
x_2 = x_34;
goto _start;
}
else
{
size_t x_56; size_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5(x_37, x_56, x_57, x_39);
lean_dec(x_37);
x_59 = lean_uint64_mix_hash(x_38, x_58);
x_60 = lean_hashset_mk_idx(x_35, x_59);
x_61 = lean_array_uget(x_1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_33);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_array_uset(x_1, x_60, x_62);
x_1 = x_63;
x_2 = x_34;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_List_foldl___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__9___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__10(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__8(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23_(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_name_eq(x_8, x_10);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_9);
x_15 = lean_array_get_size(x_11);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
x_17 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__12(x_9, x_11, lean_box(0), x_9, x_11, x_18);
lean_dec(x_9);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_name_eq(x_23, x_25);
lean_dec(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
x_28 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_22, x_2, x_3);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_get_size(x_24);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
x_33 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_22, x_2, x_3);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__12(x_24, x_26, lean_box(0), x_24, x_26, x_35);
lean_dec(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_22, x_2, x_3);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_22);
return x_39;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
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
x_6 = lean_array_get_size(x_4);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = l_Lean_Name_hash___override(x_22);
lean_dec(x_22);
x_25 = 7;
x_26 = lean_array_get_size(x_23);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_28 == 0)
{
uint64_t x_29; 
lean_dec(x_26);
lean_dec(x_23);
x_29 = lean_uint64_mix_hash(x_24, x_25);
x_7 = x_29;
goto block_21;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
uint64_t x_31; 
lean_dec(x_26);
lean_dec(x_23);
x_31 = lean_uint64_mix_hash(x_24, x_25);
x_7 = x_31;
goto block_21;
}
else
{
size_t x_32; size_t x_33; uint64_t x_34; uint64_t x_35; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5(x_23, x_32, x_33, x_25);
lean_dec(x_23);
x_35 = lean_uint64_mix_hash(x_24, x_34);
x_7 = x_35;
goto block_21;
}
}
block_21:
{
size_t x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_6);
x_8 = lean_hashset_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_4, x_8);
x_10 = l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_array_uset(x_4, x_8, x_13);
x_15 = lean_nat_dec_le(x_12, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = l_Lean_HashSetImp_expand___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__7(x_12, x_14);
return x_16;
}
else
{
lean_object* x_17; 
if (lean_is_scalar(x_5)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_5;
}
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_inc(x_2);
x_18 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_9, x_2, x_2);
lean_dec(x_2);
x_19 = lean_array_uset(x_4, x_8, x_18);
if (lean_is_scalar(x_5)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_5;
}
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_11 = lean_array_uget(x_3, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_name_eq(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; lean_object* x_16; 
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_16 = lean_box(0);
x_5 = x_15;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_11, 3);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___closed__1;
lean_inc(x_19);
x_23 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__1(x_2, x_19, x_20, x_19, x_21, x_22, x_7, x_8);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
lean_inc(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_27);
x_29 = l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__2(x_27, x_26);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_25, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__6(x_27, x_26);
lean_ctor_set(x_25, 0, x_33);
x_34 = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(x_11, x_24);
x_35 = lean_ctor_get(x_11, 4);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
x_39 = l_Lean_Compiler_LCNF_FixedParams_evalCode(x_35, x_38, x_25);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = 1;
x_42 = lean_usize_add(x_5, x_41);
x_43 = lean_box(0);
x_5 = x_42;
x_6 = x_43;
x_8 = x_40;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_25);
x_49 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__6(x_27, x_26);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_28);
x_51 = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(x_11, x_24);
x_52 = lean_ctor_get(x_11, 4);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_inc(x_53);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_51);
x_56 = l_Lean_Compiler_LCNF_FixedParams_evalCode(x_52, x_55, x_50);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = 1;
x_59 = lean_usize_add(x_5, x_58);
x_60 = lean_box(0);
x_5 = x_59;
x_6 = x_60;
x_8 = x_57;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_1);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
x_66 = 1;
x_67 = lean_usize_add(x_5, x_66);
x_68 = lean_box(0);
x_5 = x_67;
x_6 = x_68;
x_8 = x_25;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_9, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_8, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_11);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_8, x_18);
lean_dec(x_8);
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_lt(x_9, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 1);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_array_set(x_23, x_9, x_25);
lean_ctor_set(x_13, 1, x_26);
x_27 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_28 = lean_box(0);
x_8 = x_19;
x_9 = x_27;
x_10 = lean_box(0);
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_array_set(x_31, x_9, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_37 = lean_box(0);
x_8 = x_19;
x_9 = x_36;
x_10 = lean_box(0);
x_11 = x_37;
x_13 = x_35;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_array_fget(x_2, x_9);
x_40 = lean_array_fget(x_1, x_9);
x_41 = l_Lean_Compiler_LCNF_FixedParams_evalArg(x_40, x_12, x_13);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_9);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_9);
x_45 = l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23_(x_42, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_box(1);
x_47 = l___private_Lean_Compiler_LCNF_FixedParams_0__Lean_Compiler_LCNF_FixedParams_beqAbsValue____x40_Lean_Compiler_LCNF_FixedParams___hyg_23_(x_42, x_46);
lean_dec(x_42);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_43, 1);
x_50 = 0;
x_51 = lean_box(x_50);
x_52 = lean_array_set(x_49, x_9, x_51);
lean_ctor_set(x_43, 1, x_52);
x_53 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_54 = lean_box(0);
x_8 = x_19;
x_9 = x_53;
x_10 = lean_box(0);
x_11 = x_54;
x_13 = x_43;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_43);
x_58 = 0;
x_59 = lean_box(x_58);
x_60 = lean_array_set(x_57, x_9, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_63 = lean_box(0);
x_8 = x_19;
x_9 = x_62;
x_10 = lean_box(0);
x_11 = x_63;
x_13 = x_61;
goto _start;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_39, 2);
lean_inc(x_65);
lean_dec(x_39);
x_66 = l_Lean_Expr_isErased(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_43, 1);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_array_set(x_68, x_9, x_70);
lean_ctor_set(x_43, 1, x_71);
x_72 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_73 = lean_box(0);
x_8 = x_19;
x_9 = x_72;
x_10 = lean_box(0);
x_11 = x_73;
x_13 = x_43;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_43, 0);
x_76 = lean_ctor_get(x_43, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_43);
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_array_set(x_76, x_9, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_82 = lean_box(0);
x_8 = x_19;
x_9 = x_81;
x_10 = lean_box(0);
x_11 = x_82;
x_13 = x_80;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_85 = lean_box(0);
x_8 = x_19;
x_9 = x_84;
x_10 = lean_box(0);
x_11 = x_85;
x_13 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_42);
lean_dec(x_39);
x_87 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_88 = lean_box(0);
x_8 = x_19;
x_9 = x_87;
x_10 = lean_box(0);
x_11 = x_88;
x_13 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_9);
lean_dec(x_8);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_11);
lean_ctor_set(x_90, 1, x_13);
return x_90;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__16(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_1 == 0)
{
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
}
else
{
if (x_7 == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__15(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__16(x_2, x_1, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(0);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13(x_1, x_2, x_6, x_8, x_9, x_10, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_name_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1(x_1, x_2, x_8, x_3, x_4);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_box(0);
lean_inc(x_11);
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__14(x_2, x_10, x_11, x_14, x_12, x_11, x_13, x_11, x_12, lean_box(0), x_15, x_3, x_4);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = 1;
x_22 = l_Array_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__15(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_23; 
lean_free_object(x_16);
x_23 = l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1(x_1, x_2, x_15, x_3, x_18);
lean_dec(x_3);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = 1;
x_27 = l_Array_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__15(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1(x_1, x_2, x_15, x_3, x_24);
lean_dec(x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalCode___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_AltCore_getCode(x_8);
lean_dec(x_8);
lean_inc(x_5);
x_10 = l_Lean_Compiler_LCNF_FixedParams_evalCode(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_1 = x_5;
x_3 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_Compiler_LCNF_FixedParams_evalCode(x_16, x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_1 = x_15;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_24, 4);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_2);
x_27 = l_Lean_Compiler_LCNF_FixedParams_evalCode(x_26, x_2, x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_1 = x_25;
x_3 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_25);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 4:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_array_get_size(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_2);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_36, x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_46 = lean_box(0);
x_47 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalCode___spec__1(x_35, x_44, x_45, x_46, x_2, x_3);
lean_dec(x_35);
return x_47;
}
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__5(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__11(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__16(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__15___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Array_contains___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__15(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_FixedParams_evalApp___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FixedParams_evalApp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FixedParams_evalCode___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_mkInitialValues___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
lean_dec(x_1);
lean_inc(x_2);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_array_push(x_5, x_11);
x_13 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_13;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___closed__1;
lean_inc(x_1);
x_5 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_mkInitialValues___spec__1(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_mkInitialValues___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_FixedParams_mkInitialValues___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(x_9);
x_11 = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(x_7, x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_mk_array(x_9, x_13);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
lean_inc(x_7);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_11);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
x_19 = l_Lean_Compiler_LCNF_FixedParams_evalCode(x_15, x_16, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_21, x_22);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_5 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
lean_inc(x_1);
x_6 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1(x_1, x_1, x_4, x_5, x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue = _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue);
l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__1 = _init_l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__1);
l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue = _init_l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue);
l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__1 = _init_l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__1);
l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue = _init_l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue);
l_Lean_Compiler_LCNF_FixedParams_State_visited___default = _init_l_Lean_Compiler_LCNF_FixedParams_State_visited___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_State_visited___default);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FixedParams_evalApp___spec__13___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkFixedParamsMap___spec__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
