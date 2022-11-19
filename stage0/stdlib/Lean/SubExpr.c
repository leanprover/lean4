// Lean compiler output
// Module: Lean.SubExpr
// Imports: Init Lean.Meta.Basic Lean.Data.Json Lean.Data.RBMap
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
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_tail___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToStringPos;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(size_t, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody___boxed(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instToStringPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_depth___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_SubExpr_bindingBody_x21___closed__2;
static lean_object* l_Lean_SubExpr_Pos_instOrdPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_bindingBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instReprPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_toString___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instOrdPos;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn(lean_object*);
static lean_object* l_Lean_instInhabitedSubExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_tail___closed__2;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_fromString_x21___closed__1;
lean_object* l_instOrdNat___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn___boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_root;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__4;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__2;
static lean_object* l_Lean_SubExpr_bindingBody_x21___closed__3;
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain___boxed(lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_isRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody___boxed(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_typeCoord___closed__1;
static lean_object* l_Lean_instInhabitedSubExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_append___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4;
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instReprPos___closed__2;
lean_object* l_panic___at_String_toNat_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEqPos___boxed(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJsonPos___lambda__1(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instInhabitedPos;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instToJsonPos___closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instToJsonPos___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_SubExpr_Pos_toString___spec__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_fromString_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__3;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_push___closed__3;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail(lean_object*);
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_isRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instReprPos___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_Pos_tail___spec__1(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_fromString_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_maxChildren;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instEmptyCollectionPos;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr(lean_object*);
static lean_object* l_Lean_SubExpr_bindingDomain_x21___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_bindingDomain_x21___closed__1;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_toArray___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_push___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_push___closed__1;
LEAN_EXPORT uint8_t l_Lean_SubExpr_isRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at_Lean_SubExpr_Pos_all___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedSubExpr;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_typeCoord;
static lean_object* l_Lean_SubExpr_Pos_toArray___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJsonPos;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_SubExpr_Pos_maxChildren() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_typeCoord___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SubExpr_Pos_maxChildren;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_typeCoord() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_typeCoord___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_asNat(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_root() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instInhabitedPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_root;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_isRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_maxChildren;
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_Pos_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.head", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("already at top", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_Pos_head___closed__2;
x_3 = lean_unsigned_to_nat(36u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_SubExpr_Pos_head___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_maxChildren;
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_SubExpr_Pos_head___closed__4;
x_6 = l_panic___at_String_toNat_x21___spec__1(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_head(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_Pos_tail___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_Pos_instInhabitedPos;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_tail___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.tail", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_tail___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_Pos_tail___closed__1;
x_3 = lean_unsigned_to_nat(40u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_SubExpr_Pos_head___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_maxChildren;
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_SubExpr_Pos_head(x_1);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_nat_div(x_5, x_2);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_SubExpr_Pos_tail___closed__2;
x_8 = l_panic___at_Lean_SubExpr_Pos_tail___spec__1(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_push___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid coordinate ", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_push___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_push___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.push", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_SubExpr_Pos_maxChildren;
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_mul(x_1, x_3);
x_6 = lean_nat_add(x_5, x_2);
lean_dec(x_2);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l_Nat_repr(x_2);
x_8 = l_Lean_SubExpr_Pos_push___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_SubExpr_Pos_push___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_SubExpr_Pos_head___closed__1;
x_13 = l_Lean_SubExpr_Pos_push___closed__3;
x_14 = lean_unsigned_to_nat(44u);
x_15 = lean_unsigned_to_nat(27u);
x_16 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_11);
lean_dec(x_11);
x_17 = l_panic___at_Lean_SubExpr_Pos_tail___spec__1(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_SubExpr_Pos_maxChildren;
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_6 = l_Lean_SubExpr_Pos_tail(x_3);
lean_inc(x_1);
x_7 = l_Lean_SubExpr_Pos_foldl___rarg(x_1, x_2, x_6);
x_8 = l_Lean_SubExpr_Pos_head(x_3);
lean_dec(x_3);
x_9 = lean_apply_2(x_1, x_7, x_8);
return x_9;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldl___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SubExpr_Pos_foldl___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_SubExpr_Pos_maxChildren;
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_6 = l_Lean_SubExpr_Pos_tail(x_2);
x_7 = l_Lean_SubExpr_Pos_head(x_2);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_3);
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldr___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_SubExpr_Pos_head(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_SubExpr_Pos_maxChildren;
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_6);
x_10 = l_Lean_SubExpr_Pos_tail(x_6);
lean_inc(x_4);
x_11 = l_Lean_SubExpr_Pos_foldlM___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_4);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldlM___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_SubExpr_Pos_foldlM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_SubExpr_Pos_maxChildren;
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_SubExpr_Pos_head(x_3);
lean_inc(x_2);
x_9 = lean_apply_2(x_2, x_8, x_4);
x_10 = l_Lean_SubExpr_Pos_tail(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldrM___rarg), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldrM___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_depth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_depth___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_SubExpr_Pos_depth___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_SubExpr_Pos_foldr___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_depth___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at_Lean_SubExpr_Pos_all___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_SubExpr_Pos_maxChildren;
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_SubExpr_Pos_head(x_2);
lean_inc(x_1);
x_7 = lean_apply_2(x_1, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_SubExpr_Pos_tail(x_2);
x_2 = x_10;
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_all___lambda__1), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = l_Lean_SubExpr_Pos_foldrM___at_Lean_SubExpr_Pos_all___spec__1(x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SubExpr_Pos_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_append___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_push___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_SubExpr_Pos_append___closed__1;
x_4 = l_Lean_SubExpr_Pos_foldl___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_append(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_SubExpr_Pos_push(x_4, x_6);
lean_dec(x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lean_SubExpr_Pos_root;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Lean_SubExpr_Pos_root;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Lean_SubExpr_Pos_root;
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_ofArray(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_toArray___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_push___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_toArray___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_SubExpr_Pos_toArray___closed__1;
x_3 = l_Lean_SubExpr_Pos_toArray___closed__2;
x_4 = l_Lean_SubExpr_Pos_foldl___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushBindingDomain(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushBindingBody(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushLetVarType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushLetValue(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushLetBody(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushAppFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushAppArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushProj(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_SubExpr_Pos_maxChildren;
x_4 = lean_nat_pow(x_3, x_1);
x_5 = lean_nat_mul(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_pushNaryFn(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_nat_sub(x_1, x_2);
x_5 = l_Lean_SubExpr_Pos_maxChildren;
x_6 = lean_nat_pow(x_5, x_4);
lean_dec(x_4);
x_7 = lean_nat_mul(x_3, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SubExpr_Pos_pushNaryArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_SubExpr_Pos_push(x_2, x_5);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_SubExpr_Pos_push(x_2, x_3);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_SubExpr_Pos_push(x_2, x_5);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_SubExpr_Pos_toString___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Nat_repr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Nat_repr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_SubExpr_Pos_toArray(x_1);
x_3 = lean_array_to_list(lean_box(0), x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_Lean_SubExpr_Pos_toString___spec__1(x_3, x_4);
x_6 = l_Lean_SubExpr_Pos_toString___closed__1;
x_7 = l_String_intercalate(x_6, x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("0", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("1", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("2", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("3", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid coordinate ", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5;
x_11 = lean_string_append(x_10, x_1);
x_12 = l_Lean_SubExpr_Pos_push___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6;
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7;
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8;
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9;
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("malformed ", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_SubExpr_Pos_root;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_toString___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_String_splitOn(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(x_4);
x_6 = l_Lean_SubExpr_Pos_fromString_x3f___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_SubExpr_Pos_push___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = l_Lean_SubExpr_Pos_push___closed__2;
x_14 = lean_string_dec_eq(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_15 = l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(x_4);
x_16 = l_Lean_SubExpr_Pos_fromString_x3f___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = lean_string_append(x_17, x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
lean_dec(x_4);
x_20 = l_List_redLength___rarg(x_12);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
x_22 = l_List_toArrayAux___rarg(x_12, x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(x_24, x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = l_Lean_SubExpr_Pos_ofArray(x_31);
lean_dec(x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l_Lean_SubExpr_Pos_ofArray(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l_Lean_SubExpr_Pos_fromString_x3f___closed__2;
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_fromString_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.fromString!", 28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_fromString_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_SubExpr_Pos_head___closed__1;
x_5 = l_Lean_SubExpr_Pos_fromString_x21___closed__1;
x_6 = lean_unsigned_to_nat(131u);
x_7 = lean_unsigned_to_nat(22u);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_3);
lean_dec(x_3);
x_9 = l_panic___at_Lean_SubExpr_Pos_tail___spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
return x_10;
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instOrdPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdNat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instOrdPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_instOrdPos___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_instDecidableEqPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEqPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SubExpr_Pos_instDecidableEqPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToStringPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToStringPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_instToStringPos___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instEmptyCollectionPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_root;
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instReprPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Pos.fromString! ", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instReprPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_SubExpr_Pos_instReprPos___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instReprPos___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_SubExpr_Pos_push___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_SubExpr_Pos_toString(x_1);
x_4 = l_String_quote(x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_SubExpr_Pos_instReprPos___closed__2;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_SubExpr_Pos_instReprPos___closed__3;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_instReprPos(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJsonPos___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_instToJsonPos___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SubExpr_Pos_instToJsonPos___closed__1;
x_2 = l_Lean_SubExpr_Pos_instToStringPos___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToJsonPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_instToJsonPos___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_SubExpr_Pos_fromString_x3f(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_instFromJsonPos(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedSubExpr___closed__1;
x_2 = l_Lean_SubExpr_Pos_root;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedSubExpr___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_Pos_root;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_isRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_SubExpr_Pos_maxChildren;
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedSubExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.bindingBody!", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("subexpr is not a binder", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_bindingBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(176u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_SubExpr_bindingBody_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
switch (lean_obj_tag(x_2)) {
case 6:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_SubExpr_Pos_push(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_SubExpr_Pos_push(x_9, x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
case 7:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_SubExpr_Pos_push(x_15, x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_SubExpr_Pos_push(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_SubExpr_bindingBody_x21___closed__3;
x_26 = l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_bindingDomain_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.bindingDomain!", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingDomain_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_bindingDomain_x21___closed__1;
x_3 = lean_unsigned_to_nat(181u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_SubExpr_bindingBody_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
switch (lean_obj_tag(x_2)) {
case 6:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_SubExpr_Pos_push(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_SubExpr_Pos_push(x_9, x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
case 7:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_SubExpr_Pos_push(x_15, x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_SubExpr_Pos_push(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_SubExpr_bindingDomain_x21___closed__2;
x_26 = l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_SubExpr_Pos_push(x_1, x_5);
x_7 = lean_apply_2(x_2, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_SubExpr_Pos_push(x_3, x_12);
lean_inc(x_2);
x_14 = l_Lean_Expr_traverseAppWithPos___rarg(x_1, x_2, x_13, x_5);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Expr_traverseAppWithPos___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_6);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_apply_2(x_2, x_3, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseAppWithPos___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_traverseAppWithPos___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_SubExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_SubExpr_Pos_maxChildren = _init_l_Lean_SubExpr_Pos_maxChildren();
lean_mark_persistent(l_Lean_SubExpr_Pos_maxChildren);
l_Lean_SubExpr_Pos_typeCoord___closed__1 = _init_l_Lean_SubExpr_Pos_typeCoord___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_typeCoord___closed__1);
l_Lean_SubExpr_Pos_typeCoord = _init_l_Lean_SubExpr_Pos_typeCoord();
lean_mark_persistent(l_Lean_SubExpr_Pos_typeCoord);
l_Lean_SubExpr_Pos_root = _init_l_Lean_SubExpr_Pos_root();
lean_mark_persistent(l_Lean_SubExpr_Pos_root);
l_Lean_SubExpr_Pos_instInhabitedPos = _init_l_Lean_SubExpr_Pos_instInhabitedPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instInhabitedPos);
l_Lean_SubExpr_Pos_head___closed__1 = _init_l_Lean_SubExpr_Pos_head___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__1);
l_Lean_SubExpr_Pos_head___closed__2 = _init_l_Lean_SubExpr_Pos_head___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__2);
l_Lean_SubExpr_Pos_head___closed__3 = _init_l_Lean_SubExpr_Pos_head___closed__3();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__3);
l_Lean_SubExpr_Pos_head___closed__4 = _init_l_Lean_SubExpr_Pos_head___closed__4();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__4);
l_Lean_SubExpr_Pos_tail___closed__1 = _init_l_Lean_SubExpr_Pos_tail___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_tail___closed__1);
l_Lean_SubExpr_Pos_tail___closed__2 = _init_l_Lean_SubExpr_Pos_tail___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_tail___closed__2);
l_Lean_SubExpr_Pos_push___closed__1 = _init_l_Lean_SubExpr_Pos_push___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_push___closed__1);
l_Lean_SubExpr_Pos_push___closed__2 = _init_l_Lean_SubExpr_Pos_push___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_push___closed__2);
l_Lean_SubExpr_Pos_push___closed__3 = _init_l_Lean_SubExpr_Pos_push___closed__3();
lean_mark_persistent(l_Lean_SubExpr_Pos_push___closed__3);
l_Lean_SubExpr_Pos_depth___closed__1 = _init_l_Lean_SubExpr_Pos_depth___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_depth___closed__1);
l_Lean_SubExpr_Pos_append___closed__1 = _init_l_Lean_SubExpr_Pos_append___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_append___closed__1);
l_Lean_SubExpr_Pos_toArray___closed__1 = _init_l_Lean_SubExpr_Pos_toArray___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_toArray___closed__1);
l_Lean_SubExpr_Pos_toArray___closed__2 = _init_l_Lean_SubExpr_Pos_toArray___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_toArray___closed__2);
l_Lean_SubExpr_Pos_toString___closed__1 = _init_l_Lean_SubExpr_Pos_toString___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_toString___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9);
l_Lean_SubExpr_Pos_fromString_x3f___closed__1 = _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_fromString_x3f___closed__1);
l_Lean_SubExpr_Pos_fromString_x3f___closed__2 = _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_fromString_x3f___closed__2);
l_Lean_SubExpr_Pos_fromString_x21___closed__1 = _init_l_Lean_SubExpr_Pos_fromString_x21___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_fromString_x21___closed__1);
l_Lean_SubExpr_Pos_instOrdPos___closed__1 = _init_l_Lean_SubExpr_Pos_instOrdPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instOrdPos___closed__1);
l_Lean_SubExpr_Pos_instOrdPos = _init_l_Lean_SubExpr_Pos_instOrdPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instOrdPos);
l_Lean_SubExpr_Pos_instToStringPos___closed__1 = _init_l_Lean_SubExpr_Pos_instToStringPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToStringPos___closed__1);
l_Lean_SubExpr_Pos_instToStringPos = _init_l_Lean_SubExpr_Pos_instToStringPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToStringPos);
l_Lean_SubExpr_Pos_instEmptyCollectionPos = _init_l_Lean_SubExpr_Pos_instEmptyCollectionPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instEmptyCollectionPos);
l_Lean_SubExpr_Pos_instReprPos___closed__1 = _init_l_Lean_SubExpr_Pos_instReprPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instReprPos___closed__1);
l_Lean_SubExpr_Pos_instReprPos___closed__2 = _init_l_Lean_SubExpr_Pos_instReprPos___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_instReprPos___closed__2);
l_Lean_SubExpr_Pos_instReprPos___closed__3 = _init_l_Lean_SubExpr_Pos_instReprPos___closed__3();
lean_mark_persistent(l_Lean_SubExpr_Pos_instReprPos___closed__3);
l_Lean_SubExpr_Pos_instToJsonPos___closed__1 = _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToJsonPos___closed__1);
l_Lean_SubExpr_Pos_instToJsonPos___closed__2 = _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToJsonPos___closed__2);
l_Lean_SubExpr_Pos_instToJsonPos = _init_l_Lean_SubExpr_Pos_instToJsonPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToJsonPos);
l_Lean_instInhabitedSubExpr___closed__1 = _init_l_Lean_instInhabitedSubExpr___closed__1();
lean_mark_persistent(l_Lean_instInhabitedSubExpr___closed__1);
l_Lean_instInhabitedSubExpr___closed__2 = _init_l_Lean_instInhabitedSubExpr___closed__2();
lean_mark_persistent(l_Lean_instInhabitedSubExpr___closed__2);
l_Lean_instInhabitedSubExpr = _init_l_Lean_instInhabitedSubExpr();
lean_mark_persistent(l_Lean_instInhabitedSubExpr);
l_Lean_SubExpr_bindingBody_x21___closed__1 = _init_l_Lean_SubExpr_bindingBody_x21___closed__1();
lean_mark_persistent(l_Lean_SubExpr_bindingBody_x21___closed__1);
l_Lean_SubExpr_bindingBody_x21___closed__2 = _init_l_Lean_SubExpr_bindingBody_x21___closed__2();
lean_mark_persistent(l_Lean_SubExpr_bindingBody_x21___closed__2);
l_Lean_SubExpr_bindingBody_x21___closed__3 = _init_l_Lean_SubExpr_bindingBody_x21___closed__3();
lean_mark_persistent(l_Lean_SubExpr_bindingBody_x21___closed__3);
l_Lean_SubExpr_bindingDomain_x21___closed__1 = _init_l_Lean_SubExpr_bindingDomain_x21___closed__1();
lean_mark_persistent(l_Lean_SubExpr_bindingDomain_x21___closed__1);
l_Lean_SubExpr_bindingDomain_x21___closed__2 = _init_l_Lean_SubExpr_bindingDomain_x21___closed__2();
lean_mark_persistent(l_Lean_SubExpr_bindingDomain_x21___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
