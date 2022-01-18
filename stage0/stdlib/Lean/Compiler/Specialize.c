// Lean compiler output
// Module: Lean.Compiler.Specialize
// Imports: Init Lean.Attributes Lean.Compiler.Util
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
LEAN_EXPORT lean_object* lean_get_specialization_info(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_specializeAttrs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_specializeAttrs___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__12;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecState_specInfo___default;
static lean_object* l_Lean_Compiler_specializeAttrs___closed__8;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__1;
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(lean_object*, uint8_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__2;
static lean_object* l_Lean_Compiler_specExtension___closed__1;
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_specializeAttrs___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_specInfo___default___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Compiler_specializeAttrs___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__4___boxed(lean_object*);
static lean_object* l_Lean_Compiler_specExtension___closed__4;
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_14____boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__2___boxed(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_specExtension___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_toCtorIdx(uint8_t);
static uint32_t l_Lean_Compiler_specializeAttrs___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__3___boxed(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__9;
static lean_object* l_Lean_Compiler_specializeAttrs___lambda__3___closed__1;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__8;
LEAN_EXPORT uint8_t l_Lean_Compiler_instInhabitedSpecializeAttributeKind;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_SpecState_specInfo___default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_instInhabitedSpecEntry;
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx___boxed(lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__3;
LEAN_EXPORT uint8_t lean_has_specialize_attribute(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_specializeAttrs___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__4(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Compiler_instInhabitedSpecState___closed__4;
static lean_object* l_Lean_Compiler_SpecState_cache___default___closed__1;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__2;
LEAN_EXPORT lean_object* lean_add_specialization_info(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__6;
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__1;
static lean_object* l_Lean_Compiler_instInhabitedSpecEntry___closed__1;
static lean_object* l_Lean_Compiler_instInhabitedSpecState___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__14;
static lean_object* l_Lean_Compiler_instInhabitedSpecState___closed__2;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_instInhabitedSpecInfo___closed__1;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_cache_specialization(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_instInhabitedSpecArgKind;
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__4;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_14_(uint8_t, uint8_t);
static lean_object* l_Lean_Compiler_specializeAttrs___closed__4;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31_(lean_object*);
lean_object* lean_list_to_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_instInhabitedSpecState___closed__3;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__10;
LEAN_EXPORT uint8_t lean_has_nospecialize_attribute(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_instInhabitedSpecInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_cache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____lambda__1(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__13;
static lean_object* l_Lean_Compiler_specializeAttrs___closed__6;
lean_object* l_Lean_Name_getPrefix(lean_object*);
static lean_object* l_Lean_Compiler_specializeAttrs___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__7;
LEAN_EXPORT lean_object* lean_get_cached_specialization(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_specInfo___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(uint8_t);
lean_object* l_Lean_EnumAttributes_getValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Compiler_SpecState_specInfo___default___closed__2;
static lean_object* l_Lean_Compiler_SpecState_specInfo___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecState_switch(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecState_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_specExtension___closed__3;
static lean_object* l_Lean_Compiler_specExtension___closed__5;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_cache___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__5;
static lean_object* l_Lean_Compiler_specializeAttrs___lambda__1___closed__3;
static lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__4___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lean_registerEnumAttributes___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_instInhabitedSpecState;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecState_cache___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_14_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(x_1);
x_4 = l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_14____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_14_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_14____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_instBEqSpecializeAttributeKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("specializeAttrs");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("specialize");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mark definition to always be specialized");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__5;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__4;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nospecialize");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mark definition to never be specialized");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__11() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__10;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__9;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__7;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____lambda__1___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31_(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Compiler_instInhabitedSpecializeAttributeKind;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__2;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__14;
x_5 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__15;
x_6 = 2;
x_7 = lean_box(x_2);
x_8 = l_Lean_registerEnumAttributes___rarg(x_7, x_3, x_4, x_5, x_6, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____lambda__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
static uint32_t _init_l_Lean_Compiler_specializeAttrs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___lambda__1___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_specializeAttrs___lambda__1___closed__1;
x_3 = l_Lean_Compiler_specializeAttrs___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_specializeAttrs___lambda__1___closed__3;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specializeAttrs___lambda__3___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_specializeAttrs___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specializeAttrs___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specializeAttrs___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specializeAttrs___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specializeAttrs___lambda__4___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Compiler_specializeAttrs___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_specializeAttrs___closed__3;
x_4 = l_Lean_Compiler_specializeAttrs___closed__4;
x_5 = l_Lean_Compiler_specializeAttrs___closed__5;
x_6 = l_Lean_Compiler_specializeAttrs___closed__6;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_specializeAttrs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_specializeAttrs___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_specializeAttrs___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_specializeAttrs___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specializeAttrs___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttrs___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specializeAttrs___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Compiler_instInhabitedSpecializeAttributeKind;
x_5 = l_Lean_Compiler_specializeAttrs;
x_6 = lean_box(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_EnumAttributes_getValue___rarg(x_6, x_5, x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Name_isInternal(x_3);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Name_getPrefix(x_3);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_14_(x_2, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lean_has_specialize_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_specialize_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_has_nospecialize_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 1;
x_4 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_nospecialize_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_SpecArgKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_SpecArgKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecArgKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_SpecArgKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecArgKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecInfo___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_instInhabitedSpecInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_specInfo___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_SpecState_specInfo___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_SpecState_specInfo___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_SpecState_specInfo___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_SpecState_specInfo___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_SpecState_specInfo___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_SpecState_specInfo___default() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
x_3 = 1;
x_4 = l_Lean_Compiler_SpecState_specInfo___default___closed__3;
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_specInfo___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_SpecState_specInfo___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_cache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_SpecState_cache___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_SpecState_specInfo___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_SpecState_cache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
x_3 = 1;
x_4 = l_Lean_Compiler_SpecState_cache___default___closed__1;
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_cache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_SpecState_cache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecState___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Compiler_instInhabitedSpecState___closed__1;
x_3 = l_Lean_Compiler_SpecState_specInfo___default___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecState___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Compiler_instInhabitedSpecState___closed__1;
x_3 = l_Lean_Compiler_SpecState_cache___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_instInhabitedSpecState___closed__2;
x_2 = l_Lean_Compiler_instInhabitedSpecState___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_instInhabitedSpecState___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_instInhabitedSpecInfo___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedSpecEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_instInhabitedSpecEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_instBEqName;
x_8 = l_Lean_instHashableName;
x_9 = l_Std_PersistentHashMap_insert___rarg(x_7, x_8, x_6, x_2, x_3);
x_10 = 0;
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_10);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Lean_Name_instBEqName;
x_14 = l_Lean_instHashableName;
x_15 = l_Std_PersistentHashMap_insert___rarg(x_13, x_14, x_12, x_2, x_3);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_Name_instBEqName;
x_21 = l_Lean_instHashableName;
x_22 = l_Std_HashMap_insert___rarg(x_20, x_21, x_19, x_2, x_3);
x_23 = 1;
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_23);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = l_Lean_Name_instBEqName;
x_27 = l_Lean_instHashableName;
x_28 = l_Std_HashMap_insert___rarg(x_26, x_27, x_24, x_2, x_3);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_instBEqExpr;
x_8 = l_Lean_Expr_instHashableExpr;
x_9 = l_Std_PersistentHashMap_insert___rarg(x_7, x_8, x_6, x_2, x_3);
x_10 = 0;
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_10);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Lean_Expr_instBEqExpr;
x_14 = l_Lean_Expr_instHashableExpr;
x_15 = l_Std_PersistentHashMap_insert___rarg(x_13, x_14, x_12, x_2, x_3);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_Expr_instBEqExpr;
x_21 = l_Lean_Expr_instHashableExpr;
x_22 = l_Std_HashMap_insert___rarg(x_20, x_21, x_19, x_2, x_3);
x_23 = 1;
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_23);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = l_Lean_Expr_instBEqExpr;
x_27 = l_Lean_Expr_instHashableExpr;
x_28 = l_Std_HashMap_insert___rarg(x_26, x_27, x_24, x_2, x_3);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecState_addEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(x_6, x_3, x_4);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(x_8, x_3, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(x_15, x_12, x_13);
lean_ctor_set(x_1, 1, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(x_18, x_12, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecState_switch(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(x_3);
x_6 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
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
x_9 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(x_7);
x_10 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_SpecState_addEntry(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__2(x_6, x_15, x_16, x_4);
lean_dec(x_6);
x_2 = x_11;
x_4 = x_17;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__3(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_instInhabitedSpecState___closed__4;
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__1(x_2, x_1);
x_4 = l_Lean_Compiler_SpecState_switch(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_list_to_array), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_SpecState_addEntry), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__4;
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__2;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__3;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__4;
x_3 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specializeAttrs___lambda__3___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_specializeAttrs___lambda__1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_specExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specExtension___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_specExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Compiler_specializeAttrs___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_specExtension___closed__1;
x_4 = l_Lean_Compiler_specExtension___closed__2;
x_5 = l_Lean_Compiler_specExtension___closed__3;
x_6 = l_Lean_Compiler_specExtension___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specExtension___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specExtension___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_specExtension___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specExtension___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_specExtension___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_add_specialization_info(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Compiler_specExtension;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__3(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Name_instBEqName;
x_7 = l_Lean_instHashableName;
lean_inc(x_2);
x_8 = l_Std_PersistentHashMap_find_x3f___rarg(x_6, x_7, x_5, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(x_4, x_2);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(x_13, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lean_get_specialization_info(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_instInhabitedSpecState;
x_4 = l_Lean_Compiler_specExtension;
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_4, x_1);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_cache_specialization(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Compiler_specExtension;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__3(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Expr_instBEqExpr;
x_7 = l_Lean_Expr_instHashableExpr;
lean_inc(x_2);
x_8 = l_Std_PersistentHashMap_find_x3f___rarg(x_6, x_7, x_5, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(x_4, x_2);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(x_13, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lean_get_cached_specialization(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_instInhabitedSpecState;
x_4 = l_Lean_Compiler_specExtension;
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_4, x_1);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_Compiler_Util(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Specialize(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___closed__1 = _init_l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_SpecializeAttributeKind_noConfusion___rarg___closed__1);
l_Lean_Compiler_instInhabitedSpecializeAttributeKind = _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind();
l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1 = _init_l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1();
lean_mark_persistent(l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1);
l_Lean_Compiler_instBEqSpecializeAttributeKind = _init_l_Lean_Compiler_instBEqSpecializeAttributeKind();
lean_mark_persistent(l_Lean_Compiler_instBEqSpecializeAttributeKind);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__4);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__5 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__5();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__5);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__6 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__6();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__6);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__7 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__7();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__7);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__8 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__8();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__8);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__9 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__9();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__9);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__10 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__10();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__10);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__11 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__11();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__11);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__12 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__12();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__12);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__13 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__13();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__13);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__14 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__14();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__14);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__15 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__15();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31____closed__15);
l_Lean_Compiler_specializeAttrs___lambda__1___closed__1 = _init_l_Lean_Compiler_specializeAttrs___lambda__1___closed__1();
l_Lean_Compiler_specializeAttrs___lambda__1___closed__2 = _init_l_Lean_Compiler_specializeAttrs___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___lambda__1___closed__2);
l_Lean_Compiler_specializeAttrs___lambda__1___closed__3 = _init_l_Lean_Compiler_specializeAttrs___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___lambda__1___closed__3);
l_Lean_Compiler_specializeAttrs___lambda__3___closed__1 = _init_l_Lean_Compiler_specializeAttrs___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___lambda__3___closed__1);
l_Lean_Compiler_specializeAttrs___closed__1 = _init_l_Lean_Compiler_specializeAttrs___closed__1();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__1);
l_Lean_Compiler_specializeAttrs___closed__2 = _init_l_Lean_Compiler_specializeAttrs___closed__2();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__2);
l_Lean_Compiler_specializeAttrs___closed__3 = _init_l_Lean_Compiler_specializeAttrs___closed__3();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__3);
l_Lean_Compiler_specializeAttrs___closed__4 = _init_l_Lean_Compiler_specializeAttrs___closed__4();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__4);
l_Lean_Compiler_specializeAttrs___closed__5 = _init_l_Lean_Compiler_specializeAttrs___closed__5();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__5);
l_Lean_Compiler_specializeAttrs___closed__6 = _init_l_Lean_Compiler_specializeAttrs___closed__6();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__6);
l_Lean_Compiler_specializeAttrs___closed__7 = _init_l_Lean_Compiler_specializeAttrs___closed__7();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__7);
l_Lean_Compiler_specializeAttrs___closed__8 = _init_l_Lean_Compiler_specializeAttrs___closed__8();
lean_mark_persistent(l_Lean_Compiler_specializeAttrs___closed__8);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_31_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_specializeAttrs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_specializeAttrs);
lean_dec_ref(res);
l_Lean_Compiler_instInhabitedSpecArgKind = _init_l_Lean_Compiler_instInhabitedSpecArgKind();
l_Lean_Compiler_instInhabitedSpecInfo___closed__1 = _init_l_Lean_Compiler_instInhabitedSpecInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecInfo___closed__1);
l_Lean_Compiler_instInhabitedSpecInfo = _init_l_Lean_Compiler_instInhabitedSpecInfo();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecInfo);
l_Lean_Compiler_SpecState_specInfo___default___closed__1 = _init_l_Lean_Compiler_SpecState_specInfo___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_SpecState_specInfo___default___closed__1);
l_Lean_Compiler_SpecState_specInfo___default___closed__2 = _init_l_Lean_Compiler_SpecState_specInfo___default___closed__2();
lean_mark_persistent(l_Lean_Compiler_SpecState_specInfo___default___closed__2);
l_Lean_Compiler_SpecState_specInfo___default___closed__3 = _init_l_Lean_Compiler_SpecState_specInfo___default___closed__3();
lean_mark_persistent(l_Lean_Compiler_SpecState_specInfo___default___closed__3);
l_Lean_Compiler_SpecState_specInfo___default = _init_l_Lean_Compiler_SpecState_specInfo___default();
lean_mark_persistent(l_Lean_Compiler_SpecState_specInfo___default);
l_Lean_Compiler_SpecState_cache___default___closed__1 = _init_l_Lean_Compiler_SpecState_cache___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_SpecState_cache___default___closed__1);
l_Lean_Compiler_SpecState_cache___default = _init_l_Lean_Compiler_SpecState_cache___default();
lean_mark_persistent(l_Lean_Compiler_SpecState_cache___default);
l_Lean_Compiler_instInhabitedSpecState___closed__1 = _init_l_Lean_Compiler_instInhabitedSpecState___closed__1();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState___closed__1);
l_Lean_Compiler_instInhabitedSpecState___closed__2 = _init_l_Lean_Compiler_instInhabitedSpecState___closed__2();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState___closed__2);
l_Lean_Compiler_instInhabitedSpecState___closed__3 = _init_l_Lean_Compiler_instInhabitedSpecState___closed__3();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState___closed__3);
l_Lean_Compiler_instInhabitedSpecState___closed__4 = _init_l_Lean_Compiler_instInhabitedSpecState___closed__4();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState___closed__4);
l_Lean_Compiler_instInhabitedSpecState = _init_l_Lean_Compiler_instInhabitedSpecState();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState);
l_Lean_Compiler_instInhabitedSpecEntry___closed__1 = _init_l_Lean_Compiler_instInhabitedSpecEntry___closed__1();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecEntry___closed__1);
l_Lean_Compiler_instInhabitedSpecEntry = _init_l_Lean_Compiler_instInhabitedSpecEntry();
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecEntry);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333____closed__4);
l_Lean_Compiler_specExtension___closed__1 = _init_l_Lean_Compiler_specExtension___closed__1();
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__1);
l_Lean_Compiler_specExtension___closed__2 = _init_l_Lean_Compiler_specExtension___closed__2();
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__2);
l_Lean_Compiler_specExtension___closed__3 = _init_l_Lean_Compiler_specExtension___closed__3();
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__3);
l_Lean_Compiler_specExtension___closed__4 = _init_l_Lean_Compiler_specExtension___closed__4();
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__4);
l_Lean_Compiler_specExtension___closed__5 = _init_l_Lean_Compiler_specExtension___closed__5();
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__5);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_333_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_specExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_specExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
