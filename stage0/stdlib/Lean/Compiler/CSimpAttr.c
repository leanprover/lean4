// Lean compiler output
// Module: Lean.Compiler.CSimpAttr
// Imports: Init Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Util.ReplaceExpr
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
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____lambda__1(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__2;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Compiler_CSimp_State_switch___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_replaceConstants___lambda__1(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Compiler_CSimp_State_thmNames___default___closed__2;
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4;
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_CSimp_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_instInhabitedEntry;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_thmNames___default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_State_map___default___closed__3;
uint8_t l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__4;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__8(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_map___default;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_add___closed__3;
static lean_object* l_Lean_Compiler_CSimp_instInhabitedState___closed__1;
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_ext;
LEAN_EXPORT lean_object* l_Lean_Compiler_hasCSimpAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_add___closed__1;
static lean_object* l_Lean_Compiler_CSimp_State_map___default___closed__2;
static lean_object* l_Lean_Compiler_CSimp_add___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Compiler_CSimp_State_map___default___closed__1;
uint8_t l_Lean_SMap_contains___at_Lean_NameSSet_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_csimp_replace_constants(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__7(lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_4774____spec__4(lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_switch(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__5;
static lean_object* l_Lean_Compiler_CSimp_instInhabitedEntry___closed__1;
static lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__3;
LEAN_EXPORT uint8_t l_Lean_Compiler_hasCSimpAttribute(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_State_thmNames___default___closed__1;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__2;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_CSimp_add___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443_(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__5;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1___boxed(lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__3;
static lean_object* _init_l_Lean_Compiler_CSimp_instInhabitedEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_instInhabitedEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_CSimp_instInhabitedEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_map___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_map___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_CSimp_State_map___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_map___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_State_map___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_map___default() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
x_3 = 1;
x_4 = l_Lean_Compiler_CSimp_State_map___default___closed__3;
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_thmNames___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_thmNames___default___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Compiler_CSimp_State_thmNames___default___closed__1;
x_3 = l_Lean_Compiler_CSimp_State_map___default___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_thmNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_CSimp_State_thmNames___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_CSimp_State_thmNames___default___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_CSimp_instInhabitedState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Compiler_CSimp_State_switch___spec__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_switch(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_SMap_switch___at_Lean_Compiler_CSimp_State_switch___spec__1(x_3);
x_6 = l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_4774____spec__4(x_4);
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
x_9 = l_Lean_SMap_switch___at_Lean_Compiler_CSimp_State_switch___spec__1(x_7);
x_10 = l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_4774____spec__4(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__5(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__4(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__5(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__4(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Name_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__10(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__8(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__9(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__11(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__11(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__7(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__8(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__11(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__7(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__8(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__11(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__2(x_6, x_2, x_3);
x_8 = 0;
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__2(x_10, x_2, x_3);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Std_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__6(x_15, x_2, x_3);
x_17 = 1;
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = l_Std_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__6(x_18, x_2, x_3);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__1(x_4, x_6, x_7);
x_10 = lean_box(0);
x_11 = l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(x_5, x_8, x_10);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
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
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__1(x_12, x_14, x_15);
x_18 = lean_box(0);
x_19 = l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(x_13, x_16, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("csimp", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_State_switch), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__2;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__3;
x_3 = l_Lean_Compiler_CSimp_instInhabitedState___closed__1;
x_4 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__5;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = lean_environment_find(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_5);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2(x_17, x_2, x_3, x_8);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = lean_environment_find(x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_box(0);
x_25 = l_Lean_mkConst(x_1, x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2(x_30, x_2, x_3, x_21);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
return x_33;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_9 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2;
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity(x_8, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_appFn_x21(x_8);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
}
else
{
lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_5, 0, x_24);
return x_5;
}
}
else
{
lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_5, 0, x_25);
return x_5;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = l_Lean_ConstantInfo_type(x_26);
lean_dec(x_26);
x_29 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2;
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Expr_isAppOfArity(x_28, x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Expr_appFn_x21(x_28);
x_35 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
if (lean_obj_tag(x_38) == 4)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(x_37, x_40);
lean_dec(x_40);
lean_dec(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_1);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_27);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_27);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_27);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_5);
if (x_51 == 0)
{
return x_5;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_5, 0);
x_53 = lean_ctor_get(x_5, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_5);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_CSimp_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_CSimp_State_map___default___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_3) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_11, x_2);
x_14 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1;
lean_ctor_set(x_8, 4, x_14);
lean_ctor_set(x_8, 0, x_13);
x_15 = lean_st_ref_set(x_5, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
x_24 = lean_ctor_get(x_8, 2);
x_25 = lean_ctor_get(x_8, 3);
x_26 = lean_ctor_get(x_8, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_27 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_22, x_2);
x_28 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1;
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_26);
x_30 = lean_st_ref_set(x_5, x_29, x_9);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_4);
x_35 = lean_st_ref_take(x_5, x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 4);
lean_dec(x_40);
x_41 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_39, x_2);
x_42 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1;
lean_ctor_set(x_36, 4, x_42);
lean_ctor_set(x_36, 0, x_41);
x_43 = lean_st_ref_set(x_5, x_36, x_37);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 2);
x_53 = lean_ctor_get(x_36, 3);
x_54 = lean_ctor_get(x_36, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_55 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_50, x_2);
x_56 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1;
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set(x_57, 4, x_56);
lean_ctor_set(x_57, 5, x_54);
x_58 = lean_st_ref_set(x_5, x_57, x_37);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
default: 
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_4, 6);
lean_inc(x_63);
lean_dec(x_4);
x_64 = lean_st_ref_take(x_5, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 4);
lean_dec(x_69);
x_70 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_68, x_63, x_2);
x_71 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1;
lean_ctor_set(x_65, 4, x_71);
lean_ctor_set(x_65, 0, x_70);
x_72 = lean_st_ref_set(x_5, x_65, x_66);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
x_81 = lean_ctor_get(x_65, 2);
x_82 = lean_ctor_get(x_65, 3);
x_83 = lean_ctor_get(x_65, 5);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
x_84 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_79, x_63, x_2);
x_85 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1;
x_86 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set(x_86, 4, x_85);
lean_ctor_set(x_86, 5, x_83);
x_87 = lean_st_ref_set(x_5, x_86, x_66);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_add___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'csimp' theorem, only constant replacement theorems (e.g., `@f = @g`) are currently supported.", 102);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_add___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_CSimp_add___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_add___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_CSimp_ext;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Compiler_CSimp_add___closed__2;
x_10 = l_Lean_throwError___at_Lean_Compiler_CSimp_add___spec__1(x_9, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_Compiler_CSimp_add___closed__3;
x_14 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2(x_13, x_12, x_2, x_3, x_4, x_11);
lean_dec(x_4);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_CSimp_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Compiler_CSimp_add___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Compiler_CSimp_add(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_CSimp_add(x_1, x_3, x_4, x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attribute cannot be erased", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simplification theorem for the compiler", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__2;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__2;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__3;
x_3 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__5;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(x_4, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
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
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(x_11, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_replaceConstants___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConst(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Expr_constName_x21(x_2);
x_7 = l_Lean_SMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__1(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_Expr_constLevels_x21(x_2);
x_12 = l_Lean_mkConst(x_10, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Lean_Expr_constLevels_x21(x_2);
x_15 = l_Lean_mkConst(x_13, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_csimp_replace_constants(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_CSimp_instInhabitedState;
x_4 = l_Lean_Compiler_CSimp_add___closed__3;
x_5 = l_Lean_ScopedEnvExtension_getState___rarg(x_3, x_4, x_1);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_replaceConstants___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafe(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasCSimpAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_Compiler_CSimp_instInhabitedState;
x_4 = l_Lean_Compiler_CSimp_add___closed__3;
x_5 = l_Lean_ScopedEnvExtension_getState___rarg(x_3, x_4, x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_SMap_contains___at_Lean_NameSSet_contains___spec__1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasCSimpAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_hasCSimpAttribute(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_CSimp_instInhabitedEntry___closed__1 = _init_l_Lean_Compiler_CSimp_instInhabitedEntry___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedEntry___closed__1);
l_Lean_Compiler_CSimp_instInhabitedEntry = _init_l_Lean_Compiler_CSimp_instInhabitedEntry();
lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedEntry);
l_Lean_Compiler_CSimp_State_map___default___closed__1 = _init_l_Lean_Compiler_CSimp_State_map___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_State_map___default___closed__1);
l_Lean_Compiler_CSimp_State_map___default___closed__2 = _init_l_Lean_Compiler_CSimp_State_map___default___closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_State_map___default___closed__2);
l_Lean_Compiler_CSimp_State_map___default___closed__3 = _init_l_Lean_Compiler_CSimp_State_map___default___closed__3();
lean_mark_persistent(l_Lean_Compiler_CSimp_State_map___default___closed__3);
l_Lean_Compiler_CSimp_State_map___default = _init_l_Lean_Compiler_CSimp_State_map___default();
lean_mark_persistent(l_Lean_Compiler_CSimp_State_map___default);
l_Lean_Compiler_CSimp_State_thmNames___default___closed__1 = _init_l_Lean_Compiler_CSimp_State_thmNames___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_State_thmNames___default___closed__1);
l_Lean_Compiler_CSimp_State_thmNames___default___closed__2 = _init_l_Lean_Compiler_CSimp_State_thmNames___default___closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_State_thmNames___default___closed__2);
l_Lean_Compiler_CSimp_State_thmNames___default = _init_l_Lean_Compiler_CSimp_State_thmNames___default();
lean_mark_persistent(l_Lean_Compiler_CSimp_State_thmNames___default);
l_Lean_Compiler_CSimp_instInhabitedState___closed__1 = _init_l_Lean_Compiler_CSimp_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedState___closed__1);
l_Lean_Compiler_CSimp_instInhabitedState = _init_l_Lean_Compiler_CSimp_instInhabitedState();
lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedState);
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__1();
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__3 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____spec__3___closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__1 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__1);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__2 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__2);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__3 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__3();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__4 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__4();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__4);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__5 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__5();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122____closed__5);
if (builtin) {res = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_122_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_CSimp_ext = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_CSimp_ext);
lean_dec_ref(res);
}l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__1 = _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__1);
l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2 = _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2);
l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__3 = _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__3);
l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4 = _init_l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4);
l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1 = _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1);
l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2 = _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2);
l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__2___closed__1);
l_Lean_Compiler_CSimp_add___closed__1 = _init_l_Lean_Compiler_CSimp_add___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_add___closed__1);
l_Lean_Compiler_CSimp_add___closed__2 = _init_l_Lean_Compiler_CSimp_add___closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_add___closed__2);
l_Lean_Compiler_CSimp_add___closed__3 = _init_l_Lean_Compiler_CSimp_add___closed__3();
lean_mark_persistent(l_Lean_Compiler_CSimp_add___closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__1 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__1);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__2 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____lambda__2___closed__2);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__1 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__1);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__2 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__2);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__3 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__3();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__4 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__4();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__4);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__5 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__5();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443____closed__5);
res = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_443_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
