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
size_t l___private_Lean_Data_HashMap_0__Lean_HashMapImp_mkIdx(lean_object*, uint64_t, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__20;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__8(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__7;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__3;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Compiler_CSimp_State_switch___spec__1(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__12;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__4;
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__7___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(lean_object*, size_t, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Compiler_CSimp_State_thmNames___default___closed__2;
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_Cache_new;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__7(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__4;
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__19;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__9;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_instInhabitedEntry;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_thmNames___default;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_State_map___default___closed__3;
uint8_t l_List_beq___at_Lean_Core_instantiateTypeLevelParams___spec__8(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__11;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__11(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__17;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_map___default;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_add___closed__3;
static lean_object* l_Lean_Compiler_CSimp_instInhabitedState___closed__1;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__3;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__21;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_ext;
LEAN_EXPORT lean_object* l_Lean_Compiler_hasCSimpAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_addDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_add___closed__1;
static lean_object* l_Lean_Compiler_CSimp_State_map___default___closed__2;
static lean_object* l_Lean_Compiler_CSimp_add___closed__2;
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__13;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_State_map___default___closed__1;
uint8_t l_Lean_SMap_contains___at_Lean_NameSSet_contains___spec__1(lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_csimp_replace_constants(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___closed__2;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_add(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_State_switch(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__7;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Compiler_CSimp_instInhabitedEntry___closed__1;
static lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_Compiler_hasCSimpAttribute(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__5;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_State_thmNames___default___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__10(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__18;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__15;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__5;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174_(lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__16;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__6;
lean_object* l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__14;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__2;
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_6878____spec__4(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__8;
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_map___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
x_3 = 1;
x_4 = l_Lean_Compiler_CSimp_State_map___default___closed__3;
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_CSimp_State_map___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_State_thmNames___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
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
x_6 = l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_6878____spec__4(x_4);
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
x_10 = l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_Environment___hyg_6878____spec__4(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Name_hash___override(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__2;
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
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__2;
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
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__5(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__4(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__5(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__4(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(x_5, x_8, x_9, x_2, x_3);
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
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(x_13, x_16, x_17, x_2, x_3);
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
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = (size_t)(x_7) & (lean_unbox(x_6) - 1);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash___override(x_12);
x_17 = (size_t)(x_16) & (lean_unbox(x_15) - 1);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__10(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__8(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__9(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__11(x_1, x_2, x_8);
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
x_15 = l_Lean_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__11(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
lean_inc(x_7);
x_9 = (size_t)(x_8) & (lean_unbox(x_7) - 1);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__7(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__8(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__11(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Name_hash___override(x_2);
lean_inc(x_23);
x_25 = (size_t)(x_24) & (lean_unbox(x_23) - 1);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__7(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__8(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__11(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__2(x_6, x_2, x_3);
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
x_11 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__2(x_10, x_2, x_3);
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
x_16 = l_Lean_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__6(x_15, x_2, x_3);
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
x_20 = l_Lean_HashMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__6(x_18, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__1(x_4, x_6, x_7);
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
x_17 = l_Lean_SMap_insert___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__1(x_12, x_14, x_15);
x_18 = lean_box(0);
x_19 = l_Lean_SMap_insert___at_Lean_NameSSet_insert___spec__1(x_13, x_16, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CSimp", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ext", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2;
x_3 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__3;
x_4 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_State_switch), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__5;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__6;
x_3 = l_Lean_Compiler_CSimp_instInhabitedState___closed__1;
x_4 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__8;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__7(x_1, x_2);
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
x_12 = l_Lean_Expr_const___override(x_1, x_11);
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
x_25 = l_Lean_Expr_const___override(x_1, x_24);
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
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
x_24 = lean_ctor_get(x_8, 2);
x_25 = lean_ctor_get(x_8, 3);
x_26 = lean_ctor_get(x_8, 5);
x_27 = lean_ctor_get(x_8, 6);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_28 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_22, x_2);
x_29 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1;
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_27);
x_31 = lean_st_ref_set(x_5, x_30, x_9);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_4);
x_36 = lean_st_ref_take(x_5, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 4);
lean_dec(x_41);
x_42 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_40, x_2);
x_43 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1;
lean_ctor_set(x_37, 4, x_43);
lean_ctor_set(x_37, 0, x_42);
x_44 = lean_st_ref_set(x_5, x_37, x_38);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
x_53 = lean_ctor_get(x_37, 2);
x_54 = lean_ctor_get(x_37, 3);
x_55 = lean_ctor_get(x_37, 5);
x_56 = lean_ctor_get(x_37, 6);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_57 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_51, x_2);
x_58 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1;
x_59 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_55);
lean_ctor_set(x_59, 6, x_56);
x_60 = lean_st_ref_set(x_5, x_59, x_38);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
default: 
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_4, 6);
lean_inc(x_65);
lean_dec(x_4);
x_66 = lean_st_ref_take(x_5, x_6);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = lean_ctor_get(x_67, 4);
lean_dec(x_71);
x_72 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_70, x_65, x_2);
x_73 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1;
lean_ctor_set(x_67, 4, x_73);
lean_ctor_set(x_67, 0, x_72);
x_74 = lean_st_ref_set(x_5, x_67, x_68);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_67, 0);
x_82 = lean_ctor_get(x_67, 1);
x_83 = lean_ctor_get(x_67, 2);
x_84 = lean_ctor_get(x_67, 3);
x_85 = lean_ctor_get(x_67, 5);
x_86 = lean_ctor_get(x_67, 6);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_67);
x_87 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_81, x_65, x_2);
x_88 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1;
x_89 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_84);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_85);
lean_ctor_set(x_89, 6, x_86);
x_90 = lean_st_ref_set(x_5, x_89, x_68);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
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
x_10 = l_Lean_throwError___at_Lean_addDecl___spec__2(x_9, x_3, x_4, x_8);
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
x_14 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1(x_13, x_12, x_2, x_3, x_4, x_11);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1(x_1, x_2, x_7, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attribute cannot be erased", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__1;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__2;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__3;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__5;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__7;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__8;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CSimpAttr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__9;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__11;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__13;
x_2 = lean_unsigned_to_nat(574u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("csimp", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simplification theorem for the compiler", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__14;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__16;
x_3 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__17;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__18;
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__19;
x_3 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__20;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__21;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__2;
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
x_23 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = (size_t)(x_5) & (lean_unbox(x_4) - 1);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
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
x_6 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(x_4, x_2);
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
x_12 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__5(x_11, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_264; size_t x_265; uint8_t x_266; 
x_4 = lean_ptr_addr(x_2);
x_5 = 4;
x_6 = lean_usize_shift_right(x_4, x_5);
x_7 = 8192;
x_8 = lean_usize_mod(x_6, x_7);
x_264 = lean_array_uget(x_3, x_8);
x_265 = lean_ptr_addr(x_264);
lean_dec(x_264);
x_266 = lean_usize_dec_eq(x_4, x_265);
if (x_266 == 0)
{
uint8_t x_267; 
x_267 = l_Lean_Expr_isConst(x_2);
if (x_267 == 0)
{
lean_object* x_268; 
x_268 = lean_box(0);
x_9 = x_268;
goto block_263;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_1, 0);
lean_inc(x_269);
x_270 = l_Lean_Expr_constName_x21(x_2);
x_271 = l_Lean_SMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__1(x_269, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_box(0);
x_9 = x_272;
goto block_263;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; size_t x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_1);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_2);
x_274 = l_Lean_Expr_constLevels_x21(x_2);
x_275 = l_Lean_Expr_const___override(x_273, x_274);
x_276 = lean_array_uset(x_3, x_8, x_2);
x_277 = lean_usize_add(x_8, x_7);
lean_inc(x_275);
x_278 = lean_array_uset(x_276, x_277, x_275);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_275);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
size_t x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_2);
lean_dec(x_1);
x_280 = lean_usize_add(x_8, x_7);
x_281 = lean_array_uget(x_3, x_280);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_3);
return x_282;
}
block_263:
{
lean_dec(x_9);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_10, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_11);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_11, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_2);
x_19 = lean_array_uset(x_18, x_8, x_2);
x_20 = lean_usize_add(x_8, x_7);
x_21 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_22 = lean_ptr_addr(x_13);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = l_Lean_Expr_app___override(x_13, x_17);
lean_inc(x_24);
x_25 = lean_array_uset(x_19, x_20, x_24);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_27 = lean_ptr_addr(x_17);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_29 = l_Lean_Expr_app___override(x_13, x_17);
lean_inc(x_29);
x_30 = lean_array_uset(x_19, x_20, x_29);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_13);
lean_inc(x_2);
x_31 = lean_array_uset(x_19, x_20, x_2);
lean_ctor_set(x_15, 1, x_31);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
lean_inc(x_2);
x_34 = lean_array_uset(x_33, x_8, x_2);
x_35 = lean_usize_add(x_8, x_7);
x_36 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_37 = lean_ptr_addr(x_13);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_2);
x_39 = l_Lean_Expr_app___override(x_13, x_32);
lean_inc(x_39);
x_40 = lean_array_uset(x_34, x_35, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_43 = lean_ptr_addr(x_32);
x_44 = lean_usize_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_45 = l_Lean_Expr_app___override(x_13, x_32);
lean_inc(x_45);
x_46 = lean_array_uset(x_34, x_35, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
lean_dec(x_13);
lean_inc(x_2);
x_48 = lean_array_uset(x_34, x_35, x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
case 6:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_51);
lean_inc(x_1);
x_54 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_51, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_52);
x_57 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_52, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; size_t x_64; size_t x_65; uint8_t x_66; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_array_uset(x_60, x_8, x_2);
x_62 = lean_usize_add(x_8, x_7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_63 = l_Lean_Expr_lam___override(x_50, x_51, x_52, x_53);
x_64 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_65 = lean_ptr_addr(x_55);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_52);
x_67 = l_Lean_Expr_lam___override(x_50, x_55, x_59, x_53);
lean_inc(x_67);
x_68 = lean_array_uset(x_61, x_62, x_67);
lean_ctor_set(x_57, 1, x_68);
lean_ctor_set(x_57, 0, x_67);
return x_57;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_70 = lean_ptr_addr(x_59);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
x_72 = l_Lean_Expr_lam___override(x_50, x_55, x_59, x_53);
lean_inc(x_72);
x_73 = lean_array_uset(x_61, x_62, x_72);
lean_ctor_set(x_57, 1, x_73);
lean_ctor_set(x_57, 0, x_72);
return x_57;
}
else
{
uint8_t x_74; 
x_74 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_53, x_53);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
x_75 = l_Lean_Expr_lam___override(x_50, x_55, x_59, x_53);
lean_inc(x_75);
x_76 = lean_array_uset(x_61, x_62, x_75);
lean_ctor_set(x_57, 1, x_76);
lean_ctor_set(x_57, 0, x_75);
return x_57;
}
else
{
lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_50);
lean_inc(x_63);
x_77 = lean_array_uset(x_61, x_62, x_63);
lean_ctor_set(x_57, 1, x_77);
lean_ctor_set(x_57, 0, x_63);
return x_57;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; lean_object* x_82; size_t x_83; size_t x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_57, 0);
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_57);
x_80 = lean_array_uset(x_79, x_8, x_2);
x_81 = lean_usize_add(x_8, x_7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_82 = l_Lean_Expr_lam___override(x_50, x_51, x_52, x_53);
x_83 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_84 = lean_ptr_addr(x_55);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_82);
lean_dec(x_52);
x_86 = l_Lean_Expr_lam___override(x_50, x_55, x_78, x_53);
lean_inc(x_86);
x_87 = lean_array_uset(x_80, x_81, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
size_t x_89; size_t x_90; uint8_t x_91; 
x_89 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_90 = lean_ptr_addr(x_78);
x_91 = lean_usize_dec_eq(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
x_92 = l_Lean_Expr_lam___override(x_50, x_55, x_78, x_53);
lean_inc(x_92);
x_93 = lean_array_uset(x_80, x_81, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
else
{
uint8_t x_95; 
x_95 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_53, x_53);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
x_96 = l_Lean_Expr_lam___override(x_50, x_55, x_78, x_53);
lean_inc(x_96);
x_97 = lean_array_uset(x_80, x_81, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_78);
lean_dec(x_55);
lean_dec(x_50);
lean_inc(x_82);
x_99 = lean_array_uset(x_80, x_81, x_82);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_82);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_2, 2);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_102);
lean_inc(x_1);
x_105 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_102, x_3);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_103);
x_108 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_103, x_107);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; lean_object* x_114; size_t x_115; size_t x_116; uint8_t x_117; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
x_112 = lean_array_uset(x_111, x_8, x_2);
x_113 = lean_usize_add(x_8, x_7);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_114 = l_Lean_Expr_forallE___override(x_101, x_102, x_103, x_104);
x_115 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_116 = lean_ptr_addr(x_106);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_114);
lean_dec(x_103);
x_118 = l_Lean_Expr_forallE___override(x_101, x_106, x_110, x_104);
lean_inc(x_118);
x_119 = lean_array_uset(x_112, x_113, x_118);
lean_ctor_set(x_108, 1, x_119);
lean_ctor_set(x_108, 0, x_118);
return x_108;
}
else
{
size_t x_120; size_t x_121; uint8_t x_122; 
x_120 = lean_ptr_addr(x_103);
lean_dec(x_103);
x_121 = lean_ptr_addr(x_110);
x_122 = lean_usize_dec_eq(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_114);
x_123 = l_Lean_Expr_forallE___override(x_101, x_106, x_110, x_104);
lean_inc(x_123);
x_124 = lean_array_uset(x_112, x_113, x_123);
lean_ctor_set(x_108, 1, x_124);
lean_ctor_set(x_108, 0, x_123);
return x_108;
}
else
{
uint8_t x_125; 
x_125 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_104, x_104);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_114);
x_126 = l_Lean_Expr_forallE___override(x_101, x_106, x_110, x_104);
lean_inc(x_126);
x_127 = lean_array_uset(x_112, x_113, x_126);
lean_ctor_set(x_108, 1, x_127);
lean_ctor_set(x_108, 0, x_126);
return x_108;
}
else
{
lean_object* x_128; 
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_101);
lean_inc(x_114);
x_128 = lean_array_uset(x_112, x_113, x_114);
lean_ctor_set(x_108, 1, x_128);
lean_ctor_set(x_108, 0, x_114);
return x_108;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; lean_object* x_133; size_t x_134; size_t x_135; uint8_t x_136; 
x_129 = lean_ctor_get(x_108, 0);
x_130 = lean_ctor_get(x_108, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_108);
x_131 = lean_array_uset(x_130, x_8, x_2);
x_132 = lean_usize_add(x_8, x_7);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_133 = l_Lean_Expr_forallE___override(x_101, x_102, x_103, x_104);
x_134 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_135 = lean_ptr_addr(x_106);
x_136 = lean_usize_dec_eq(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_133);
lean_dec(x_103);
x_137 = l_Lean_Expr_forallE___override(x_101, x_106, x_129, x_104);
lean_inc(x_137);
x_138 = lean_array_uset(x_131, x_132, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
size_t x_140; size_t x_141; uint8_t x_142; 
x_140 = lean_ptr_addr(x_103);
lean_dec(x_103);
x_141 = lean_ptr_addr(x_129);
x_142 = lean_usize_dec_eq(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_133);
x_143 = l_Lean_Expr_forallE___override(x_101, x_106, x_129, x_104);
lean_inc(x_143);
x_144 = lean_array_uset(x_131, x_132, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
else
{
uint8_t x_146; 
x_146 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_104, x_104);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_133);
x_147 = l_Lean_Expr_forallE___override(x_101, x_106, x_129, x_104);
lean_inc(x_147);
x_148 = lean_array_uset(x_131, x_132, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_129);
lean_dec(x_106);
lean_dec(x_101);
lean_inc(x_133);
x_150 = lean_array_uset(x_131, x_132, x_133);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_133);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
}
case 8:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_152 = lean_ctor_get(x_2, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_2, 3);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_153);
lean_inc(x_1);
x_157 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_153, x_3);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_154);
lean_inc(x_1);
x_160 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_154, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_155);
x_163 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_155, x_162);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; size_t x_168; size_t x_169; size_t x_170; uint8_t x_171; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_2);
x_167 = lean_array_uset(x_166, x_8, x_2);
x_168 = lean_usize_add(x_8, x_7);
x_169 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_170 = lean_ptr_addr(x_158);
x_171 = lean_usize_dec_eq(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_2);
x_172 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_165, x_156);
lean_inc(x_172);
x_173 = lean_array_uset(x_167, x_168, x_172);
lean_ctor_set(x_163, 1, x_173);
lean_ctor_set(x_163, 0, x_172);
return x_163;
}
else
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_154);
lean_dec(x_154);
x_175 = lean_ptr_addr(x_161);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_155);
lean_dec(x_2);
x_177 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_165, x_156);
lean_inc(x_177);
x_178 = lean_array_uset(x_167, x_168, x_177);
lean_ctor_set(x_163, 1, x_178);
lean_ctor_set(x_163, 0, x_177);
return x_163;
}
else
{
size_t x_179; size_t x_180; uint8_t x_181; 
x_179 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_180 = lean_ptr_addr(x_165);
x_181 = lean_usize_dec_eq(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_2);
x_182 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_165, x_156);
lean_inc(x_182);
x_183 = lean_array_uset(x_167, x_168, x_182);
lean_ctor_set(x_163, 1, x_183);
lean_ctor_set(x_163, 0, x_182);
return x_163;
}
else
{
lean_object* x_184; 
lean_dec(x_165);
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_152);
lean_inc(x_2);
x_184 = lean_array_uset(x_167, x_168, x_2);
lean_ctor_set(x_163, 1, x_184);
lean_ctor_set(x_163, 0, x_2);
return x_163;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; size_t x_188; size_t x_189; size_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_163, 0);
x_186 = lean_ctor_get(x_163, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_163);
lean_inc(x_2);
x_187 = lean_array_uset(x_186, x_8, x_2);
x_188 = lean_usize_add(x_8, x_7);
x_189 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_190 = lean_ptr_addr(x_158);
x_191 = lean_usize_dec_eq(x_189, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_2);
x_192 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_185, x_156);
lean_inc(x_192);
x_193 = lean_array_uset(x_187, x_188, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
else
{
size_t x_195; size_t x_196; uint8_t x_197; 
x_195 = lean_ptr_addr(x_154);
lean_dec(x_154);
x_196 = lean_ptr_addr(x_161);
x_197 = lean_usize_dec_eq(x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_155);
lean_dec(x_2);
x_198 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_185, x_156);
lean_inc(x_198);
x_199 = lean_array_uset(x_187, x_188, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
else
{
size_t x_201; size_t x_202; uint8_t x_203; 
x_201 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_202 = lean_ptr_addr(x_185);
x_203 = lean_usize_dec_eq(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_2);
x_204 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_185, x_156);
lean_inc(x_204);
x_205 = lean_array_uset(x_187, x_188, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_185);
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_152);
lean_inc(x_2);
x_207 = lean_array_uset(x_187, x_188, x_2);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_2);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
}
case 10:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_2, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_2, 1);
lean_inc(x_210);
lean_inc(x_210);
x_211 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_210, x_3);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; size_t x_216; size_t x_217; size_t x_218; uint8_t x_219; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_2);
x_215 = lean_array_uset(x_214, x_8, x_2);
x_216 = lean_usize_add(x_8, x_7);
x_217 = lean_ptr_addr(x_210);
lean_dec(x_210);
x_218 = lean_ptr_addr(x_213);
x_219 = lean_usize_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_2);
x_220 = l_Lean_Expr_mdata___override(x_209, x_213);
lean_inc(x_220);
x_221 = lean_array_uset(x_215, x_216, x_220);
lean_ctor_set(x_211, 1, x_221);
lean_ctor_set(x_211, 0, x_220);
return x_211;
}
else
{
lean_object* x_222; 
lean_dec(x_213);
lean_dec(x_209);
lean_inc(x_2);
x_222 = lean_array_uset(x_215, x_216, x_2);
lean_ctor_set(x_211, 1, x_222);
lean_ctor_set(x_211, 0, x_2);
return x_211;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; size_t x_226; size_t x_227; size_t x_228; uint8_t x_229; 
x_223 = lean_ctor_get(x_211, 0);
x_224 = lean_ctor_get(x_211, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_211);
lean_inc(x_2);
x_225 = lean_array_uset(x_224, x_8, x_2);
x_226 = lean_usize_add(x_8, x_7);
x_227 = lean_ptr_addr(x_210);
lean_dec(x_210);
x_228 = lean_ptr_addr(x_223);
x_229 = lean_usize_dec_eq(x_227, x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_2);
x_230 = l_Lean_Expr_mdata___override(x_209, x_223);
lean_inc(x_230);
x_231 = lean_array_uset(x_225, x_226, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_223);
lean_dec(x_209);
lean_inc(x_2);
x_233 = lean_array_uset(x_225, x_226, x_2);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_2);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
case 11:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_2, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_2, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_2, 2);
lean_inc(x_237);
lean_inc(x_237);
x_238 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_237, x_3);
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; size_t x_243; size_t x_244; size_t x_245; uint8_t x_246; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_2);
x_242 = lean_array_uset(x_241, x_8, x_2);
x_243 = lean_usize_add(x_8, x_7);
x_244 = lean_ptr_addr(x_237);
lean_dec(x_237);
x_245 = lean_ptr_addr(x_240);
x_246 = lean_usize_dec_eq(x_244, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_2);
x_247 = l_Lean_Expr_proj___override(x_235, x_236, x_240);
lean_inc(x_247);
x_248 = lean_array_uset(x_242, x_243, x_247);
lean_ctor_set(x_238, 1, x_248);
lean_ctor_set(x_238, 0, x_247);
return x_238;
}
else
{
lean_object* x_249; 
lean_dec(x_240);
lean_dec(x_236);
lean_dec(x_235);
lean_inc(x_2);
x_249 = lean_array_uset(x_242, x_243, x_2);
lean_ctor_set(x_238, 1, x_249);
lean_ctor_set(x_238, 0, x_2);
return x_238;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; size_t x_253; size_t x_254; size_t x_255; uint8_t x_256; 
x_250 = lean_ctor_get(x_238, 0);
x_251 = lean_ctor_get(x_238, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_238);
lean_inc(x_2);
x_252 = lean_array_uset(x_251, x_8, x_2);
x_253 = lean_usize_add(x_8, x_7);
x_254 = lean_ptr_addr(x_237);
lean_dec(x_237);
x_255 = lean_ptr_addr(x_250);
x_256 = lean_usize_dec_eq(x_254, x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_2);
x_257 = l_Lean_Expr_proj___override(x_235, x_236, x_250);
lean_inc(x_257);
x_258 = lean_array_uset(x_252, x_253, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_250);
lean_dec(x_236);
lean_dec(x_235);
lean_inc(x_2);
x_260 = lean_array_uset(x_252, x_253, x_2);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_2);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
default: 
{
lean_object* x_262; 
lean_dec(x_1);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_2);
lean_ctor_set(x_262, 1, x_3);
return x_262;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_csimp_replace_constants(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Compiler_CSimp_instInhabitedState;
x_4 = l_Lean_Compiler_CSimp_add___closed__3;
x_5 = l_Lean_ScopedEnvExtension_getState___rarg(x_3, x_4, x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceImpl_Cache_new;
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_5, x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_CSimp_replaceConstants___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_CSimp_replaceConstants___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__6(x_1, x_2);
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
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____spec__3___closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__1);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__2);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__3 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__3();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__4 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__4();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__4);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__5 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__5();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__5);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__6 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__6();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__6);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__7 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__7();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__7);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__8 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__8();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174____closed__8);
if (builtin) {res = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_174_(lean_io_mk_world());
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
l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Compiler_CSimp_add___spec__1___closed__1);
l_Lean_Compiler_CSimp_add___closed__1 = _init_l_Lean_Compiler_CSimp_add___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_add___closed__1);
l_Lean_Compiler_CSimp_add___closed__2 = _init_l_Lean_Compiler_CSimp_add___closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_add___closed__2);
l_Lean_Compiler_CSimp_add___closed__3 = _init_l_Lean_Compiler_CSimp_add___closed__3();
lean_mark_persistent(l_Lean_Compiler_CSimp_add___closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__1 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__1);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__2 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____lambda__2___closed__2);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__1 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__1();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__1);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__2 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__2();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__2);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__3 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__3();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__3);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__4 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__4();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__4);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__5 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__5();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__5);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__6 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__6();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__6);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__7 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__7();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__7);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__8 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__8();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__8);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__9 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__9();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__9);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__10 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__10();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__10);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__11 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__11();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__11);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__12 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__12();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__12);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__13 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__13();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__13);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__14 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__14();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__14);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__15 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__15();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__15);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__16 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__16();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__16);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__17 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__17();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__17);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__18 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__18();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__18);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__19 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__19();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__19);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__20 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__20();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__20);
l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__21 = _init_l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__21();
lean_mark_persistent(l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574____closed__21);
res = l_Lean_Compiler_CSimp_initFn____x40_Lean_Compiler_CSimpAttr___hyg_574_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
