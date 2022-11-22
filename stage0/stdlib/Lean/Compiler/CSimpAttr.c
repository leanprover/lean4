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
size_t x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_262; size_t x_263; uint8_t x_264; 
x_4 = lean_ptr_addr(x_2);
x_5 = 8191;
x_6 = lean_usize_mod(x_4, x_5);
x_262 = lean_array_uget(x_3, x_6);
x_263 = lean_ptr_addr(x_262);
lean_dec(x_262);
x_264 = lean_usize_dec_eq(x_4, x_263);
if (x_264 == 0)
{
uint8_t x_265; 
x_265 = l_Lean_Expr_isConst(x_2);
if (x_265 == 0)
{
lean_object* x_266; 
x_266 = lean_box(0);
x_7 = x_266;
goto block_261;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_1, 0);
lean_inc(x_267);
x_268 = l_Lean_Expr_constName_x21(x_2);
x_269 = l_Lean_SMap_find_x3f___at_Lean_Compiler_CSimp_replaceConstants___spec__1(x_267, x_268);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_box(0);
x_7 = x_270;
goto block_261;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; size_t x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_1);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_2);
x_272 = l_Lean_Expr_constLevels_x21(x_2);
x_273 = l_Lean_Expr_const___override(x_271, x_272);
x_274 = lean_array_uset(x_3, x_6, x_2);
x_275 = lean_usize_add(x_6, x_5);
lean_inc(x_273);
x_276 = lean_array_uset(x_274, x_275, x_273);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_273);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
else
{
size_t x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_2);
lean_dec(x_1);
x_278 = lean_usize_add(x_6, x_5);
x_279 = lean_array_uget(x_3, x_278);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_3);
return x_280;
}
block_261:
{
lean_dec(x_7);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_8, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_9);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_2);
x_17 = lean_array_uset(x_16, x_6, x_2);
x_18 = lean_usize_add(x_6, x_5);
x_19 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_20 = lean_ptr_addr(x_11);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_2);
x_22 = l_Lean_Expr_app___override(x_11, x_15);
lean_inc(x_22);
x_23 = lean_array_uset(x_17, x_18, x_22);
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_25 = lean_ptr_addr(x_15);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_27 = l_Lean_Expr_app___override(x_11, x_15);
lean_inc(x_27);
x_28 = lean_array_uset(x_17, x_18, x_27);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_11);
lean_inc(x_2);
x_29 = lean_array_uset(x_17, x_18, x_2);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; size_t x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
lean_inc(x_2);
x_32 = lean_array_uset(x_31, x_6, x_2);
x_33 = lean_usize_add(x_6, x_5);
x_34 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_35 = lean_ptr_addr(x_11);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_2);
x_37 = l_Lean_Expr_app___override(x_11, x_30);
lean_inc(x_37);
x_38 = lean_array_uset(x_32, x_33, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_41 = lean_ptr_addr(x_30);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_43 = l_Lean_Expr_app___override(x_11, x_30);
lean_inc(x_43);
x_44 = lean_array_uset(x_32, x_33, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
lean_dec(x_11);
lean_inc(x_2);
x_46 = lean_array_uset(x_32, x_33, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_49);
lean_inc(x_1);
x_52 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_49, x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_50, x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; lean_object* x_61; size_t x_62; size_t x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_array_uset(x_58, x_6, x_2);
x_60 = lean_usize_add(x_6, x_5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_61 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_62 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_63 = lean_ptr_addr(x_53);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_50);
x_65 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_65);
x_66 = lean_array_uset(x_59, x_60, x_65);
lean_ctor_set(x_55, 1, x_66);
lean_ctor_set(x_55, 0, x_65);
return x_55;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; 
x_67 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_68 = lean_ptr_addr(x_57);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
x_70 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_70);
x_71 = lean_array_uset(x_59, x_60, x_70);
lean_ctor_set(x_55, 1, x_71);
lean_ctor_set(x_55, 0, x_70);
return x_55;
}
else
{
uint8_t x_72; 
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_51, x_51);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
x_73 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_73);
x_74 = lean_array_uset(x_59, x_60, x_73);
lean_ctor_set(x_55, 1, x_74);
lean_ctor_set(x_55, 0, x_73);
return x_55;
}
else
{
lean_object* x_75; 
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_48);
lean_inc(x_61);
x_75 = lean_array_uset(x_59, x_60, x_61);
lean_ctor_set(x_55, 1, x_75);
lean_ctor_set(x_55, 0, x_61);
return x_55;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; size_t x_81; size_t x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_55, 0);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_55);
x_78 = lean_array_uset(x_77, x_6, x_2);
x_79 = lean_usize_add(x_6, x_5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_80 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_81 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_82 = lean_ptr_addr(x_53);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_50);
x_84 = l_Lean_Expr_lam___override(x_48, x_53, x_76, x_51);
lean_inc(x_84);
x_85 = lean_array_uset(x_78, x_79, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
size_t x_87; size_t x_88; uint8_t x_89; 
x_87 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_88 = lean_ptr_addr(x_76);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_80);
x_90 = l_Lean_Expr_lam___override(x_48, x_53, x_76, x_51);
lean_inc(x_90);
x_91 = lean_array_uset(x_78, x_79, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_51, x_51);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_80);
x_94 = l_Lean_Expr_lam___override(x_48, x_53, x_76, x_51);
lean_inc(x_94);
x_95 = lean_array_uset(x_78, x_79, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_76);
lean_dec(x_53);
lean_dec(x_48);
lean_inc(x_80);
x_97 = lean_array_uset(x_78, x_79, x_80);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_80);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_99 = lean_ctor_get(x_2, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 2);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_100);
lean_inc(x_1);
x_103 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_100, x_3);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_101);
x_106 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_101, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; lean_object* x_112; size_t x_113; size_t x_114; uint8_t x_115; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
x_110 = lean_array_uset(x_109, x_6, x_2);
x_111 = lean_usize_add(x_6, x_5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_112 = l_Lean_Expr_forallE___override(x_99, x_100, x_101, x_102);
x_113 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_114 = lean_ptr_addr(x_104);
x_115 = lean_usize_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
lean_dec(x_101);
x_116 = l_Lean_Expr_forallE___override(x_99, x_104, x_108, x_102);
lean_inc(x_116);
x_117 = lean_array_uset(x_110, x_111, x_116);
lean_ctor_set(x_106, 1, x_117);
lean_ctor_set(x_106, 0, x_116);
return x_106;
}
else
{
size_t x_118; size_t x_119; uint8_t x_120; 
x_118 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_119 = lean_ptr_addr(x_108);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_112);
x_121 = l_Lean_Expr_forallE___override(x_99, x_104, x_108, x_102);
lean_inc(x_121);
x_122 = lean_array_uset(x_110, x_111, x_121);
lean_ctor_set(x_106, 1, x_122);
lean_ctor_set(x_106, 0, x_121);
return x_106;
}
else
{
uint8_t x_123; 
x_123 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_102, x_102);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_112);
x_124 = l_Lean_Expr_forallE___override(x_99, x_104, x_108, x_102);
lean_inc(x_124);
x_125 = lean_array_uset(x_110, x_111, x_124);
lean_ctor_set(x_106, 1, x_125);
lean_ctor_set(x_106, 0, x_124);
return x_106;
}
else
{
lean_object* x_126; 
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_99);
lean_inc(x_112);
x_126 = lean_array_uset(x_110, x_111, x_112);
lean_ctor_set(x_106, 1, x_126);
lean_ctor_set(x_106, 0, x_112);
return x_106;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; lean_object* x_131; size_t x_132; size_t x_133; uint8_t x_134; 
x_127 = lean_ctor_get(x_106, 0);
x_128 = lean_ctor_get(x_106, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_106);
x_129 = lean_array_uset(x_128, x_6, x_2);
x_130 = lean_usize_add(x_6, x_5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_131 = l_Lean_Expr_forallE___override(x_99, x_100, x_101, x_102);
x_132 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_133 = lean_ptr_addr(x_104);
x_134 = lean_usize_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_131);
lean_dec(x_101);
x_135 = l_Lean_Expr_forallE___override(x_99, x_104, x_127, x_102);
lean_inc(x_135);
x_136 = lean_array_uset(x_129, x_130, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
else
{
size_t x_138; size_t x_139; uint8_t x_140; 
x_138 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_139 = lean_ptr_addr(x_127);
x_140 = lean_usize_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_131);
x_141 = l_Lean_Expr_forallE___override(x_99, x_104, x_127, x_102);
lean_inc(x_141);
x_142 = lean_array_uset(x_129, x_130, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
else
{
uint8_t x_144; 
x_144 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_102, x_102);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_131);
x_145 = l_Lean_Expr_forallE___override(x_99, x_104, x_127, x_102);
lean_inc(x_145);
x_146 = lean_array_uset(x_129, x_130, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
lean_dec(x_104);
lean_dec(x_99);
lean_inc(x_131);
x_148 = lean_array_uset(x_129, x_130, x_131);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_131);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
}
case 8:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_150 = lean_ctor_get(x_2, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 3);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_151);
lean_inc(x_1);
x_155 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_151, x_3);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_152);
lean_inc(x_1);
x_158 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_152, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_153);
x_161 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_153, x_160);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; size_t x_166; size_t x_167; size_t x_168; uint8_t x_169; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_2);
x_165 = lean_array_uset(x_164, x_6, x_2);
x_166 = lean_usize_add(x_6, x_5);
x_167 = lean_ptr_addr(x_151);
lean_dec(x_151);
x_168 = lean_ptr_addr(x_156);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_2);
x_170 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_163, x_154);
lean_inc(x_170);
x_171 = lean_array_uset(x_165, x_166, x_170);
lean_ctor_set(x_161, 1, x_171);
lean_ctor_set(x_161, 0, x_170);
return x_161;
}
else
{
size_t x_172; size_t x_173; uint8_t x_174; 
x_172 = lean_ptr_addr(x_152);
lean_dec(x_152);
x_173 = lean_ptr_addr(x_159);
x_174 = lean_usize_dec_eq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_153);
lean_dec(x_2);
x_175 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_163, x_154);
lean_inc(x_175);
x_176 = lean_array_uset(x_165, x_166, x_175);
lean_ctor_set(x_161, 1, x_176);
lean_ctor_set(x_161, 0, x_175);
return x_161;
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_178 = lean_ptr_addr(x_163);
x_179 = lean_usize_dec_eq(x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_2);
x_180 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_163, x_154);
lean_inc(x_180);
x_181 = lean_array_uset(x_165, x_166, x_180);
lean_ctor_set(x_161, 1, x_181);
lean_ctor_set(x_161, 0, x_180);
return x_161;
}
else
{
lean_object* x_182; 
lean_dec(x_163);
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_150);
lean_inc(x_2);
x_182 = lean_array_uset(x_165, x_166, x_2);
lean_ctor_set(x_161, 1, x_182);
lean_ctor_set(x_161, 0, x_2);
return x_161;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; size_t x_186; size_t x_187; size_t x_188; uint8_t x_189; 
x_183 = lean_ctor_get(x_161, 0);
x_184 = lean_ctor_get(x_161, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_161);
lean_inc(x_2);
x_185 = lean_array_uset(x_184, x_6, x_2);
x_186 = lean_usize_add(x_6, x_5);
x_187 = lean_ptr_addr(x_151);
lean_dec(x_151);
x_188 = lean_ptr_addr(x_156);
x_189 = lean_usize_dec_eq(x_187, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_2);
x_190 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_183, x_154);
lean_inc(x_190);
x_191 = lean_array_uset(x_185, x_186, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
else
{
size_t x_193; size_t x_194; uint8_t x_195; 
x_193 = lean_ptr_addr(x_152);
lean_dec(x_152);
x_194 = lean_ptr_addr(x_159);
x_195 = lean_usize_dec_eq(x_193, x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_153);
lean_dec(x_2);
x_196 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_183, x_154);
lean_inc(x_196);
x_197 = lean_array_uset(x_185, x_186, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
else
{
size_t x_199; size_t x_200; uint8_t x_201; 
x_199 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_200 = lean_ptr_addr(x_183);
x_201 = lean_usize_dec_eq(x_199, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_2);
x_202 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_183, x_154);
lean_inc(x_202);
x_203 = lean_array_uset(x_185, x_186, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_183);
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_150);
lean_inc(x_2);
x_205 = lean_array_uset(x_185, x_186, x_2);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_2);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
}
case 10:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_2, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_2, 1);
lean_inc(x_208);
lean_inc(x_208);
x_209 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_208, x_3);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; size_t x_214; size_t x_215; size_t x_216; uint8_t x_217; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_2);
x_213 = lean_array_uset(x_212, x_6, x_2);
x_214 = lean_usize_add(x_6, x_5);
x_215 = lean_ptr_addr(x_208);
lean_dec(x_208);
x_216 = lean_ptr_addr(x_211);
x_217 = lean_usize_dec_eq(x_215, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_2);
x_218 = l_Lean_Expr_mdata___override(x_207, x_211);
lean_inc(x_218);
x_219 = lean_array_uset(x_213, x_214, x_218);
lean_ctor_set(x_209, 1, x_219);
lean_ctor_set(x_209, 0, x_218);
return x_209;
}
else
{
lean_object* x_220; 
lean_dec(x_211);
lean_dec(x_207);
lean_inc(x_2);
x_220 = lean_array_uset(x_213, x_214, x_2);
lean_ctor_set(x_209, 1, x_220);
lean_ctor_set(x_209, 0, x_2);
return x_209;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; size_t x_224; size_t x_225; size_t x_226; uint8_t x_227; 
x_221 = lean_ctor_get(x_209, 0);
x_222 = lean_ctor_get(x_209, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_209);
lean_inc(x_2);
x_223 = lean_array_uset(x_222, x_6, x_2);
x_224 = lean_usize_add(x_6, x_5);
x_225 = lean_ptr_addr(x_208);
lean_dec(x_208);
x_226 = lean_ptr_addr(x_221);
x_227 = lean_usize_dec_eq(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_2);
x_228 = l_Lean_Expr_mdata___override(x_207, x_221);
lean_inc(x_228);
x_229 = lean_array_uset(x_223, x_224, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_221);
lean_dec(x_207);
lean_inc(x_2);
x_231 = lean_array_uset(x_223, x_224, x_2);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_2);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
case 11:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_233 = lean_ctor_get(x_2, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_2, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_2, 2);
lean_inc(x_235);
lean_inc(x_235);
x_236 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_CSimp_replaceConstants___spec__7(x_1, x_235, x_3);
x_237 = !lean_is_exclusive(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; size_t x_241; size_t x_242; size_t x_243; uint8_t x_244; 
x_238 = lean_ctor_get(x_236, 0);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_2);
x_240 = lean_array_uset(x_239, x_6, x_2);
x_241 = lean_usize_add(x_6, x_5);
x_242 = lean_ptr_addr(x_235);
lean_dec(x_235);
x_243 = lean_ptr_addr(x_238);
x_244 = lean_usize_dec_eq(x_242, x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_2);
x_245 = l_Lean_Expr_proj___override(x_233, x_234, x_238);
lean_inc(x_245);
x_246 = lean_array_uset(x_240, x_241, x_245);
lean_ctor_set(x_236, 1, x_246);
lean_ctor_set(x_236, 0, x_245);
return x_236;
}
else
{
lean_object* x_247; 
lean_dec(x_238);
lean_dec(x_234);
lean_dec(x_233);
lean_inc(x_2);
x_247 = lean_array_uset(x_240, x_241, x_2);
lean_ctor_set(x_236, 1, x_247);
lean_ctor_set(x_236, 0, x_2);
return x_236;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; size_t x_251; size_t x_252; size_t x_253; uint8_t x_254; 
x_248 = lean_ctor_get(x_236, 0);
x_249 = lean_ctor_get(x_236, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_236);
lean_inc(x_2);
x_250 = lean_array_uset(x_249, x_6, x_2);
x_251 = lean_usize_add(x_6, x_5);
x_252 = lean_ptr_addr(x_235);
lean_dec(x_235);
x_253 = lean_ptr_addr(x_248);
x_254 = lean_usize_dec_eq(x_252, x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_2);
x_255 = l_Lean_Expr_proj___override(x_233, x_234, x_248);
lean_inc(x_255);
x_256 = lean_array_uset(x_250, x_251, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_248);
lean_dec(x_234);
lean_dec(x_233);
lean_inc(x_2);
x_258 = lean_array_uset(x_250, x_251, x_2);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_2);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
default: 
{
lean_object* x_260; 
lean_dec(x_1);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_2);
lean_ctor_set(x_260, 1, x_3);
return x_260;
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
