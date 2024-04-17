// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Attr
// Imports: Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.Simproc
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
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__10;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__6;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__13;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__12;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__4;
lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__15;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__22;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_ofNatTruncate(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_registerSimpAttr___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__9;
lean_object* l_Array_instBEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__3;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__15;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__8;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__6;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__21;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEq;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__11;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__13;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__17;
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8_;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__26;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2;
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__5(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__14;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__12;
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_sevalSimpExtension;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__28;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__9;
static lean_object* l_Lean_Meta_getSimpTheorems___closed__1;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__15;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__7;
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object*, lean_object*);
static uint32_t l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__11;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getSEvalTheorems___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__4;
lean_object* l_Lean_ScopedEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerSimpAttr___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__25;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtension;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__5;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__12;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__24;
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__27;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__3;
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_647_;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__14;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__7;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__29;
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__5;
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__10;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__16;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_Expr_instHashable;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__9;
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__18;
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__18;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__16;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__1;
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__23;
extern lean_object* l_Lean_Meta_simpExtensionMapRef;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747_(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_registerSimpAttr___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__10;
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__8;
lean_object* l_Lean_Meta_InfoCacheKey_instHashable___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773_(lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__17;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__1;
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__8;
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq", 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq1Indented", 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exact", 5);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__11;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declName", 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__15;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__16;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decl_name%", 10);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__18;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__17;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__20;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__14;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__12;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__22;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__23;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__10;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__24;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__25;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__8;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__26;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__27;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__5;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__28;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__29;
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashable___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__8;
x_2 = lean_alloc_closure((void*)(l_Array_instBEq___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__9;
x_2 = l_Lean_Expr_instBEq;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__11;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__12;
x_2 = l_Lean_Expr_instHashable;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEq;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashable;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__17;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
x_2 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__7;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__14;
x_4 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__18;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (x_3) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 4);
lean_dec(x_14);
x_15 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_13, x_2);
x_16 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
lean_ctor_set(x_10, 4, x_16);
lean_ctor_set(x_10, 0, x_15);
x_17 = lean_st_ref_set(x_7, x_10, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
x_24 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
lean_ctor_set(x_20, 1, x_24);
x_25 = lean_st_ref_set(x_5, x_20, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 2);
x_34 = lean_ctor_get(x_20, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_35 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
x_37 = lean_st_ref_set(x_5, x_36, x_21);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
x_44 = lean_ctor_get(x_10, 2);
x_45 = lean_ctor_get(x_10, 3);
x_46 = lean_ctor_get(x_10, 5);
x_47 = lean_ctor_get(x_10, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_48 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_42, x_2);
x_49 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
x_50 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
x_51 = lean_st_ref_set(x_7, x_50, x_11);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_take(x_5, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 3);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 4, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_58);
x_62 = lean_st_ref_set(x_5, x_61, x_55);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
case 1:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_6);
x_67 = lean_st_ref_take(x_7, x_8);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 4);
lean_dec(x_72);
x_73 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_71, x_2);
x_74 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
lean_ctor_set(x_68, 4, x_74);
lean_ctor_set(x_68, 0, x_73);
x_75 = lean_st_ref_set(x_7, x_68, x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_take(x_5, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_78, 1);
lean_dec(x_81);
x_82 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
lean_ctor_set(x_78, 1, x_82);
x_83 = lean_st_ref_set(x_5, x_78, x_79);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_ctor_set(x_83, 0, x_86);
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_78, 0);
x_91 = lean_ctor_get(x_78, 2);
x_92 = lean_ctor_get(x_78, 3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_78);
x_93 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_91);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_st_ref_set(x_5, x_94, x_79);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_100 = lean_ctor_get(x_68, 0);
x_101 = lean_ctor_get(x_68, 1);
x_102 = lean_ctor_get(x_68, 2);
x_103 = lean_ctor_get(x_68, 3);
x_104 = lean_ctor_get(x_68, 5);
x_105 = lean_ctor_get(x_68, 6);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_68);
x_106 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_100, x_2);
x_107 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
x_108 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_101);
lean_ctor_set(x_108, 2, x_102);
lean_ctor_set(x_108, 3, x_103);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_104);
lean_ctor_set(x_108, 6, x_105);
x_109 = lean_st_ref_set(x_7, x_108, x_69);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_take(x_5, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 x_117 = x_112;
} else {
 lean_dec_ref(x_112);
 x_117 = lean_box(0);
}
x_118 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 4, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_115);
lean_ctor_set(x_119, 3, x_116);
x_120 = lean_st_ref_set(x_5, x_119, x_113);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
default: 
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_6, 6);
lean_inc(x_125);
lean_dec(x_6);
x_126 = lean_st_ref_take(x_7, x_8);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_130 = lean_ctor_get(x_127, 0);
x_131 = lean_ctor_get(x_127, 4);
lean_dec(x_131);
x_132 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_130, x_125, x_2);
x_133 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
lean_ctor_set(x_127, 4, x_133);
lean_ctor_set(x_127, 0, x_132);
x_134 = lean_st_ref_set(x_7, x_127, x_128);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_st_ref_take(x_5, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = !lean_is_exclusive(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = lean_ctor_get(x_137, 1);
lean_dec(x_140);
x_141 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
lean_ctor_set(x_137, 1, x_141);
x_142 = lean_st_ref_set(x_5, x_137, x_138);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
lean_dec(x_144);
x_145 = lean_box(0);
lean_ctor_set(x_142, 0, x_145);
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_149 = lean_ctor_get(x_137, 0);
x_150 = lean_ctor_get(x_137, 2);
x_151 = lean_ctor_get(x_137, 3);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_137);
x_152 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
x_153 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_151);
x_154 = lean_st_ref_set(x_5, x_153, x_138);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
x_157 = lean_box(0);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_159 = lean_ctor_get(x_127, 0);
x_160 = lean_ctor_get(x_127, 1);
x_161 = lean_ctor_get(x_127, 2);
x_162 = lean_ctor_get(x_127, 3);
x_163 = lean_ctor_get(x_127, 5);
x_164 = lean_ctor_get(x_127, 6);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_127);
x_165 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_159, x_125, x_2);
x_166 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
x_167 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_162);
lean_ctor_set(x_167, 4, x_166);
lean_ctor_set(x_167, 5, x_163);
lean_ctor_set(x_167, 6, x_164);
x_168 = lean_st_ref_set(x_7, x_167, x_128);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_st_ref_take(x_5, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 3);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 4, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_174);
lean_ctor_set(x_178, 3, x_175);
x_179 = lean_st_ref_set(x_5, x_178, x_172);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
x_17 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Lean_Meta_addSimpTheorem(x_1, x_16, x_3, x_17, x_2, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_22 = lean_box(0);
x_7 = x_21;
x_8 = x_22;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' does not have [simp] attribute", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_19; 
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_19 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_box(0);
x_6 = x_21;
goto block_18;
}
else
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_inc(x_23);
lean_inc(x_1);
x_24 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_1, 5);
lean_inc(x_25);
x_26 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_25, x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_box(0);
x_6 = x_27;
goto block_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_28, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_30, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_1);
x_32 = lean_box(0);
x_6 = x_32;
goto block_18;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = lean_box(0);
x_6 = x_33;
goto block_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_34, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_35;
}
block_18:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
x_7 = l_Lean_Meta_Origin_key(x_2);
lean_dec(x_2);
x_8 = l_Lean_MessageData_ofName(x_7);
x_9 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(x_12, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_2);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_2);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__4;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__2;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__1;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__6;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__8;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__9;
x_4 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__10;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'simp', it is not a proposition nor a definition (to unfold)", 68);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpPost", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_125 = l_Lean_Meta_Simp_isSimproc(x_3, x_6, x_7, x_8);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_126);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
lean_inc(x_3);
x_129 = l_Lean_Meta_Simp_isBuiltinSimproc(x_3, x_6, x_7, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_unbox(x_130);
lean_dec(x_130);
x_9 = x_132;
x_10 = x_131;
goto block_124;
}
else
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
lean_dec(x_125);
x_134 = lean_unbox(x_126);
lean_dec(x_126);
x_9 = x_134;
x_10 = x_133;
goto block_124;
}
block_124:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_11 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__11;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_25 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__7;
lean_inc(x_3);
x_26 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_25, x_13, x_6, x_7, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_94 = lean_unsigned_to_nat(1u);
x_95 = l_Lean_Syntax_getArg(x_4, x_94);
x_96 = l_Lean_Syntax_isNone(x_95);
x_97 = lean_unsigned_to_nat(2u);
x_98 = l_Lean_Syntax_getArg(x_4, x_97);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_6);
x_99 = l_Lean_getAttrParamOptPrio(x_98, x_6, x_7, x_28);
if (x_96 == 0)
{
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lean_Syntax_getArg(x_95, x_102);
lean_dec(x_95);
x_104 = l_Lean_Syntax_getKind(x_103);
x_105 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__15;
x_106 = lean_name_eq(x_104, x_105);
lean_dec(x_104);
x_29 = x_106;
x_30 = x_100;
x_31 = x_101;
goto block_93;
}
else
{
uint8_t x_107; 
lean_dec(x_95);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_99);
if (x_107 == 0)
{
return x_99;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_99, 0);
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_99);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_dec(x_95);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
lean_dec(x_99);
x_113 = 1;
x_29 = x_113;
x_30 = x_111;
x_31 = x_112;
goto block_93;
}
else
{
uint8_t x_114; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_99);
if (x_114 == 0)
{
return x_99;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_99, 0);
x_116 = lean_ctor_get(x_99, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_99);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
block_93:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_ConstantInfo_type(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_33 = l_Lean_Meta_isProp(x_32, x_25, x_13, x_6, x_7, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_ConstantInfo_hasValue(x_27);
lean_dec(x_27);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_1);
x_38 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__13;
x_39 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_38, x_25, x_13, x_6, x_7, x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_13);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; lean_object* x_45; 
x_44 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_3);
x_45 = l_Lean_Meta_getEqnsFor_x3f(x_3, x_44, x_25, x_13, x_6, x_7, x_36);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_30);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_3);
x_49 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_48, x_5, x_25, x_13, x_6, x_7, x_47);
lean_dec(x_7);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_15 = x_50;
x_16 = x_51;
goto block_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_array_get_size(x_53);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = 0;
x_57 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_1);
x_58 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_1, x_5, x_29, x_30, x_53, x_55, x_56, x_57, x_25, x_13, x_6, x_7, x_52);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_3);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_53);
lean_inc(x_6);
lean_inc(x_1);
x_61 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_60, x_5, x_25, x_13, x_6, x_7, x_59);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_get(x_7, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_3);
x_67 = l_Lean_Meta_hasSmartUnfoldingDecl(x_66, x_3);
if (x_67 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_15 = x_57;
x_16 = x_65;
goto block_24;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_3);
x_69 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_68, x_5, x_25, x_13, x_6, x_7, x_65);
lean_dec(x_7);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_15 = x_70;
x_16 = x_71;
goto block_24;
}
}
else
{
uint8_t x_72; 
lean_dec(x_53);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_58);
if (x_72 == 0)
{
return x_58;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_58, 0);
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_58);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_45);
if (x_76 == 0)
{
return x_45;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_45, 0);
x_78 = lean_ctor_get(x_45, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_45);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; 
lean_dec(x_27);
x_80 = lean_ctor_get(x_33, 1);
lean_inc(x_80);
lean_dec(x_33);
x_81 = 0;
lean_inc(x_13);
x_82 = l_Lean_Meta_addSimpTheorem(x_1, x_3, x_29, x_81, x_5, x_30, x_25, x_13, x_6, x_7, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_15 = x_83;
x_16 = x_84;
goto block_24;
}
else
{
uint8_t x_85; 
lean_dec(x_13);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_82);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_33);
if (x_89 == 0)
{
return x_33;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_33, 0);
x_91 = lean_ctor_get(x_33, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_33);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_26);
if (x_118 == 0)
{
return x_26;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_26, 0);
x_120 = lean_ctor_get(x_26, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_26);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
block_24:
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_15);
x_17 = lean_st_ref_get(x_13, x_16);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_1);
x_122 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_2);
x_123 = l_Lean_Attribute_add(x_3, x_122, x_4, x_5, x_6, x_7, x_10);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l_Lean_Meta_Simp_isSimproc(x_3, x_4, x_5, x_6);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_3);
x_63 = l_Lean_Meta_Simp_isBuiltinSimproc(x_3, x_4, x_5, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unbox(x_64);
lean_dec(x_64);
x_7 = x_66;
x_8 = x_65;
goto block_58;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_dec(x_59);
x_68 = lean_unbox(x_60);
lean_dec(x_60);
x_7 = x_68;
x_8 = x_67;
goto block_58;
}
block_58:
{
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_instInhabitedSimpTheorems;
x_14 = l_Lean_ScopedEnvExtension_getState___rarg(x_13, x_1, x_12);
lean_dec(x_12);
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_16);
lean_inc(x_5);
x_18 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(x_14, x_17, x_4, x_5, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_5, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 4);
lean_dec(x_26);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__2___boxed), 2, 1);
lean_closure_set(x_27, 0, x_19);
x_28 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_1, x_25, x_27);
x_29 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
lean_ctor_set(x_22, 4, x_29);
lean_ctor_set(x_22, 0, x_28);
x_30 = lean_st_ref_set(x_5, x_22, x_23);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
x_39 = lean_ctor_get(x_22, 2);
x_40 = lean_ctor_get(x_22, 3);
x_41 = lean_ctor_get(x_22, 5);
x_42 = lean_ctor_get(x_22, 6);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__2___boxed), 2, 1);
lean_closure_set(x_43, 0, x_19);
x_44 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_1, x_37, x_43);
x_45 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
x_46 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_41);
lean_ctor_set(x_46, 6, x_42);
x_47 = lean_st_ref_set(x_5, x_46, x_23);
lean_dec(x_5);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_18);
if (x_52 == 0)
{
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_2);
x_57 = l_Lean_Attribute_erase(x_3, x_56, x_4, x_5, x_8);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = 1;
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__1___boxed), 8, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__3___boxed), 6, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Lean_registerBuiltinAttribute(x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_1, x_14, x_15, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Meta_mkSimpAttr___lambda__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_mkSimpAttr___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkSimpAttr___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_647_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__29;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_8 = lean_hashmap_mk_idx(x_6, x_7);
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
x_17 = lean_hashmap_mk_idx(x_15, x_16);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_registerSimpAttr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Meta_registerSimpAttr___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_1, x_2, x_8);
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
x_15 = l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_registerSimpAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(x_2, x_10);
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
x_18 = l_Lean_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(x_13, x_15);
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
x_19 = l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_2, x_3, x_10);
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
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(x_2, x_26);
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
x_34 = l_Lean_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(x_29, x_31);
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
x_36 = l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Meta_registerSimpAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtensionMapRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_mkSimpExt(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkSimpAttr(x_1, x_2, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_registerSimpAttr___closed__1;
x_11 = lean_st_ref_take(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
x_14 = l_Lean_HashMap_insert___at_Lean_Meta_registerSimpAttr___spec__1(x_12, x_1, x_6);
x_15 = lean_st_ref_set(x_10, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpExtension", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simplification theorem", 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__6;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__5;
x_5 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("seval", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sevalSimpExtension", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("symbolic evaluator theorem", 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__4;
x_5 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_getSimpTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_getSimpTheorems___closed__1;
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpTheorems(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_getSEvalTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_sevalSimpExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_getSEvalTheorems___closed__1;
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSEvalTheorems(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
return x_6;
}
}
static uint32_t _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Meta_getSimpTheorems___closed__1;
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_4, x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
x_12 = lean_array_push(x_11, x_6);
x_13 = lean_box(0);
x_14 = 0;
x_15 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
x_16 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_17 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set_uint32(x_17, sizeof(void*)*4, x_16);
lean_ctor_set_uint32(x_17, sizeof(void*)*4 + 4, x_14);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
x_21 = lean_array_push(x_20, x_6);
x_22 = lean_box(0);
x_23 = 0;
x_24 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
x_25 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_26 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint32(x_26, sizeof(void*)*4, x_25);
lean_ctor_set_uint32(x_26, sizeof(void*)*4 + 4, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Context_mkDefault___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Context_mkDefault(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__1);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__2);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__3);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__4 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__4();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__4);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__5 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__5();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__5);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__6);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__7 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__7();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__7);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__8 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__8();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__8);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__9 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__9();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__9);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__10 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__10();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__10);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__11 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__11();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__11);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__12 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__12();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__12);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__13 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__13();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__13);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__14 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__14();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__14);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__15 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__15();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__15);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__16 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__16();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__16);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__17 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__17();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__17);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__18 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__18();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__18);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__19 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__19();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__19);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__20 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__20();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__20);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__21 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__21();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__21);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__22 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__22();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__22);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__23 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__23();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__23);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__24 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__24();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__24);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__25 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__25();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__25);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__26 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__26();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__26);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__27 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__27();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__27);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__28 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__28();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__28);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__29 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__29();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8____closed__29);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_8_);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__7 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__7();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__7);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__8 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__8();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__8);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__9 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__9();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__9);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__10 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__10();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__10);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__11 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__11();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__11);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__12 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__12();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__12);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__13 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__13();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__13);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__14 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__14();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__14);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__15 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__15();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__15);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__16 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__16();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__16);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__17 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__17();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__17);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__18 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__18();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__18);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__19);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__1 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__1);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__3 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__3);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__1 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__1);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__2 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__2);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__3 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__3);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__4 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__4);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__5 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__5);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__6 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__6);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__7 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__7);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__8 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__8);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__9 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__9);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__10 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__10);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__11 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__11);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__12 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__12);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__13 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__13);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__14 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__14);
l_Lean_Meta_mkSimpAttr___lambda__1___closed__15 = _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__1___closed__15);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_647_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_647_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_647_);
l_Lean_Meta_registerSimpAttr___closed__1 = _init_l_Lean_Meta_registerSimpAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_registerSimpAttr___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_747_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtension);
lean_dec_ref(res);
}l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_773_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_sevalSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_sevalSimpExtension);
lean_dec_ref(res);
}l_Lean_Meta_getSimpTheorems___closed__1 = _init_l_Lean_Meta_getSimpTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_getSimpTheorems___closed__1);
l_Lean_Meta_getSEvalTheorems___closed__1 = _init_l_Lean_Meta_getSEvalTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_getSEvalTheorems___closed__1);
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1);
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2();
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
