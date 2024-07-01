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
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689_(lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__4;
lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_ofNatTruncate(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_registerSimpAttr___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__8;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__8;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__6;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__16;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__13;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__13;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2;
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__22;
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4;
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__25;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__5(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3;
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_sevalSimpExtension;
static lean_object* l_Lean_Meta_getSimpTheorems___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__14;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__28;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__7;
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object*, lean_object*);
static uint32_t l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__11;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__21;
static lean_object* l_Lean_Meta_getSEvalTheorems___closed__1;
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerSimpAttr___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__27;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__4;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__20;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__19;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__26;
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__3;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29;
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717_(lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__6;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__18;
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__23;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__15;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__4;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__17;
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__4;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__24;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__2;
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__10;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__9;
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Parser_Tactic_Doc_initFn____x40_Lean_Parser_Tactic_Doc___hyg_831____spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_619_;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___closed__1;
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
extern lean_object* l_Lean_Meta_simpExtensionMapRef;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__3;
static lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_registerSimpAttr___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__15;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__16;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__18;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__17;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__20;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__14;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__12;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__22;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__23;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__10;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__24;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__25;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__8;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__26;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__27;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__5;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__28;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 6);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_ref_take(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 4);
lean_dec(x_15);
x_16 = l_Lean_ScopedEnvExtension_addCore___rarg(x_14, x_1, x_2, x_3, x_9);
x_17 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
lean_ctor_set(x_11, 4, x_17);
lean_ctor_set(x_11, 0, x_16);
x_18 = lean_st_ref_set(x_7, x_11, x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_5, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
x_39 = lean_st_ref_set(x_5, x_38, x_22);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
x_46 = lean_ctor_get(x_11, 2);
x_47 = lean_ctor_get(x_11, 3);
x_48 = lean_ctor_get(x_11, 5);
x_49 = lean_ctor_get(x_11, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_50 = l_Lean_ScopedEnvExtension_addCore___rarg(x_44, x_1, x_2, x_3, x_9);
x_51 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_49);
x_53 = lean_st_ref_set(x_7, x_52, x_12);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_take(x_5, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 4);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
x_63 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 5, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_60);
lean_ctor_set(x_64, 4, x_61);
x_65 = lean_st_ref_set(x_5, x_64, x_57);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
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
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_7 = l_Lean_logAt___at_Lean_Parser_Tactic_Doc_initFn____x40_Lean_Parser_Tactic_Doc___hyg_831____spec__1(x_6, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1;
x_7 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5(x_1, x_8, x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 2;
x_11 = l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5(x_1, x_10, x_2, x_3, x_4);
return x_11;
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
x_1 = lean_mk_string_unchecked("'", 1, 1);
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
x_1 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
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
lean_object* x_6; uint8_t x_18; 
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_18 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
x_6 = x_20;
goto block_17;
}
else
{
uint8_t x_21; 
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_inc(x_1);
x_23 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 5);
lean_inc(x_24);
x_25 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_24, x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_6 = x_26;
goto block_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_27, x_3, x_4, x_5);
lean_dec(x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_29, x_3, x_4, x_5);
lean_dec(x_3);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = lean_box(0);
x_6 = x_31;
goto block_17;
}
}
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_6 = x_32;
goto block_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_33, x_3, x_4, x_5);
lean_dec(x_3);
return x_34;
}
block_17:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_7 = l_Lean_Meta_Origin_key(x_2);
x_8 = l_Lean_MessageData_ofName(x_7);
x_9 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_3);
x_13 = l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4(x_12, x_3, x_4, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_14, x_3, x_4, x_15);
lean_dec(x_3);
lean_dec(x_14);
return x_16;
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
x_5 = lean_alloc_ctor(0, 0, 13);
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
lean_ctor_set_uint8(x_5, 12, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__3;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__2;
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
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__1;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__5;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__7;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__4;
x_5 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__8;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'simp', it is not a proposition nor a definition (to unfold)", 68, 68);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpPost", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_3);
x_149 = l_Lean_Meta_Simp_isSimproc(x_3, x_6, x_7, x_8);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_150);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = l_Lean_Meta_Simp_isBuiltinSimproc(x_3, x_6, x_7, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_unbox(x_154);
lean_dec(x_154);
x_9 = x_156;
x_10 = x_155;
goto block_148;
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_149, 1);
lean_inc(x_157);
lean_dec(x_149);
x_158 = lean_unbox(x_150);
lean_dec(x_150);
x_9 = x_158;
x_10 = x_157;
goto block_148;
}
block_148:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_11 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__9;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_26 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__6;
lean_inc(x_3);
x_27 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_26, x_13, x_6, x_7, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_118 = lean_unsigned_to_nat(1u);
x_119 = l_Lean_Syntax_getArg(x_4, x_118);
x_120 = l_Lean_Syntax_isNone(x_119);
x_121 = lean_unsigned_to_nat(2u);
x_122 = l_Lean_Syntax_getArg(x_4, x_121);
lean_dec(x_4);
lean_inc(x_6);
x_123 = l_Lean_getAttrParamOptPrio(x_122, x_6, x_7, x_29);
lean_dec(x_122);
if (x_120 == 0)
{
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lean_Syntax_getArg(x_119, x_126);
lean_dec(x_119);
x_128 = l_Lean_Syntax_getKind(x_127);
x_129 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__13;
x_130 = lean_name_eq(x_128, x_129);
lean_dec(x_128);
x_30 = x_130;
x_31 = x_124;
x_32 = x_125;
goto block_117;
}
else
{
uint8_t x_131; 
lean_dec(x_119);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_123);
if (x_131 == 0)
{
return x_123;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_123, 0);
x_133 = lean_ctor_get(x_123, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_123);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_dec(x_119);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_123, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_123, 1);
lean_inc(x_136);
lean_dec(x_123);
x_137 = 1;
x_30 = x_137;
x_31 = x_135;
x_32 = x_136;
goto block_117;
}
else
{
uint8_t x_138; 
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_123);
if (x_138 == 0)
{
return x_123;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_123, 0);
x_140 = lean_ctor_get(x_123, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_123);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
block_117:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_ConstantInfo_type(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_34 = l_Lean_Meta_isProp(x_33, x_26, x_13, x_6, x_7, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_ConstantInfo_hasValue(x_28);
lean_dec(x_28);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_39 = l_Lean_Meta_mkSimpAttr___lambda__1___closed__11;
x_40 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_39, x_26, x_13, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_13);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; 
x_45 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_3);
x_46 = l_Lean_Meta_getEqnsFor_x3f(x_3, x_45, x_26, x_13, x_6, x_7, x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_31);
lean_dec(x_15);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_3);
x_50 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_49, x_5, x_26, x_13, x_6, x_7, x_48);
lean_dec(x_7);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_16 = x_51;
x_17 = x_52;
goto block_25;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_array_get_size(x_55);
x_57 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_58 = 0;
x_59 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_1);
x_60 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_1, x_5, x_30, x_31, x_55, x_57, x_58, x_59, x_26, x_13, x_6, x_7, x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_3);
if (lean_is_scalar(x_15)) {
 x_62 = lean_alloc_ctor(2, 2, 0);
} else {
 x_62 = x_15;
 lean_ctor_set_tag(x_62, 2);
}
lean_ctor_set(x_62, 0, x_3);
lean_ctor_set(x_62, 1, x_55);
lean_inc(x_6);
lean_inc(x_1);
x_63 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_62, x_5, x_26, x_13, x_6, x_7, x_61);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_7, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_3);
x_69 = l_Lean_Meta_hasSmartUnfoldingDecl(x_68, x_3);
if (x_69 == 0)
{
lean_free_object(x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_16 = x_59;
x_17 = x_67;
goto block_25;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_ctor_set(x_47, 0, x_3);
x_70 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_47, x_5, x_26, x_13, x_6, x_7, x_67);
lean_dec(x_7);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_16 = x_71;
x_17 = x_72;
goto block_25;
}
}
else
{
uint8_t x_73; 
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
return x_60;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_60);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_47, 0);
lean_inc(x_77);
lean_dec(x_47);
x_78 = lean_array_get_size(x_77);
x_79 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_80 = 0;
x_81 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_1);
x_82 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_1, x_5, x_30, x_31, x_77, x_79, x_80, x_81, x_26, x_13, x_6, x_7, x_53);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
lean_inc(x_3);
if (lean_is_scalar(x_15)) {
 x_84 = lean_alloc_ctor(2, 2, 0);
} else {
 x_84 = x_15;
 lean_ctor_set_tag(x_84, 2);
}
lean_ctor_set(x_84, 0, x_3);
lean_ctor_set(x_84, 1, x_77);
lean_inc(x_6);
lean_inc(x_1);
x_85 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_84, x_5, x_26, x_13, x_6, x_7, x_83);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_st_ref_get(x_7, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_3);
x_91 = l_Lean_Meta_hasSmartUnfoldingDecl(x_90, x_3);
if (x_91 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_16 = x_81;
x_17 = x_89;
goto block_25;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_3);
x_93 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_1, x_92, x_5, x_26, x_13, x_6, x_7, x_89);
lean_dec(x_7);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_16 = x_94;
x_17 = x_95;
goto block_25;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_77);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_ctor_get(x_82, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_98 = x_82;
} else {
 lean_dec_ref(x_82);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_46);
if (x_100 == 0)
{
return x_46;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_46, 0);
x_102 = lean_ctor_get(x_46, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_46);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; 
lean_dec(x_28);
lean_dec(x_15);
x_104 = lean_ctor_get(x_34, 1);
lean_inc(x_104);
lean_dec(x_34);
x_105 = 0;
lean_inc(x_13);
x_106 = l_Lean_Meta_addSimpTheorem(x_1, x_3, x_30, x_105, x_5, x_31, x_26, x_13, x_6, x_7, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_16 = x_107;
x_17 = x_108;
goto block_25;
}
else
{
uint8_t x_109; 
lean_dec(x_13);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_34);
if (x_113 == 0)
{
return x_34;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_34, 0);
x_115 = lean_ctor_get(x_34, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_34);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_27);
if (x_142 == 0)
{
return x_27;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_27, 0);
x_144 = lean_ctor_get(x_27, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_27);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
block_25:
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_16);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_1);
x_146 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_2);
x_147 = l_Lean_Attribute_add(x_3, x_146, x_4, x_5, x_6, x_7, x_10);
return x_147;
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
uint8_t x_7; lean_object* x_8; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_inc(x_3);
x_55 = l_Lean_Meta_Simp_isSimproc(x_3, x_4, x_5, x_6);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_Lean_Meta_Simp_isBuiltinSimproc(x_3, x_4, x_5, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unbox(x_60);
lean_dec(x_60);
x_7 = x_62;
x_8 = x_61;
goto block_54;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_unbox(x_56);
lean_dec(x_56);
x_7 = x_64;
x_8 = x_63;
goto block_54;
}
block_54:
{
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
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
x_18 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(x_14, x_17, x_4, x_5, x_11);
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
x_29 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
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
x_45 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
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
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_2);
x_53 = l_Lean_Attribute_erase(x_3, x_52, x_4, x_5, x_8);
return x_53;
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
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
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
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_619_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_6, x_9, x_19);
x_21 = l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_2, x_3, x_10);
x_22 = lean_array_uset(x_20, x_9, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Name_hash___override(x_2);
lean_inc(x_25);
x_27 = lean_hashmap_mk_idx(x_25, x_26);
x_28 = lean_array_uget(x_24, x_27);
x_29 = l_Lean_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__2(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_23, x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_24, x_27, x_32);
x_34 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_25);
lean_dec(x_25);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_HashMapImp_expand___at_Lean_Meta_registerSimpAttr___spec__3(x_31, x_33);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
x_38 = lean_box(0);
x_39 = lean_array_uset(x_24, x_27, x_38);
x_40 = l_Lean_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__6(x_2, x_3, x_28);
x_41 = lean_array_uset(x_39, x_27, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpExtension", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simplification theorem", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__6;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__5;
x_5 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seval", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sevalSimpExtension", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("symbolic evaluator theorem", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__4;
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
x_6 = lean_alloc_ctor(0, 2, 19);
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
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
x_12 = lean_array_push(x_11, x_6);
x_13 = lean_box(0);
x_14 = 0;
x_15 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
x_16 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set_uint32(x_19, sizeof(void*)*5, x_16);
lean_ctor_set_uint32(x_19, sizeof(void*)*5 + 4, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*5 + 8, x_18);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
x_23 = lean_array_push(x_22, x_6);
x_24 = lean_box(0);
x_25 = 0;
x_26 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
x_27 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_28 = lean_unsigned_to_nat(0u);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_28);
lean_ctor_set_uint32(x_30, sizeof(void*)*5, x_27);
lean_ctor_set_uint32(x_30, sizeof(void*)*5 + 4, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 8, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
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
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__4 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__4();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__4);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__5 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__5();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__5);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__7 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__7();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__7);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__8 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__8();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__8);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__9 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__9();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__9);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__10 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__10();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__10);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__12 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__12();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__12);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__13 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__13();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__13);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__14 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__14();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__14);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__15 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__15();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__15);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__16 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__16();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__16);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__17 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__17();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__17);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__18 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__18();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__18);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__19 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__19();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__19);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__20 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__20();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__20);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__21 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__21();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__21);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__22 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__22();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__22);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__23 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__23();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__23);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__24 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__24();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__24);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__25 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__25();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__25);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__26 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__26();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__26);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__27 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__27();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__27);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__28 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__28();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__28);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_);
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
l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1 = _init_l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1();
lean_mark_persistent(l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1);
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
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_619_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_619_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_619_);
l_Lean_Meta_registerSimpAttr___closed__1 = _init_l_Lean_Meta_registerSimpAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_registerSimpAttr___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_689_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtension);
lean_dec_ref(res);
}l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_717_(lean_io_mk_world());
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
