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
lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__3;
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__2;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__8;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__2;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__16;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__14;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__4;
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__2;
lean_object* l_Lean_logAt___at_Lean_Parser_Tactic_Doc_initFn____x40_Lean_Parser_Tactic_Doc___hyg_822____spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__3;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__6;
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__13;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__22;
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__16;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getSEvalTheorems___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__25;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__12;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888_(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_sevalSimpExtension;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getSimpTheorems___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__14;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862_(lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__17;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_793_;
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__21;
static lean_object* l_Lean_Meta_getSEvalTheorems___closed__1;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__18;
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerSimpAttr___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__27;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__9;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__20;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__12;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__26;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__11;
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29;
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9_;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__8;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__18;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__15;
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__23;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__15;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__4;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__17;
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__24;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__6;
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__10;
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__7;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__4;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_converse(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
extern lean_object* l_Lean_Meta_simpExtensionMapRef;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_registerSimpAttr___spec__2(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__3;
static lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___closed__13;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_registerSimpAttr___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_mkSimpAttr___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__6;
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
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
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5() {
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
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__4;
x_2 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__5;
x_4 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_3);
lean_ctor_set(x_4, 6, x_3);
return x_4;
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
x_25 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6;
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
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6;
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
x_63 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_10);
x_18 = lean_array_uget(x_7, x_9);
x_19 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_1);
x_20 = l_Lean_Meta_addSimpTheorem(x_1, x_18, x_3, x_19, x_2, x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_9, x_22);
x_24 = lean_box(0);
x_9 = x_23;
x_10 = x_24;
x_15 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
x_7 = l_Lean_logAt___at_Lean_Parser_Tactic_Doc_initFn____x40_Lean_Parser_Tactic_Doc___hyg_822____spec__1(x_6, x_1, x_2, x_3, x_4, x_5);
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
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Meta_Origin_key(x_1);
x_8 = l_Lean_MessageData_ofName(x_7);
x_9 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4(x_12, x_4, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_Origin_converse(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_2);
x_11 = l_Lean_Meta_SimpTheorems_isLemma(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1(x_1, x_2, x_12, x_4, x_5, x_6);
lean_dec(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_14 = l_Lean_Meta_SimpTheorems_eraseCore(x_2, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_1);
x_6 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_6 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
x_10 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_9, x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__2(x_2, x_1, x_11, x_3, x_4, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_3);
x_15 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__2(x_2, x_1, x_17, x_3, x_4, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_12 = l_Lean_Meta_SimpTheorems_ignoreEquations(x_1, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_18 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_12);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_21, x_3, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_box(0);
x_27 = lean_array_size(x_25);
x_28 = 0;
x_29 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_30 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_2, x_3, x_4, x_5, x_25, x_26, x_25, x_27, x_28, x_29, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_1);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_1);
lean_inc(x_9);
lean_inc(x_2);
x_32 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_12, x_3, x_7, x_8, x_9, x_10, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_34 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(x_1, x_9, x_10, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_free_object(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
lean_ctor_set(x_34, 0, x_29);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
lean_ctor_set(x_19, 0, x_1);
x_42 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_19, x_3, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_19);
lean_dec(x_25);
lean_free_object(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_30);
if (x_47 == 0)
{
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_30, 0);
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_30);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_51);
lean_dec(x_19);
x_52 = lean_box(0);
x_53 = lean_array_size(x_51);
x_54 = 0;
x_55 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_2, x_3, x_4, x_5, x_51, x_52, x_51, x_53, x_54, x_55, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_1);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_51);
lean_ctor_set(x_12, 0, x_1);
lean_inc(x_9);
lean_inc(x_2);
x_58 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_12, x_3, x_7, x_8, x_9, x_10, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_60 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(x_1, x_9, x_10, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_1);
x_68 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_67, x_3, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_71 = x_60;
} else {
 lean_dec_ref(x_60);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_51);
lean_free_object(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_75 = x_56;
} else {
 lean_dec_ref(x_56);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_free_object(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_18);
if (x_77 == 0)
{
return x_18;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_18, 0);
x_79 = lean_ctor_get(x_18, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_18);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_12, 1);
lean_inc(x_81);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_82 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_7, x_8, x_9, x_10, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_5);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_1);
x_86 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_85, x_3, x_7, x_8, x_9, x_10, x_84);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec(x_82);
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_89 = x_83;
} else {
 lean_dec_ref(x_83);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
x_91 = lean_array_size(x_88);
x_92 = 0;
x_93 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_94 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_2, x_3, x_4, x_5, x_88, x_90, x_88, x_91, x_92, x_93, x_7, x_8, x_9, x_10, x_87);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_inc(x_1);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_88);
lean_inc(x_9);
lean_inc(x_2);
x_97 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_96, x_3, x_7, x_8, x_9, x_10, x_95);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_99 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(x_1, x_9, x_10, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
if (lean_is_scalar(x_89)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_89;
}
lean_ctor_set(x_106, 0, x_1);
x_107 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_106, x_3, x_7, x_8, x_9, x_10, x_105);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_99, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_110 = x_99;
} else {
 lean_dec_ref(x_99);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_ctor_get(x_94, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_94, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_114 = x_94;
} else {
 lean_dec_ref(x_94);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_82, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_82, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_118 = x_82;
} else {
 lean_dec_ref(x_82);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_5);
x_120 = lean_ctor_get(x_12, 1);
lean_inc(x_120);
lean_dec(x_12);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_1);
x_122 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_121, x_3, x_7, x_8, x_9, x_10, x_120);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_122;
}
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__1() {
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
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__3;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__2;
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
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__2;
x_2 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__1;
x_3 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__5;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__6;
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
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__8() {
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
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__9() {
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
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__8;
x_3 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__4;
x_5 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__9;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'simp', it is not a proposition nor a definition (to unfold)", 68, 68);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid '←' modifier, '", 25, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is a declaration name to be unfolded", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpPost", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__3;
x_4 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__17;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_inc(x_3);
x_114 = l_Lean_Meta_Simp_isSimproc(x_3, x_6, x_7, x_8);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_115);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_Lean_Meta_Simp_isBuiltinSimproc(x_3, x_6, x_7, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_unbox(x_119);
lean_dec(x_119);
x_9 = x_121;
x_10 = x_120;
goto block_113;
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
lean_dec(x_114);
x_123 = lean_unbox(x_115);
lean_dec(x_115);
x_9 = x_123;
x_10 = x_122;
goto block_113;
}
block_113:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_11 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__10;
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
x_16 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__7;
lean_inc(x_3);
x_17 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_3, x_16, x_13, x_6, x_7, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_4, x_20);
x_22 = l_Lean_Syntax_isNone(x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_4, x_23);
x_25 = l_Lean_Syntax_isNone(x_24);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Syntax_getArg(x_4, x_26);
lean_dec(x_4);
lean_inc(x_6);
x_28 = l_Lean_getAttrParamOptPrio(x_27, x_6, x_7, x_19);
lean_dec(x_27);
if (x_22 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Lean_Syntax_getArg(x_21, x_101);
lean_dec(x_21);
x_103 = l_Lean_Syntax_getKind(x_102);
x_104 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__18;
x_105 = lean_name_eq(x_103, x_104);
lean_dec(x_103);
x_29 = x_105;
goto block_100;
}
else
{
uint8_t x_106; 
lean_dec(x_21);
x_106 = 1;
x_29 = x_106;
goto block_100;
}
block_100:
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
if (x_25 == 0)
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_28, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_28, 1);
lean_inc(x_87);
lean_dec(x_28);
x_88 = 1;
x_30 = x_88;
x_31 = x_86;
x_32 = x_87;
goto block_85;
}
else
{
uint8_t x_89; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_28);
if (x_89 == 0)
{
return x_28;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_28, 0);
x_91 = lean_ctor_get(x_28, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_28);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_28, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_28, 1);
lean_inc(x_94);
lean_dec(x_28);
x_95 = 0;
x_30 = x_95;
x_31 = x_93;
x_32 = x_94;
goto block_85;
}
else
{
uint8_t x_96; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_28);
if (x_96 == 0)
{
return x_28;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_28, 0);
x_98 = lean_ctor_get(x_28, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_28);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
block_85:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_ConstantInfo_type(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_34 = l_Lean_Meta_isProp(x_33, x_16, x_13, x_6, x_7, x_32);
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
x_38 = l_Lean_ConstantInfo_hasValue(x_18);
lean_dec(x_18);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_39 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__12;
x_40 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_39, x_16, x_13, x_6, x_7, x_37);
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
if (x_30 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_15);
x_45 = lean_box(0);
lean_inc(x_13);
x_46 = l_Lean_Meta_mkSimpAttr___lambda__1(x_3, x_1, x_5, x_29, x_31, x_45, x_16, x_13, x_6, x_7, x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_get(x_13, x_47);
lean_dec(x_13);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_45);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_13);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_31);
lean_dec(x_1);
x_57 = l_Lean_MessageData_ofName(x_3);
x_58 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__14;
if (lean_is_scalar(x_15)) {
 x_59 = lean_alloc_ctor(7, 2, 0);
} else {
 x_59 = x_15;
 lean_ctor_set_tag(x_59, 7);
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Meta_mkSimpAttr___lambda__2___closed__16;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_61, x_16, x_13, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_13);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_18);
lean_dec(x_15);
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
lean_dec(x_34);
lean_inc(x_13);
x_68 = l_Lean_Meta_addSimpTheorem(x_1, x_3, x_29, x_30, x_5, x_31, x_16, x_13, x_6, x_7, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_get(x_13, x_69);
lean_dec(x_13);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_13);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
return x_68;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_68, 0);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_68);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_34);
if (x_81 == 0)
{
return x_34;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_34, 0);
x_83 = lean_ctor_get(x_34, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_34);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_17);
if (x_107 == 0)
{
return x_17;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_17, 0);
x_109 = lean_ctor_get(x_17, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_17);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_2);
x_112 = l_Lean_Attribute_add(x_3, x_111, x_4, x_5, x_6, x_7, x_10);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__3___boxed), 2, 1);
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
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__3___boxed), 2, 1);
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
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__2___boxed), 8, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpAttr___lambda__4___boxed), 6, 2);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_mkSimpAttr___spec__2(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_20;
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
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_mkSimpAttr___lambda__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Meta_mkSimpAttr___lambda__2(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_mkSimpAttr___lambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpAttr___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkSimpAttr___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_793_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__29;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Name_hash___override(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_registerSimpAttr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_registerSimpAttr___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_registerSimpAttr___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_registerSimpAttr___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__5(x_1, x_2, x_8);
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
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__5(x_1, x_2, x_13);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
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
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Name_hash___override(x_1);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_16, x_29);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__1(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_15, x_32);
lean_dec(x_15);
lean_inc(x_6);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_30);
x_35 = lean_array_uset(x_16, x_29, x_34);
x_36 = lean_unsigned_to_nat(4u);
x_37 = lean_nat_mul(x_33, x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_div(x_37, x_38);
lean_dec(x_37);
x_40 = lean_array_get_size(x_35);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_registerSimpAttr___spec__2(x_35);
lean_ctor_set(x_12, 1, x_42);
lean_ctor_set(x_12, 0, x_33);
x_43 = lean_st_ref_set(x_10, x_12, x_13);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_6);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_ctor_set(x_12, 1, x_35);
lean_ctor_set(x_12, 0, x_33);
x_48 = lean_st_ref_set(x_10, x_12, x_13);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_6);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_box(0);
x_54 = lean_array_uset(x_16, x_29, x_53);
lean_inc(x_6);
x_55 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__5(x_1, x_6, x_30);
x_56 = lean_array_uset(x_54, x_29, x_55);
lean_ctor_set(x_12, 1, x_56);
x_57 = lean_st_ref_set(x_10, x_12, x_13);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_6);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
x_64 = lean_array_get_size(x_63);
x_65 = l_Lean_Name_hash___override(x_1);
x_66 = 32;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = 16;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = lean_uint64_to_usize(x_71);
x_73 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_74 = 1;
x_75 = lean_usize_sub(x_73, x_74);
x_76 = lean_usize_land(x_72, x_75);
x_77 = lean_array_uget(x_63, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__1(x_1, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_62, x_79);
lean_dec(x_62);
lean_inc(x_6);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_6);
lean_ctor_set(x_81, 2, x_77);
x_82 = lean_array_uset(x_63, x_76, x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_mul(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_registerSimpAttr___spec__2(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_st_ref_set(x_10, x_90, x_13);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_6);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_80);
lean_ctor_set(x_95, 1, x_82);
x_96 = lean_st_ref_set(x_10, x_95, x_13);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_6);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_63, x_76, x_100);
lean_inc(x_6);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_registerSimpAttr___spec__5(x_1, x_6, x_77);
x_103 = lean_array_uset(x_101, x_76, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_62);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_st_ref_set(x_10, x_104, x_13);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_6);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_6);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_8);
if (x_109 == 0)
{
return x_8;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_8, 0);
x_111 = lean_ctor_get(x_8, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_8);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_5);
if (x_113 == 0)
{
return x_5;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_5, 0);
x_115 = lean_ctor_get(x_5, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_5);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_registerSimpAttr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpExtension", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simplification theorem", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__6;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__5;
x_5 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seval", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sevalSimpExtension", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_9____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("symbolic evaluator theorem", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__4;
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
static lean_object* _init_l_Lean_Meta_Simp_Context_mkDefault___closed__1() {
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
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_Lean_Meta_getSimpTheorems___closed__1;
x_7 = l_Lean_Meta_SimpExtension_getTheorems(x_6, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_8);
x_15 = lean_array_mk(x_10);
x_16 = l_Lean_Meta_Simp_Context_mkDefault___closed__1;
x_17 = l_Lean_Meta_Simp_mkContext(x_16, x_15, x_12, x_1, x_2, x_3, x_4, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
x_23 = l_Lean_Meta_Simp_Context_mkDefault___closed__1;
x_24 = l_Lean_Meta_Simp_mkContext(x_23, x_22, x_18, x_1, x_2, x_3, x_4, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_Context_mkDefault(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1___closed__6);
l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1 = _init_l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1();
lean_mark_persistent(l_Lean_logWarning___at_Lean_Meta_mkSimpAttr___spec__4___closed__1);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__1 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__1);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__2 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__2);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__3 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__3);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__4 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Meta_mkSimpAttr___spec__3___lambda__1___closed__4);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__1 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__1);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__2 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__2);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__3 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__3);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__4 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__4);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__5 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__5);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__6 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__6);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__7 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__7);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__8 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__8);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__9 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__9);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__10 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__10);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__11 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__11);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__12 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__12);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__13 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__13);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__14 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__14);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__15 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__15);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__16 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__16();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__16);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__17 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__17();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__17);
l_Lean_Meta_mkSimpAttr___lambda__2___closed__18 = _init_l_Lean_Meta_mkSimpAttr___lambda__2___closed__18();
lean_mark_persistent(l_Lean_Meta_mkSimpAttr___lambda__2___closed__18);
l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_793_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_793_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Attr___hyg_793_);
l_Lean_Meta_registerSimpAttr___closed__1 = _init_l_Lean_Meta_registerSimpAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_registerSimpAttr___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_862_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtension);
lean_dec_ref(res);
}l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_Attr___hyg_888_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_sevalSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_sevalSimpExtension);
lean_dec_ref(res);
}l_Lean_Meta_getSimpTheorems___closed__1 = _init_l_Lean_Meta_getSimpTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_getSimpTheorems___closed__1);
l_Lean_Meta_getSEvalTheorems___closed__1 = _init_l_Lean_Meta_getSEvalTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_getSEvalTheorems___closed__1);
l_Lean_Meta_Simp_Context_mkDefault___closed__1 = _init_l_Lean_Meta_Simp_Context_mkDefault___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_mkDefault___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
