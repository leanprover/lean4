// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Simproc
// Imports: Lean.ScopedEnvExtension Lean.Compiler.InitAttr Lean.Meta.DiscrTree Lean.Meta.Tactic.Simp.Types
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
static lean_object* l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocArrayCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__7___boxed(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__12;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5;
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerSimprocAttr___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__6;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__4;
static lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
static lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__17;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getDtConfig(lean_object*);
static lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1;
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__11;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__1;
lean_object* l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__6;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__10;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerSimprocAttr___spec__4(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__3;
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocArrayCore___spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3___boxed(lean_object**);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_ExtensionState_declNames___default___spec__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__2;
static lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__5;
static lean_object* l_Lean_Meta_Simp_userPreSimprocs___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1;
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774_;
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__5;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___closed__3;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_SimprocsArray_isErased___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__4;
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__2(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__20;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocDecl_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__6;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__2;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocs;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__7;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__3;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__13;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Simp_Simprocs_addCore___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Simp_Simprocs_addCore___spec__10(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocArrayCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__7;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__2(lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSimprocsRef;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_BuiltinSimprocs_procs___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocArrayCore___spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__16;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqSimprocEntry(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__4;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__5;
static lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__10;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__13;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__21;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__23;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__5;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_realizeGlobalConstCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TransformStep_toStep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__1;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_isErased___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__7;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__12;
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1182_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__5;
static lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__2(lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6090_;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__2;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__8;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__4;
lean_object* l_Lean_ScopedEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__13;
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__8;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__2;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerSimprocAttr___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_getSimprocs___rarg___closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__8;
static lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_60_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerSimprocAttr___spec__2(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_Simprocs_addCore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_BuiltinSimprocs_keys___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl;
static lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_SimprocsArray_isErased___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16;
static lean_object* l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__22;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__2;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
static lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6046_(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189_(lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__19;
static lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__9;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__3;
lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__1;
static lean_object* l_Lean_Meta_Simp_registerSimprocAttr___closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__8;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__4;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__6;
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocExtensionCore_x3f___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__2___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__26;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_Simprocs_addCore___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_Simprocs_addCore___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__4;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocsArray_isErased(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSimprocDeclsRef;
static lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__3;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__4;
static lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__4;
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_Simprocs_addCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__25;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192_(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocExtensionCore_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1(lean_object*);
lean_object* l_Array_insertAt_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__14;
lean_object* l_Lean_ScopedEnvExtension_addCore___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__7;
static lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___boxed(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439_(lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocDecl_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1;
static lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__2;
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__15;
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Simp_Simprocs_addCore___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__5(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__18;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_SimprocsArray_erase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocExtensionMapRef;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__1(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Simp_dsimprocCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_SimprocsArray_erase___spec__1(lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__11;
static lean_object* l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3;
static lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__9;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146_(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocSEvalExtension;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__2;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655_(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSEvalprocsRef;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_Simprocs_addCore___spec__5(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__2(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerSimprocAttr___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__11;
lean_object* l_Lean_Meta_Simp_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerSimprocAttr___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___closed__1;
static lean_object* l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__2;
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__6;
lean_object* l_Lean_throwError___at___private_Lean_ReducibilityAttrs_0__Lean_validate___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__14;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__1;
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__3(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocDeclExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___closed__2;
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocExtension;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__6;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_BuiltinSimprocs_procs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_60_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs___closed__1;
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3;
x_2 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocDecl_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocDecl_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_SimprocDecl_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__4(x_1, x_83, x_4, x_5);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__4(x_96, x_97, x_4, x_5);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_SimprocDecl_lt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
lean_ctor_set(x_1, 1, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
x_10 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
lean_ctor_set(x_7, 1, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__1(x_4, x_5, x_6);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__1(x_9, x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__5), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__2;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_3, x_2, x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6(x_5, x_9, x_8);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocDeclExt", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__2), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__6;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__7;
x_3 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__4), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__7___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__5;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__8;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__9;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__10;
x_5 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__11;
x_6 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__12;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__13;
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_name_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__4(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__3(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_nat_add(x_4, x_5);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
lean_inc(x_3);
x_11 = lean_array_get(x_3, x_2, x_10);
x_12 = l_Lean_Meta_Simp_SimprocDecl_lt(x_11, x_3);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_5);
x_13 = l_Lean_Meta_Simp_SimprocDecl_lt(x_3, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_10, x_17);
lean_dec(x_10);
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_4);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_10, x_21);
lean_dec(x_10);
x_4 = x_22;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_simprocDeclExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_8 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_9 = l_Lean_PersistentEnvExtension_getState___rarg(x_7, x_8, x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_array_get_size(x_12);
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_sub(x_23, x_24);
x_26 = lean_usize_land(x_22, x_25);
x_27 = lean_array_uget(x_12, x_26);
lean_dec(x_12);
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1(x_2, x_27);
lean_dec(x_27);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_array_get_size(x_29);
x_31 = l_Lean_Name_hash___override(x_2);
x_32 = 32;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = 16;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_40 = 1;
x_41 = lean_usize_sub(x_39, x_40);
x_42 = lean_usize_land(x_38, x_41);
x_43 = lean_array_uget(x_29, x_42);
lean_dec(x_29);
x_44 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1(x_2, x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_6);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
lean_dec(x_3);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Environment_getModuleIdxFor_x3f(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_5);
x_11 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_12 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_13 = l_Lean_PersistentEnvExtension_getState___rarg(x_11, x_12, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__2(x_14, x_1);
x_16 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_9, x_1, x_15, x_2, x_3, x_8);
lean_dec(x_1);
lean_dec(x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_19 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_20 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_18, x_19, x_9, x_17);
lean_dec(x_17);
x_21 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_1);
x_22 = lean_array_get_size(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_22);
lean_dec(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_9, x_1, x_27, x_2, x_3, x_8);
lean_dec(x_1);
lean_dec(x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l_Array_binSearchAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__5(x_29, x_20, x_5, x_25, x_24);
lean_dec(x_20);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_9, x_1, x_29, x_2, x_3, x_8);
lean_dec(x_1);
lean_dec(x_9);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_34);
x_35 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_9, x_1, x_30, x_2, x_3, x_8);
lean_dec(x_1);
lean_dec(x_9);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_9, x_1, x_38, x_2, x_3, x_8);
lean_dec(x_1);
lean_dec(x_9);
return x_39;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Environment_getModuleIdxFor_x3f(x_42, x_1);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_45 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_46 = l_Lean_PersistentEnvExtension_getState___rarg(x_44, x_45, x_42);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__2(x_47, x_1);
x_49 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_42, x_1, x_48, x_2, x_3, x_41);
lean_dec(x_1);
lean_dec(x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
x_51 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_52 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_53 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_51, x_52, x_42, x_50);
lean_dec(x_50);
x_54 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_get_size(x_53);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_56, x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_56);
lean_dec(x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_53);
x_61 = lean_box(0);
x_62 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_42, x_1, x_61, x_2, x_3, x_41);
lean_dec(x_1);
lean_dec(x_42);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(0);
x_64 = l_Array_binSearchAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__5(x_63, x_53, x_55, x_59, x_58);
lean_dec(x_53);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_42, x_1, x_63, x_2, x_3, x_41);
lean_dec(x_1);
lean_dec(x_42);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_42, x_1, x_69, x_2, x_3, x_41);
lean_dec(x_1);
lean_dec(x_42);
return x_70;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_10 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_11 = l_Lean_PersistentEnvExtension_getState___rarg(x_9, x_10, x_8);
lean_dec(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lean_Name_hash___override(x_1);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_sub(x_23, x_24);
x_26 = lean_usize_land(x_22, x_25);
x_27 = lean_array_uget(x_13, x_26);
lean_dec(x_13);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(x_1, x_27);
lean_dec(x_27);
x_29 = lean_box(x_28);
lean_ctor_set(x_5, 0, x_29);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_34 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_35 = l_Lean_PersistentEnvExtension_getState___rarg(x_33, x_34, x_32);
lean_dec(x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_array_get_size(x_37);
x_39 = l_Lean_Name_hash___override(x_1);
x_40 = 32;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = 16;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_48 = 1;
x_49 = lean_usize_sub(x_47, x_48);
x_50 = lean_usize_land(x_46, x_49);
x_51 = lean_array_uget(x_37, x_50);
lean_dec(x_37);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(x_1, x_51);
lean_dec(x_51);
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_31);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_isBuiltinSimproc(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_isSimproc(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__2(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__5(x_1, x_2, x_8);
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
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__5(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__8(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__8(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__6(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__7(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__9(x_1, x_2, x_8);
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
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__9(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_69; 
x_6 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_7 = lean_st_ref_take(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_13 = x_8;
} else {
 lean_dec_ref(x_8);
 x_13 = lean_box(0);
}
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
x_72 = lean_array_get_size(x_71);
x_73 = l_Lean_Name_hash___override(x_1);
x_74 = 32;
x_75 = lean_uint64_shift_right(x_73, x_74);
x_76 = lean_uint64_xor(x_73, x_75);
x_77 = 16;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = lean_uint64_to_usize(x_79);
x_81 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_82 = 1;
x_83 = lean_usize_sub(x_81, x_82);
x_84 = lean_usize_land(x_80, x_83);
x_85 = lean_array_uget(x_71, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(x_1, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_70, x_87);
lean_dec(x_70);
lean_inc(x_1);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_3);
lean_ctor_set(x_89, 2, x_85);
x_90 = lean_array_uset(x_71, x_84, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__6(x_90);
lean_ctor_set(x_11, 1, x_97);
lean_ctor_set(x_11, 0, x_88);
x_98 = lean_ctor_get(x_12, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_12, 1);
lean_inc(x_99);
lean_dec(x_12);
x_14 = x_11;
x_15 = x_98;
x_16 = x_99;
goto block_68;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_ctor_set(x_11, 1, x_90);
lean_ctor_set(x_11, 0, x_88);
x_100 = lean_ctor_get(x_12, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
lean_dec(x_12);
x_14 = x_11;
x_15 = x_100;
x_16 = x_101;
goto block_68;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_71, x_84, x_102);
lean_inc(x_1);
x_104 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__9(x_1, x_3, x_85);
x_105 = lean_array_uset(x_103, x_84, x_104);
lean_ctor_set(x_11, 1, x_105);
x_106 = lean_ctor_get(x_12, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_12, 1);
lean_inc(x_107);
lean_dec(x_12);
x_14 = x_11;
x_15 = x_106;
x_16 = x_107;
goto block_68;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; uint8_t x_124; 
x_108 = lean_ctor_get(x_11, 0);
x_109 = lean_ctor_get(x_11, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_11);
x_110 = lean_array_get_size(x_109);
x_111 = l_Lean_Name_hash___override(x_1);
x_112 = 32;
x_113 = lean_uint64_shift_right(x_111, x_112);
x_114 = lean_uint64_xor(x_111, x_113);
x_115 = 16;
x_116 = lean_uint64_shift_right(x_114, x_115);
x_117 = lean_uint64_xor(x_114, x_116);
x_118 = lean_uint64_to_usize(x_117);
x_119 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_120 = 1;
x_121 = lean_usize_sub(x_119, x_120);
x_122 = lean_usize_land(x_118, x_121);
x_123 = lean_array_uget(x_109, x_122);
x_124 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(x_1, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_108, x_125);
lean_dec(x_108);
lean_inc(x_1);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_3);
lean_ctor_set(x_127, 2, x_123);
x_128 = lean_array_uset(x_109, x_122, x_127);
x_129 = lean_unsigned_to_nat(4u);
x_130 = lean_nat_mul(x_126, x_129);
x_131 = lean_unsigned_to_nat(3u);
x_132 = lean_nat_div(x_130, x_131);
lean_dec(x_130);
x_133 = lean_array_get_size(x_128);
x_134 = lean_nat_dec_le(x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__6(x_128);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_126);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_ctor_get(x_12, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_12, 1);
lean_inc(x_138);
lean_dec(x_12);
x_14 = x_136;
x_15 = x_137;
x_16 = x_138;
goto block_68;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_128);
x_140 = lean_ctor_get(x_12, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_12, 1);
lean_inc(x_141);
lean_dec(x_12);
x_14 = x_139;
x_15 = x_140;
x_16 = x_141;
goto block_68;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_box(0);
x_143 = lean_array_uset(x_109, x_122, x_142);
lean_inc(x_1);
x_144 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__9(x_1, x_3, x_123);
x_145 = lean_array_uset(x_143, x_122, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_108);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_ctor_get(x_12, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_12, 1);
lean_inc(x_148);
lean_dec(x_12);
x_14 = x_146;
x_15 = x_147;
x_16 = x_148;
goto block_68;
}
}
block_68:
{
lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__1(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_15, x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__2(x_35);
if (lean_is_scalar(x_10)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_10;
}
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
if (lean_is_scalar(x_13)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_13;
}
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_st_ref_set(x_6, x_44, x_9);
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
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
if (lean_is_scalar(x_10)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_10;
}
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_35);
if (lean_is_scalar(x_13)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_13;
}
lean_ctor_set(x_51, 0, x_14);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_st_ref_set(x_6, x_51, x_9);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_box(0);
x_58 = lean_array_uset(x_16, x_29, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__5(x_1, x_2, x_30);
x_60 = lean_array_uset(x_58, x_29, x_59);
if (lean_is_scalar(x_10)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_10;
}
lean_ctor_set(x_61, 0, x_15);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_13)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_13;
}
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_st_ref_set(x_6, x_62, x_9);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid builtin simproc declaration '", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', it has already been declared", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lean_Name_hash___override(x_1);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_sub(x_23, x_24);
x_26 = lean_usize_land(x_22, x_25);
x_27 = lean_array_uget(x_13, x_26);
lean_dec(x_13);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(x_1, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_7);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__1(x_1, x_2, x_3, x_29, x_11);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_31 = 1;
x_32 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1;
x_33 = l_Lean_Name_toString(x_1, x_31, x_32);
x_34 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_38);
return x_7;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; uint8_t x_55; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_array_get_size(x_40);
x_42 = l_Lean_Name_hash___override(x_1);
x_43 = 32;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = 16;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = lean_uint64_to_usize(x_48);
x_50 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_51 = 1;
x_52 = lean_usize_sub(x_50, x_51);
x_53 = lean_usize_land(x_49, x_52);
x_54 = lean_array_uget(x_40, x_53);
lean_dec(x_40);
x_55 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_isBuiltinSimproc___spec__1(x_1, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__1(x_1, x_2, x_3, x_56, x_39);
return x_57;
}
else
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_dec(x_2);
x_58 = 1;
x_59 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1;
x_60 = l_Lean_Name_toString(x_1, x_58, x_59);
x_61 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__2;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_39);
return x_66;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid builtin simproc declaration, it can only be registered during initialization", 84, 84);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_initializing(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3(x_1, x_3, x_2, x_15, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerBuiltinSimprocCore___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l_Lean_Meta_Simp_registerBuiltinSimprocCore(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l_Lean_Meta_Simp_registerBuiltinSimprocCore(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__1(x_5, x_1, x_2);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__1(x_8, x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerSimproc___lambda__1), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_15 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_14, x_11, x_13);
x_16 = l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1;
lean_ctor_set(x_8, 4, x_16);
lean_ctor_set(x_8, 0, x_15);
x_17 = lean_st_ref_set(x_5, x_8, x_9);
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
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_ctor_get(x_8, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerSimproc___lambda__1), 3, 2);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
x_31 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1;
x_32 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_31, x_24, x_30);
x_33 = l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1;
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
x_35 = lean_st_ref_set(x_5, x_34, x_9);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid simproc declaration '", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_7 = l_Lean_Meta_Simp_isSimproc(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_Lean_Meta_Simp_registerSimproc___lambda__2(x_1, x_2, x_11, x_4, x_5, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = l_Lean_MessageData_ofName(x_1);
x_17 = l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2;
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_17);
x_18 = l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_realizeGlobalConstCore___spec__3(x_19, x_4, x_5, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_dec(x_7);
x_26 = l_Lean_MessageData_ofName(x_1);
x_27 = l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__3;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_realizeGlobalConstCore___spec__3(x_30, x_4, x_5, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', function declaration is in an imported module", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_registerSimproc___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Environment_getModuleIdxFor_x3f(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_Simp_registerSimproc___lambda__3(x_1, x_2, x_12, x_3, x_4, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_2);
x_14 = l_Lean_MessageData_ofName(x_1);
x_15 = l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2;
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_15);
x_16 = l_Lean_Meta_Simp_registerSimproc___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_realizeGlobalConstCore___spec__3(x_17, x_3, x_4, x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Environment_getModuleIdxFor_x3f(x_25, x_1);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Simp_registerSimproc___lambda__3(x_1, x_2, x_27, x_3, x_4, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_2);
x_29 = l_Lean_MessageData_ofName(x_1);
x_30 = l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Meta_Simp_registerSimproc___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_realizeGlobalConstCore___spec__3(x_33, x_3, x_4, x_24);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_registerSimproc___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_registerSimproc___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_registerSimproc(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqSimprocEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_name_eq(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_instBEqSimprocEntry(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = 1;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1;
x_6 = l_Lean_Name_toString(x_3, x_4, x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(x_4, x_2);
x_7 = lean_box(0);
x_8 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_5, x_2, x_7);
lean_ctor_set(x_1, 3, x_8);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_13 = l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(x_11, x_2);
x_14 = lean_box(0);
x_15 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_12, x_2, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__1;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_ExtensionState_declNames___default___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2;
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1182_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2;
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_1, 18);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_1, 18);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type at simproc", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simproc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DSimproc", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_4);
x_5 = lean_environment_find(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = 1;
x_7 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1;
x_8 = l_Lean_Name_toString(x_1, x_6, x_7);
x_9 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = l_Lean_ConstantInfo_type(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_32 = lean_string_dec_eq(x_25, x_31);
lean_dec(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_36 = lean_string_dec_eq(x_24, x_35);
lean_dec(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5;
x_40 = lean_string_dec_eq(x_23, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6;
x_42 = lean_string_dec_eq(x_23, x_41);
lean_dec(x_23);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_dec(x_2);
x_46 = lean_eval_const(x_4, x_45, x_1);
lean_dec(x_1);
lean_dec(x_45);
lean_dec(x_4);
x_47 = l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__1(x_46, x_3);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_5, 0, x_49);
lean_ctor_set(x_47, 0, x_5);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_5, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_free_object(x_5);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_dec(x_2);
x_58 = lean_eval_const(x_4, x_57, x_1);
lean_dec(x_1);
lean_dec(x_57);
lean_dec(x_4);
x_59 = l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__2(x_58, x_3);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_61);
lean_ctor_set(x_59, 0, x_5);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_free_object(x_5);
x_65 = !lean_is_exclusive(x_59);
if (x_65 == 0)
{
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_73 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_3);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_75 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_3);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_77 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_3);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_17);
lean_free_object(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_79 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_3);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_5, 0);
lean_inc(x_81);
lean_dec(x_5);
x_82 = l_Lean_ConstantInfo_type(x_81);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 4)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 1)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 1)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 1)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_93 = lean_string_dec_eq(x_91, x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
return x_95;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_97 = lean_string_dec_eq(x_90, x_96);
lean_dec(x_90);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_98 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_3);
return x_99;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_101 = lean_string_dec_eq(x_89, x_100);
lean_dec(x_89);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_102 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_3);
return x_103;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5;
x_105 = lean_string_dec_eq(x_88, x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6;
x_107 = lean_string_dec_eq(x_88, x_106);
lean_dec(x_88);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_3);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_2, 1);
lean_inc(x_110);
lean_dec(x_2);
x_111 = lean_eval_const(x_4, x_110, x_1);
lean_dec(x_1);
lean_dec(x_110);
lean_dec(x_4);
x_112 = l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__1(x_111, x_3);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_113);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_88);
x_122 = lean_ctor_get(x_2, 1);
lean_inc(x_122);
lean_dec(x_2);
x_123 = lean_eval_const(x_4, x_122, x_1);
lean_dec(x_1);
lean_dec(x_122);
lean_dec(x_4);
x_124 = l_IO_ofExcept___at_Lean_Meta_Simp_getSimprocFromDeclImpl___spec__2(x_123, x_3);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_125);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_124, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_132 = x_124;
} else {
 lean_dec_ref(x_124);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_134 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_3);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_136 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_3);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_138 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_3);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_140 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_3);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_83);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_142 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_82);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_3);
return x_145;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Simprocs_erase(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___lambda__1), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_2, x_11, x_13);
x_15 = l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1;
lean_ctor_set(x_8, 4, x_15);
lean_ctor_set(x_8, 0, x_14);
x_16 = lean_st_ref_set(x_5, x_8, x_9);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = lean_ctor_get(x_8, 5);
x_28 = lean_ctor_get(x_8, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___lambda__1), 2, 1);
lean_closure_set(x_29, 0, x_1);
x_30 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_2, x_23, x_29);
x_31 = l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1;
x_32 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_27);
lean_ctor_set(x_32, 6, x_28);
x_33 = lean_st_ref_set(x_5, x_32, x_9);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not have a simproc attribute", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_eraseSimprocAttr___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_12 = l_Lean_ScopedEnvExtension_getState___rarg(x_11, x_1, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = l_Lean_MessageData_ofName(x_2);
x_16 = l_Lean_Meta_Simp_eraseSimprocAttr___closed__1;
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
x_17 = l_Lean_Meta_Simp_eraseSimprocAttr___closed__3;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(x_18, x_3, x_4, x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_6);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Simp_eraseSimprocAttr___lambda__2(x_2, x_1, x_24, x_3, x_4, x_9);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_30 = l_Lean_ScopedEnvExtension_getState___rarg(x_29, x_1, x_28);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = l_Lean_MessageData_ofName(x_2);
x_34 = l_Lean_Meta_Simp_eraseSimprocAttr___closed__1;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Meta_Simp_eraseSimprocAttr___closed__3;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(x_37, x_3, x_4, x_27);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_Meta_Simp_eraseSimprocAttr___lambda__2(x_2, x_1, x_43, x_3, x_4, x_27);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_eraseSimprocAttr___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_eraseSimprocAttr(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 6);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 4);
lean_dec(x_13);
x_14 = l_Lean_ScopedEnvExtension_addCore___rarg(x_12, x_1, x_2, x_3, x_7);
x_15 = l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1;
lean_ctor_set(x_9, 4, x_15);
lean_ctor_set(x_9, 0, x_14);
x_16 = lean_st_ref_set(x_5, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
x_26 = lean_ctor_get(x_9, 3);
x_27 = lean_ctor_get(x_9, 5);
x_28 = lean_ctor_get(x_9, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_29 = l_Lean_ScopedEnvExtension_addCore___rarg(x_23, x_1, x_2, x_3, x_7);
x_30 = l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1;
x_31 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_27);
lean_ctor_set(x_31, 6, x_28);
x_32 = lean_st_ref_set(x_5, x_31, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_12);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
lean_inc(x_2);
x_15 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_8, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(x_2, x_5, x_6, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = l_Lean_MessageData_ofName(x_2);
x_24 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_18, 0, x_24);
x_25 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___private_Lean_ReducibilityAttrs_0__Lean_validate___spec__3(x_26, x_5, x_6, x_21);
lean_dec(x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = l_Lean_MessageData_ofName(x_2);
x_30 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___private_Lean_ReducibilityAttrs_0__Lean_validate___spec__3(x_33, x_5, x_6, x_28);
lean_dec(x_5);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_18, 1);
x_37 = lean_ctor_get(x_18, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_4);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 0, x_39);
x_40 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1(x_1, x_18, x_3, x_5, x_6, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
lean_dec(x_19);
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_16);
x_45 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1(x_1, x_44, x_3, x_5, x_6, x_41);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_io_error_to_string(x_47);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_14);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_15, 0, x_51);
return x_15;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_15, 0);
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_15);
x_54 = lean_io_error_to_string(x_52);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_8, 0);
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_8);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_ctor_get(x_5, 5);
lean_inc(x_64);
lean_inc(x_2);
x_65 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_63, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_2);
x_68 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(x_2, x_5, x_6, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_66);
lean_dec(x_1);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_Lean_MessageData_ofName(x_2);
x_73 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(7, 2, 0);
} else {
 x_74 = x_71;
 lean_ctor_set_tag(x_74, 7);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_throwError___at___private_Lean_ReducibilityAttrs_0__Lean_validate___spec__3(x_76, x_5, x_6, x_70);
lean_dec(x_5);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_79 = x_68;
} else {
 lean_dec_ref(x_68);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
lean_dec(x_69);
x_81 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_4);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_66);
x_83 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1(x_1, x_82, x_3, x_5, x_6, x_78);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_ctor_get(x_65, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_86 = x_65;
} else {
 lean_dec_ref(x_65);
 x_86 = lean_box(0);
}
x_87 = lean_io_error_to_string(x_84);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_MessageData_ofFormat(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_64);
lean_ctor_set(x_90, 1, x_89);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_Simp_addSimprocAttrCore___spec__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Meta_Simp_addSimprocAttrCore(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_5, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__4(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_Simprocs_addCore___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__3(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_Simprocs_addCore___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_3, x_17);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
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
x_21 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_4, x_19);
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
x_28 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_4, x_26);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2;
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
x_63 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_101_(x_4, x_60);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__8(x_1, x_83, x_4, x_5);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_Simprocs_addCore___spec__7(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__8(x_96, x_97, x_4, x_5);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_Simprocs_addCore___spec__7(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_Simprocs_addCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Simp_Simprocs_addCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_array_fset(x_1, x_3, x_2);
lean_dec(x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_7, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_6);
x_12 = lean_array_get(x_6, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = l_Lean_Meta_DiscrTree_Key_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_lt(x_11, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_array_fget(x_5, x_11);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_5, x_11, x_20);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_3, x_25);
x_27 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_1, x_2, x_26, x_23);
lean_dec(x_26);
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_4);
x_28 = lean_array_fset(x_21, x_11, x_19);
lean_dec(x_11);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
x_32 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_1, x_2, x_31, x_29);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_fset(x_21, x_11, x_33);
lean_dec(x_11);
return x_34;
}
}
}
else
{
x_8 = x_11;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_13);
x_36 = lean_nat_dec_eq(x_11, x_7);
if (x_36 == 0)
{
lean_dec(x_7);
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_3, x_38);
x_40 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_nat_add(x_7, x_38);
lean_dec(x_7);
x_43 = l_Array_insertAt_x21___rarg(x_5, x_42, x_41);
lean_dec(x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Simp_Simprocs_addCore___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___rarg(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_9 = lean_array_get(x_6, x_5, x_8);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_DiscrTree_Key_lt(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_10);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_8, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_array_fget(x_5, x_8);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_5, x_8, x_17);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_1, x_2, x_23, x_20);
lean_dec(x_23);
lean_ctor_set(x_16, 1, x_24);
lean_ctor_set(x_16, 0, x_4);
x_25 = lean_array_fset(x_18, x_8, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_3, x_27);
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_1, x_2, x_28, x_26);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_fset(x_18, x_8, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_inc(x_6);
x_32 = l_Array_back___rarg(x_6, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Meta_DiscrTree_Key_lt(x_33, x_10);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Meta_DiscrTree_Key_lt(x_10, x_33);
lean_dec(x_33);
lean_dec(x_10);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_6);
x_36 = lean_array_get_size(x_5);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_36, x_37);
x_39 = lean_nat_dec_lt(x_38, x_36);
lean_dec(x_36);
if (x_39 == 0)
{
lean_dec(x_38);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_array_fget(x_5, x_38);
x_41 = lean_box(0);
x_42 = lean_array_fset(x_5, x_38, x_41);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_ctor_get(x_40, 0);
lean_dec(x_45);
x_46 = lean_nat_add(x_3, x_37);
x_47 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_1, x_2, x_46, x_44);
lean_dec(x_46);
lean_ctor_set(x_40, 1, x_47);
lean_ctor_set(x_40, 0, x_4);
x_48 = lean_array_fset(x_42, x_38, x_40);
lean_dec(x_38);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_nat_add(x_3, x_37);
x_51 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_1, x_2, x_50, x_49);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_fset(x_42, x_38, x_52);
lean_dec(x_38);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_array_get_size(x_5);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_54, x_55);
lean_dec(x_54);
x_57 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_6);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_3, x_58);
x_60 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_push(x_5, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_3, x_63);
x_65 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Array_insertAt_x21___rarg(x_5, x_8, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_6);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_3, x_68);
x_70 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_5, x_71);
return x_72;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Simp_Simprocs_addCore___spec__10(x_6, x_2, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_1, x_3);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___closed__1;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_binInsertM___at_Lean_Meta_Simp_Simprocs_addCore___spec__11(x_1, x_2, x_3, x_12, x_7, x_14);
lean_ctor_set(x_4, 1, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_lt(x_3, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Simp_Simprocs_addCore___spec__10(x_16, x_2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_array_fget(x_1, x_3);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___closed__1;
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_binInsertM___at_Lean_Meta_Simp_Simprocs_addCore___spec__11(x_1, x_2, x_3, x_23, x_17, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.insertCore", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid key sequence", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(488u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_9 = l_outOfBounds___rarg(x_8);
lean_inc(x_1);
x_10 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_Simprocs_addCore___spec__2(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_11);
x_13 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_Simprocs_addCore___spec__5(x_1, x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_2, x_3, x_15, x_14);
x_17 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_Simprocs_addCore___spec__5(x_1, x_9, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_2, x_6);
lean_inc(x_1);
x_19 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_Simprocs_addCore___spec__2(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_20);
x_22 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_Simprocs_addCore___spec__5(x_1, x_18, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_2, x_3, x_24, x_23);
x_26 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_Simprocs_addCore___spec__5(x_1, x_18, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__4;
x_28 = l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_box(0);
lean_inc(x_3);
x_12 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_9, x_3, x_11);
x_13 = l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(x_10, x_3);
if (x_4 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1(x_7, x_2, x_15);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_13);
lean_ctor_set(x_1, 2, x_12);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1(x_8, x_2, x_18);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_13);
lean_ctor_set(x_1, 2, x_12);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_box(0);
lean_inc(x_3);
x_25 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_22, x_3, x_24);
x_26 = l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(x_23, x_3);
if (x_4 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
x_29 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1(x_20, x_2, x_28);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_2);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1(x_21, x_2, x_32);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_26);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_Simprocs_addCore___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_Simprocs_addCore___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_Simprocs_addCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_Simprocs_addCore___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__6(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Simp_Simprocs_addCore___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binInsertM___at_Lean_Meta_Simp_Simprocs_addCore___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_Simp_Simprocs_addCore(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid [builtin_simproc] attribute, '{declName}' is not a builtin simproc", 74, 74);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_sub(x_23, x_24);
x_26 = lean_usize_land(x_22, x_25);
x_27 = lean_array_uget(x_13, x_26);
lean_dec(x_13);
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1(x_2, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__2;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_7);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_take(x_1, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Simp_Simprocs_addCore(x_32, x_30, x_2, x_3, x_4);
x_35 = lean_st_ref_set(x_1, x_34, x_33);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_dec(x_9);
x_42 = lean_array_get_size(x_41);
x_43 = l_Lean_Name_hash___override(x_2);
x_44 = 32;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = 16;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_52 = 1;
x_53 = lean_usize_sub(x_51, x_52);
x_54 = lean_usize_land(x_50, x_53);
x_55 = lean_array_uget(x_41, x_54);
lean_dec(x_41);
x_56 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocDeclKeys_x3f___spec__1(x_2, x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_4);
lean_dec(x_2);
x_57 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_40);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_st_ref_take(x_1, x_40);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Simp_Simprocs_addCore(x_61, x_59, x_2, x_3, x_4);
x_64 = lean_st_ref_set(x_1, x_63, x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocBuiltinAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_builtinSimprocsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr___closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_builtinSEvalprocsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(x_1, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MessageData_ofName(x_1);
x_12 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__1(x_15, x_5, x_6, x_10);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Meta_Simp_Simprocs_addCore(x_2, x_19, x_1, x_3, x_4);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = l_Lean_Meta_Simp_Simprocs_addCore(x_2, x_22, x_1, x_3, x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = lean_ctor_get(x_4, 5);
lean_inc(x_2);
x_14 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_7, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_2, x_1, x_3, x_15, x_4, x_5, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_io_error_to_string(x_19);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
lean_inc(x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Exception_isInterrupt(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_14);
x_27 = l_Lean_Meta_Simp_isBuiltinSimproc(x_2, x_4, x_5, x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_24);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_36 = lean_st_ref_get(x_35, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_38, 1);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = lean_array_get_size(x_43);
x_46 = l_Lean_Name_hash___override(x_2);
x_47 = 32;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = 16;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = 1;
x_56 = lean_usize_sub(x_54, x_55);
x_57 = lean_usize_land(x_53, x_56);
x_58 = lean_array_uget(x_43, x_57);
lean_dec(x_43);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(x_2, x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_1);
x_60 = l_Lean_MessageData_ofName(x_2);
x_61 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_61);
x_62 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_38);
x_63 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(x_36, x_4, x_5, x_40);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_free_object(x_38);
lean_free_object(x_36);
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
x_69 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_2, x_1, x_3, x_68, x_4, x_5, x_40);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
lean_dec(x_38);
x_71 = lean_array_get_size(x_70);
x_72 = l_Lean_Name_hash___override(x_2);
x_73 = 32;
x_74 = lean_uint64_shift_right(x_72, x_73);
x_75 = lean_uint64_xor(x_72, x_74);
x_76 = 16;
x_77 = lean_uint64_shift_right(x_75, x_76);
x_78 = lean_uint64_xor(x_75, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_81 = 1;
x_82 = lean_usize_sub(x_80, x_81);
x_83 = lean_usize_land(x_79, x_82);
x_84 = lean_array_uget(x_70, x_83);
lean_dec(x_70);
x_85 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(x_2, x_84);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_86 = l_Lean_MessageData_ofName(x_2);
x_87 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_89);
lean_ctor_set(x_36, 0, x_88);
x_90 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(x_36, x_4, x_5, x_40);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_free_object(x_36);
x_95 = lean_ctor_get(x_85, 0);
lean_inc(x_95);
lean_dec(x_85);
x_96 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_2, x_1, x_3, x_95, x_4, x_5, x_40);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; size_t x_108; size_t x_109; size_t x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; 
x_97 = lean_ctor_get(x_36, 1);
lean_inc(x_97);
lean_dec(x_36);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_99 = x_38;
} else {
 lean_dec_ref(x_38);
 x_99 = lean_box(0);
}
x_100 = lean_array_get_size(x_98);
x_101 = l_Lean_Name_hash___override(x_2);
x_102 = 32;
x_103 = lean_uint64_shift_right(x_101, x_102);
x_104 = lean_uint64_xor(x_101, x_103);
x_105 = 16;
x_106 = lean_uint64_shift_right(x_104, x_105);
x_107 = lean_uint64_xor(x_104, x_106);
x_108 = lean_uint64_to_usize(x_107);
x_109 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_110 = 1;
x_111 = lean_usize_sub(x_109, x_110);
x_112 = lean_usize_land(x_108, x_111);
x_113 = lean_array_uget(x_98, x_112);
lean_dec(x_98);
x_114 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(x_2, x_113);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_1);
x_115 = l_Lean_MessageData_ofName(x_2);
x_116 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
if (lean_is_scalar(x_99)) {
 x_117 = lean_alloc_ctor(7, 2, 0);
} else {
 x_117 = x_99;
 lean_ctor_set_tag(x_117, 7);
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(x_119, x_4, x_5, x_97);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_99);
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
lean_dec(x_114);
x_126 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_2, x_1, x_3, x_125, x_4, x_5, x_97);
return x_126;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_127 = lean_ctor_get(x_14, 0);
x_128 = lean_ctor_get(x_14, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_14);
x_129 = lean_io_error_to_string(x_127);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Lean_MessageData_ofFormat(x_130);
lean_inc(x_13);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_13);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Exception_isInterrupt(x_132);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = l_Lean_Exception_isRuntime(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = l_Lean_Meta_Simp_isBuiltinSimproc(x_2, x_4, x_5, x_128);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_132);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; uint64_t x_154; uint64_t x_155; uint64_t x_156; uint64_t x_157; size_t x_158; size_t x_159; size_t x_160; size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_132);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
lean_dec(x_135);
x_142 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_143 = lean_st_ref_get(x_142, x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_147 = x_143;
} else {
 lean_dec_ref(x_143);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
x_150 = lean_array_get_size(x_148);
x_151 = l_Lean_Name_hash___override(x_2);
x_152 = 32;
x_153 = lean_uint64_shift_right(x_151, x_152);
x_154 = lean_uint64_xor(x_151, x_153);
x_155 = 16;
x_156 = lean_uint64_shift_right(x_154, x_155);
x_157 = lean_uint64_xor(x_154, x_156);
x_158 = lean_uint64_to_usize(x_157);
x_159 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_160 = 1;
x_161 = lean_usize_sub(x_159, x_160);
x_162 = lean_usize_land(x_158, x_161);
x_163 = lean_array_uget(x_148, x_162);
lean_dec(x_148);
x_164 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(x_2, x_163);
lean_dec(x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_1);
x_165 = l_Lean_MessageData_ofName(x_2);
x_166 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
if (lean_is_scalar(x_149)) {
 x_167 = lean_alloc_ctor(7, 2, 0);
} else {
 x_167 = x_149;
 lean_ctor_set_tag(x_167, 7);
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
if (lean_is_scalar(x_147)) {
 x_169 = lean_alloc_ctor(7, 2, 0);
} else {
 x_169 = x_147;
 lean_ctor_set_tag(x_169, 7);
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(x_169, x_4, x_5, x_146);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_149);
lean_dec(x_147);
x_175 = lean_ctor_get(x_164, 0);
lean_inc(x_175);
lean_dec(x_164);
x_176 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_2, x_1, x_3, x_175, x_4, x_5, x_146);
return x_176;
}
}
}
else
{
lean_object* x_177; 
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_132);
lean_ctor_set(x_177, 1, x_128);
return x_177;
}
}
else
{
lean_object* x_178; 
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_132);
lean_ctor_set(x_178, 1, x_128);
return x_178;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_179 = lean_ctor_get(x_7, 0);
x_180 = lean_ctor_get(x_7, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_7);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_4, 2);
lean_inc(x_182);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_ctor_get(x_4, 5);
lean_inc(x_2);
x_185 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_183, x_180);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_2, x_1, x_3, x_186, x_4, x_5, x_187);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
x_192 = lean_io_error_to_string(x_189);
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_194 = l_Lean_MessageData_ofFormat(x_193);
lean_inc(x_184);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_184);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Exception_isInterrupt(x_195);
if (x_196 == 0)
{
uint8_t x_197; 
x_197 = l_Lean_Exception_isRuntime(x_195);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_191);
x_198 = l_Lean_Meta_Simp_isBuiltinSimproc(x_2, x_4, x_5, x_190);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_202 = x_198;
} else {
 lean_dec_ref(x_198);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
 lean_ctor_set_tag(x_203, 1);
}
lean_ctor_set(x_203, 0, x_195);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint64_t x_214; uint64_t x_215; uint64_t x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; uint64_t x_220; size_t x_221; size_t x_222; size_t x_223; size_t x_224; size_t x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_195);
x_204 = lean_ctor_get(x_198, 1);
lean_inc(x_204);
lean_dec(x_198);
x_205 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1;
x_206 = lean_st_ref_get(x_205, x_204);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_210 = x_206;
} else {
 lean_dec_ref(x_206);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_212 = x_208;
} else {
 lean_dec_ref(x_208);
 x_212 = lean_box(0);
}
x_213 = lean_array_get_size(x_211);
x_214 = l_Lean_Name_hash___override(x_2);
x_215 = 32;
x_216 = lean_uint64_shift_right(x_214, x_215);
x_217 = lean_uint64_xor(x_214, x_216);
x_218 = 16;
x_219 = lean_uint64_shift_right(x_217, x_218);
x_220 = lean_uint64_xor(x_217, x_219);
x_221 = lean_uint64_to_usize(x_220);
x_222 = lean_usize_of_nat(x_213);
lean_dec(x_213);
x_223 = 1;
x_224 = lean_usize_sub(x_222, x_223);
x_225 = lean_usize_land(x_221, x_224);
x_226 = lean_array_uget(x_211, x_225);
lean_dec(x_211);
x_227 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(x_2, x_226);
lean_dec(x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_1);
x_228 = l_Lean_MessageData_ofName(x_2);
x_229 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__2;
if (lean_is_scalar(x_212)) {
 x_230 = lean_alloc_ctor(7, 2, 0);
} else {
 x_230 = x_212;
 lean_ctor_set_tag(x_230, 7);
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_Lean_Meta_Simp_addSimprocAttrCore___closed__4;
if (lean_is_scalar(x_210)) {
 x_232 = lean_alloc_ctor(7, 2, 0);
} else {
 x_232 = x_210;
 lean_ctor_set_tag(x_232, 7);
}
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(x_232, x_4, x_5, x_209);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_212);
lean_dec(x_210);
x_238 = lean_ctor_get(x_227, 0);
lean_inc(x_238);
lean_dec(x_227);
x_239 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_2, x_1, x_3, x_238, x_4, x_5, x_209);
return x_239;
}
}
}
else
{
lean_object* x_240; 
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_191)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_191;
}
lean_ctor_set(x_240, 0, x_195);
lean_ctor_set(x_240, 1, x_190);
return x_240;
}
}
else
{
lean_object* x_241; 
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_191)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_191;
}
lean_ctor_set(x_241, 0, x_195);
lean_ctor_set(x_241, 1, x_190);
return x_241;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_Simprocs_add___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Meta_Simp_Simprocs_add___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Meta_Simp_Simprocs_add___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_Simp_Simprocs_add(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_1, x_17);
lean_dec(x_1);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = l_Lean_Expr_appArg_x21(x_19);
x_22 = lean_array_push(x_20, x_21);
x_23 = l_Lean_Expr_appFn_x21(x_19);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_25;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_13);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_13);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_16 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1(x_2, x_14, x_2, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Array_reverse___rarg(x_20);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = lean_apply_9(x_23, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Simp_Step_addExtraArgs(x_25, x_21, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_21);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_33 = lean_apply_9(x_32, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_TransformStep_toStep(x_34);
x_37 = l_Lean_Meta_Simp_Step_addExtraArgs(x_36, x_21, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_21);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_16 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1(x_2, x_14, x_2, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1;
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = l_Array_reverse___rarg(x_27);
x_30 = lean_apply_9(x_28, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_Meta_Simp_DStep_addExtraArgs(x_32, x_29);
lean_dec(x_29);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = l_Lean_Meta_Simp_DStep_addExtraArgs(x_34, x_29);
lean_dec(x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_29);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_19 = l_Lean_Meta_Simp_recordSimpTheorem(x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unbox(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_3, x_21, x_5, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_22);
if (x_42 == 0)
{
return x_22;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_19 = l_Lean_Meta_Simp_recordSimpTheorem(x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unbox(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_3, x_21, x_5, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_22);
if (x_42 == 0)
{
return x_22;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_20 = l_Lean_Meta_Simp_recordSimpTheorem(x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_dec(x_3);
x_25 = l_Lean_Meta_mkEqTrans_x3f(x_8, x_23, x_13, x_14, x_15, x_16, x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
if (x_5 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_box(x_18);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_box(x_24);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_25, 0, x_39);
return x_25;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_25);
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_22);
lean_ctor_set(x_45, 1, x_44);
if (x_5 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_box(x_18);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_box(x_24);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_41);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_22);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_25, 0);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_25);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
return x_20;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simproc result ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" => ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_18 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_ctor_get(x_18, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
lean_inc(x_2);
x_46 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_40);
x_47 = l_Lean_Meta_Simp_SimprocEntry_try(x_31, x_34, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
switch (lean_obj_tag(x_48)) {
case 0:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_52 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_51, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_18);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_45, x_1, x_44, x_37, x_50, x_43, x_40, x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_19 = x_58;
x_20 = x_59;
goto block_27;
}
else
{
uint8_t x_60; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_65 = lean_ctor_get(x_52, 1);
x_66 = lean_ctor_get(x_52, 0);
lean_dec(x_66);
lean_inc(x_40);
x_67 = l_Lean_MessageData_ofExpr(x_40);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_67);
lean_ctor_set(x_52, 0, x_68);
x_69 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_69);
lean_ctor_set(x_18, 0, x_52);
x_70 = lean_ctor_get(x_50, 0);
lean_inc(x_70);
x_71 = l_Lean_MessageData_ofExpr(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_51, x_74, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_65);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_78 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_45, x_1, x_44, x_37, x_50, x_43, x_40, x_76, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_77);
lean_dec(x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_19 = x_79;
x_20 = x_80;
goto block_27;
}
else
{
uint8_t x_81; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_85 = lean_ctor_get(x_52, 1);
lean_inc(x_85);
lean_dec(x_52);
lean_inc(x_40);
x_86 = l_Lean_MessageData_ofExpr(x_40);
x_87 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_89);
lean_ctor_set(x_18, 0, x_88);
x_90 = lean_ctor_get(x_50, 0);
lean_inc(x_90);
x_91 = l_Lean_MessageData_ofExpr(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_18);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_51, x_94, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_85);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_98 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_45, x_1, x_44, x_37, x_50, x_43, x_40, x_96, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_97);
lean_dec(x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_19 = x_99;
x_20 = x_100;
goto block_27;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_103 = x_98;
} else {
 lean_dec_ref(x_98);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
}
case 1:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
x_105 = lean_ctor_get(x_47, 1);
lean_inc(x_105);
lean_dec(x_47);
x_106 = lean_ctor_get(x_48, 0);
lean_inc(x_106);
lean_dec(x_48);
x_107 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_108 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_107, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_105);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_18);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_113 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_45, x_1, x_44, x_37, x_106, x_43, x_40, x_112, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_19 = x_114;
x_20 = x_115;
goto block_27;
}
else
{
uint8_t x_116; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_113);
if (x_116 == 0)
{
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_113, 0);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_113);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_108);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_121 = lean_ctor_get(x_108, 1);
x_122 = lean_ctor_get(x_108, 0);
lean_dec(x_122);
lean_inc(x_40);
x_123 = l_Lean_MessageData_ofExpr(x_40);
x_124 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
lean_ctor_set_tag(x_108, 7);
lean_ctor_set(x_108, 1, x_123);
lean_ctor_set(x_108, 0, x_124);
x_125 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_125);
lean_ctor_set(x_18, 0, x_108);
x_126 = lean_ctor_get(x_106, 0);
lean_inc(x_126);
x_127 = l_Lean_MessageData_ofExpr(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_18);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_107, x_130, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_121);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_134 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_45, x_1, x_44, x_37, x_106, x_43, x_40, x_132, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_133);
lean_dec(x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_19 = x_135;
x_20 = x_136;
goto block_27;
}
else
{
uint8_t x_137; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_134);
if (x_137 == 0)
{
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_134, 0);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_134);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_141 = lean_ctor_get(x_108, 1);
lean_inc(x_141);
lean_dec(x_108);
lean_inc(x_40);
x_142 = l_Lean_MessageData_ofExpr(x_40);
x_143 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_145);
lean_ctor_set(x_18, 0, x_144);
x_146 = lean_ctor_get(x_106, 0);
lean_inc(x_146);
x_147 = l_Lean_MessageData_ofExpr(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_18);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_107, x_150, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_141);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_154 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_45, x_1, x_44, x_37, x_106, x_43, x_40, x_152, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_153);
lean_dec(x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_19 = x_155;
x_20 = x_156;
goto block_27;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_159 = x_154;
} else {
 lean_dec_ref(x_154);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
default: 
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_48);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_48, 0);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
lean_dec(x_45);
x_163 = lean_ctor_get(x_47, 1);
lean_inc(x_163);
lean_dec(x_47);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set_tag(x_48, 1);
lean_ctor_set(x_48, 0, x_18);
x_19 = x_48;
x_20 = x_163;
goto block_27;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_free_object(x_48);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
x_164 = lean_ctor_get(x_47, 1);
lean_inc(x_164);
lean_dec(x_47);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
lean_dec(x_162);
x_166 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_167 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_166, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_164);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_173; lean_object* x_174; 
lean_free_object(x_18);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_box(0);
x_172 = lean_unbox(x_37);
lean_dec(x_37);
x_173 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_174 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_45, x_1, x_165, x_3, x_172, x_40, x_173, x_44, x_171, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_170);
lean_dec(x_40);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_19 = x_175;
x_20 = x_176;
goto block_27;
}
else
{
uint8_t x_177; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_174);
if (x_177 == 0)
{
return x_174;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_174, 0);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_174);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_167);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; lean_object* x_197; 
x_182 = lean_ctor_get(x_167, 1);
x_183 = lean_ctor_get(x_167, 0);
lean_dec(x_183);
lean_inc(x_40);
x_184 = l_Lean_MessageData_ofExpr(x_40);
x_185 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
lean_ctor_set_tag(x_167, 7);
lean_ctor_set(x_167, 1, x_184);
lean_ctor_set(x_167, 0, x_185);
x_186 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_186);
lean_ctor_set(x_18, 0, x_167);
x_187 = lean_ctor_get(x_165, 0);
lean_inc(x_187);
x_188 = l_Lean_MessageData_ofExpr(x_187);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_18);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_166, x_191, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_182);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_unbox(x_37);
lean_dec(x_37);
x_196 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_197 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_45, x_1, x_165, x_3, x_195, x_40, x_196, x_44, x_193, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_194);
lean_dec(x_193);
lean_dec(x_40);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_19 = x_198;
x_20 = x_199;
goto block_27;
}
else
{
uint8_t x_200; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
return x_197;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_197, 0);
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_197);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; lean_object* x_219; 
x_204 = lean_ctor_get(x_167, 1);
lean_inc(x_204);
lean_dec(x_167);
lean_inc(x_40);
x_205 = l_Lean_MessageData_ofExpr(x_40);
x_206 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_208);
lean_ctor_set(x_18, 0, x_207);
x_209 = lean_ctor_get(x_165, 0);
lean_inc(x_209);
x_210 = l_Lean_MessageData_ofExpr(x_209);
x_211 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_211, 0, x_18);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_166, x_213, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_204);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_unbox(x_37);
lean_dec(x_37);
x_218 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_219 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_45, x_1, x_165, x_3, x_217, x_40, x_218, x_44, x_215, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_216);
lean_dec(x_215);
lean_dec(x_40);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_19 = x_220;
x_20 = x_221;
goto block_27;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_222 = lean_ctor_get(x_219, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_224 = x_219;
} else {
 lean_dec_ref(x_219);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
}
}
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_48, 0);
lean_inc(x_226);
lean_dec(x_48);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_45);
x_227 = lean_ctor_get(x_47, 1);
lean_inc(x_227);
lean_dec(x_47);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_18);
x_19 = x_228;
x_20 = x_227;
goto block_27;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
x_229 = lean_ctor_get(x_47, 1);
lean_inc(x_229);
lean_dec(x_47);
x_230 = lean_ctor_get(x_226, 0);
lean_inc(x_230);
lean_dec(x_226);
x_231 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_232 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_231, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_229);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_unbox(x_233);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; 
lean_free_object(x_18);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
x_236 = lean_box(0);
x_237 = lean_unbox(x_37);
lean_dec(x_37);
x_238 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_239 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_45, x_1, x_230, x_3, x_237, x_40, x_238, x_44, x_236, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_235);
lean_dec(x_40);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_19 = x_240;
x_20 = x_241;
goto block_27;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_244 = x_239;
} else {
 lean_dec_ref(x_239);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; 
x_246 = lean_ctor_get(x_232, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_247 = x_232;
} else {
 lean_dec_ref(x_232);
 x_247 = lean_box(0);
}
lean_inc(x_40);
x_248 = l_Lean_MessageData_ofExpr(x_40);
x_249 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_247)) {
 x_250 = lean_alloc_ctor(7, 2, 0);
} else {
 x_250 = x_247;
 lean_ctor_set_tag(x_250, 7);
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_251);
lean_ctor_set(x_18, 0, x_250);
x_252 = lean_ctor_get(x_230, 0);
lean_inc(x_252);
x_253 = l_Lean_MessageData_ofExpr(x_252);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_18);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_256 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_231, x_256, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_246);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_unbox(x_37);
lean_dec(x_37);
x_261 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_262 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_45, x_1, x_230, x_3, x_260, x_40, x_261, x_44, x_258, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_259);
lean_dec(x_258);
lean_dec(x_40);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_19 = x_263;
x_20 = x_264;
goto block_27;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_267 = x_262;
} else {
 lean_dec_ref(x_262);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
}
}
}
}
else
{
uint8_t x_269; 
lean_dec(x_45);
lean_free_object(x_30);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_28);
lean_dec(x_37);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_269 = !lean_is_exclusive(x_47);
if (x_269 == 0)
{
return x_47;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_47, 0);
x_271 = lean_ctor_get(x_47, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_47);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_273; 
lean_dec(x_45);
lean_dec(x_34);
lean_dec(x_31);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_18);
x_19 = x_273;
x_20 = x_15;
goto block_27;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_274 = lean_ctor_get(x_30, 0);
x_275 = lean_ctor_get(x_30, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_30);
x_276 = lean_ctor_get(x_32, 0);
lean_inc(x_276);
lean_dec(x_32);
lean_inc(x_2);
x_277 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_276);
if (x_277 == 0)
{
lean_object* x_278; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_40);
x_278 = l_Lean_Meta_Simp_SimprocEntry_try(x_31, x_34, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
switch (lean_obj_tag(x_279)) {
case 0:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_free_object(x_29);
lean_free_object(x_28);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
lean_dec(x_279);
x_282 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_283 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_282, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_280);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_unbox(x_284);
lean_dec(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_free_object(x_18);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_288 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_276, x_1, x_275, x_37, x_281, x_274, x_40, x_287, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_286);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_19 = x_289;
x_20 = x_290;
goto block_27;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_291 = lean_ctor_get(x_288, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_293 = x_288;
} else {
 lean_dec_ref(x_288);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_295 = lean_ctor_get(x_283, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_296 = x_283;
} else {
 lean_dec_ref(x_283);
 x_296 = lean_box(0);
}
lean_inc(x_40);
x_297 = l_Lean_MessageData_ofExpr(x_40);
x_298 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_296)) {
 x_299 = lean_alloc_ctor(7, 2, 0);
} else {
 x_299 = x_296;
 lean_ctor_set_tag(x_299, 7);
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_300);
lean_ctor_set(x_18, 0, x_299);
x_301 = lean_ctor_get(x_281, 0);
lean_inc(x_301);
x_302 = l_Lean_MessageData_ofExpr(x_301);
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_18);
lean_ctor_set(x_303, 1, x_302);
x_304 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_305 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_282, x_305, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_295);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_309 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_276, x_1, x_275, x_37, x_281, x_274, x_40, x_307, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_308);
lean_dec(x_307);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_19 = x_310;
x_20 = x_311;
goto block_27;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_312 = lean_ctor_get(x_309, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_309, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_314 = x_309;
} else {
 lean_dec_ref(x_309);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
}
case 1:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
lean_free_object(x_29);
lean_free_object(x_28);
x_316 = lean_ctor_get(x_278, 1);
lean_inc(x_316);
lean_dec(x_278);
x_317 = lean_ctor_get(x_279, 0);
lean_inc(x_317);
lean_dec(x_279);
x_318 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_319 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_318, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_316);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_unbox(x_320);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_free_object(x_18);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_323 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_324 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_276, x_1, x_275, x_37, x_317, x_274, x_40, x_323, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_322);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_19 = x_325;
x_20 = x_326;
goto block_27;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_327 = lean_ctor_get(x_324, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_329 = x_324;
} else {
 lean_dec_ref(x_324);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_331 = lean_ctor_get(x_319, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_332 = x_319;
} else {
 lean_dec_ref(x_319);
 x_332 = lean_box(0);
}
lean_inc(x_40);
x_333 = l_Lean_MessageData_ofExpr(x_40);
x_334 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_332)) {
 x_335 = lean_alloc_ctor(7, 2, 0);
} else {
 x_335 = x_332;
 lean_ctor_set_tag(x_335, 7);
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_336);
lean_ctor_set(x_18, 0, x_335);
x_337 = lean_ctor_get(x_317, 0);
lean_inc(x_337);
x_338 = l_Lean_MessageData_ofExpr(x_337);
x_339 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_339, 0, x_18);
lean_ctor_set(x_339, 1, x_338);
x_340 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_341 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_318, x_341, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_331);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_345 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_276, x_1, x_275, x_37, x_317, x_274, x_40, x_343, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_344);
lean_dec(x_343);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_19 = x_346;
x_20 = x_347;
goto block_27;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_345, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_350 = x_345;
} else {
 lean_dec_ref(x_345);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
}
default: 
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_279, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 x_353 = x_279;
} else {
 lean_dec_ref(x_279);
 x_353 = lean_box(0);
}
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_276);
x_354 = lean_ctor_get(x_278, 1);
lean_inc(x_354);
lean_dec(x_278);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_274);
lean_ctor_set(x_355, 1, x_275);
lean_ctor_set(x_29, 1, x_355);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
if (lean_is_scalar(x_353)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_353;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_18);
x_19 = x_356;
x_20 = x_354;
goto block_27;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
lean_dec(x_353);
lean_free_object(x_29);
lean_free_object(x_28);
x_357 = lean_ctor_get(x_278, 1);
lean_inc(x_357);
lean_dec(x_278);
x_358 = lean_ctor_get(x_352, 0);
lean_inc(x_358);
lean_dec(x_352);
x_359 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_360 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_359, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_357);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_unbox(x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; uint8_t x_366; lean_object* x_367; 
lean_free_object(x_18);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
lean_dec(x_360);
x_364 = lean_box(0);
x_365 = lean_unbox(x_37);
lean_dec(x_37);
x_366 = lean_unbox(x_274);
lean_dec(x_274);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_367 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_276, x_1, x_358, x_3, x_365, x_40, x_366, x_275, x_364, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_363);
lean_dec(x_40);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_19 = x_368;
x_20 = x_369;
goto block_27;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_370 = lean_ctor_get(x_367, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_367, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_372 = x_367;
} else {
 lean_dec_ref(x_367);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; uint8_t x_389; lean_object* x_390; 
x_374 = lean_ctor_get(x_360, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_375 = x_360;
} else {
 lean_dec_ref(x_360);
 x_375 = lean_box(0);
}
lean_inc(x_40);
x_376 = l_Lean_MessageData_ofExpr(x_40);
x_377 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_375)) {
 x_378 = lean_alloc_ctor(7, 2, 0);
} else {
 x_378 = x_375;
 lean_ctor_set_tag(x_378, 7);
}
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_379);
lean_ctor_set(x_18, 0, x_378);
x_380 = lean_ctor_get(x_358, 0);
lean_inc(x_380);
x_381 = l_Lean_MessageData_ofExpr(x_380);
x_382 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_382, 0, x_18);
lean_ctor_set(x_382, 1, x_381);
x_383 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_384 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_359, x_384, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_374);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_unbox(x_37);
lean_dec(x_37);
x_389 = lean_unbox(x_274);
lean_dec(x_274);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_390 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_276, x_1, x_358, x_3, x_388, x_40, x_389, x_275, x_386, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_387);
lean_dec(x_386);
lean_dec(x_40);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_19 = x_391;
x_20 = x_392;
goto block_27;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_393 = lean_ctor_get(x_390, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_390, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_395 = x_390;
} else {
 lean_dec_ref(x_390);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
}
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_28);
lean_dec(x_37);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_397 = lean_ctor_get(x_278, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_278, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_399 = x_278;
} else {
 lean_dec_ref(x_278);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_276);
lean_dec(x_34);
lean_dec(x_31);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_274);
lean_ctor_set(x_401, 1, x_275);
lean_ctor_set(x_29, 1, x_401);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_18);
x_19 = x_402;
x_20 = x_15;
goto block_27;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_403 = lean_ctor_get(x_29, 0);
lean_inc(x_403);
lean_dec(x_29);
x_404 = lean_ctor_get(x_30, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_30, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_406 = x_30;
} else {
 lean_dec_ref(x_30);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_32, 0);
lean_inc(x_407);
lean_dec(x_32);
lean_inc(x_2);
x_408 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_407);
if (x_408 == 0)
{
lean_object* x_409; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_403);
x_409 = l_Lean_Meta_Simp_SimprocEntry_try(x_31, x_34, x_403, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
switch (lean_obj_tag(x_410)) {
case 0:
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
lean_dec(x_406);
lean_free_object(x_28);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
lean_dec(x_410);
x_413 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_414 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_413, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_411);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_unbox(x_415);
lean_dec(x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_free_object(x_18);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
lean_dec(x_414);
x_418 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_419 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_407, x_1, x_405, x_37, x_412, x_404, x_403, x_418, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_417);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_19 = x_420;
x_20 = x_421;
goto block_27;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_422 = lean_ctor_get(x_419, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_426 = lean_ctor_get(x_414, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_427 = x_414;
} else {
 lean_dec_ref(x_414);
 x_427 = lean_box(0);
}
lean_inc(x_403);
x_428 = l_Lean_MessageData_ofExpr(x_403);
x_429 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_427)) {
 x_430 = lean_alloc_ctor(7, 2, 0);
} else {
 x_430 = x_427;
 lean_ctor_set_tag(x_430, 7);
}
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_431);
lean_ctor_set(x_18, 0, x_430);
x_432 = lean_ctor_get(x_412, 0);
lean_inc(x_432);
x_433 = l_Lean_MessageData_ofExpr(x_432);
x_434 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_434, 0, x_18);
lean_ctor_set(x_434, 1, x_433);
x_435 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_436 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
x_437 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_413, x_436, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_426);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_440 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_407, x_1, x_405, x_37, x_412, x_404, x_403, x_438, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_439);
lean_dec(x_438);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_19 = x_441;
x_20 = x_442;
goto block_27;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_443 = lean_ctor_get(x_440, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_440, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_445 = x_440;
} else {
 lean_dec_ref(x_440);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
}
case 1:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
lean_dec(x_406);
lean_free_object(x_28);
x_447 = lean_ctor_get(x_409, 1);
lean_inc(x_447);
lean_dec(x_409);
x_448 = lean_ctor_get(x_410, 0);
lean_inc(x_448);
lean_dec(x_410);
x_449 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_450 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_449, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_447);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_unbox(x_451);
lean_dec(x_451);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_free_object(x_18);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_455 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_407, x_1, x_405, x_37, x_448, x_404, x_403, x_454, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_453);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_19 = x_456;
x_20 = x_457;
goto block_27;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_458 = lean_ctor_get(x_455, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_455, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_460 = x_455;
} else {
 lean_dec_ref(x_455);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_462 = lean_ctor_get(x_450, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_463 = x_450;
} else {
 lean_dec_ref(x_450);
 x_463 = lean_box(0);
}
lean_inc(x_403);
x_464 = l_Lean_MessageData_ofExpr(x_403);
x_465 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_463)) {
 x_466 = lean_alloc_ctor(7, 2, 0);
} else {
 x_466 = x_463;
 lean_ctor_set_tag(x_466, 7);
}
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
x_467 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_467);
lean_ctor_set(x_18, 0, x_466);
x_468 = lean_ctor_get(x_448, 0);
lean_inc(x_468);
x_469 = l_Lean_MessageData_ofExpr(x_468);
x_470 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_470, 0, x_18);
lean_ctor_set(x_470, 1, x_469);
x_471 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_472 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
x_473 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_449, x_472, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_462);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_476 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_407, x_1, x_405, x_37, x_448, x_404, x_403, x_474, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_475);
lean_dec(x_474);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_19 = x_477;
x_20 = x_478;
goto block_27;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_479 = lean_ctor_get(x_476, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_476, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_481 = x_476;
} else {
 lean_dec_ref(x_476);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_480);
return x_482;
}
}
}
default: 
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_410, 0);
lean_inc(x_483);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 x_484 = x_410;
} else {
 lean_dec_ref(x_410);
 x_484 = lean_box(0);
}
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_407);
x_485 = lean_ctor_get(x_409, 1);
lean_inc(x_485);
lean_dec(x_409);
if (lean_is_scalar(x_406)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_406;
}
lean_ctor_set(x_486, 0, x_404);
lean_ctor_set(x_486, 1, x_405);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_403);
lean_ctor_set(x_487, 1, x_486);
lean_ctor_set(x_28, 1, x_487);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
if (lean_is_scalar(x_484)) {
 x_488 = lean_alloc_ctor(1, 1, 0);
} else {
 x_488 = x_484;
 lean_ctor_set_tag(x_488, 1);
}
lean_ctor_set(x_488, 0, x_18);
x_19 = x_488;
x_20 = x_485;
goto block_27;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
lean_dec(x_484);
lean_dec(x_406);
lean_free_object(x_28);
x_489 = lean_ctor_get(x_409, 1);
lean_inc(x_489);
lean_dec(x_409);
x_490 = lean_ctor_get(x_483, 0);
lean_inc(x_490);
lean_dec(x_483);
x_491 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_492 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_491, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_489);
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_unbox(x_493);
lean_dec(x_493);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; uint8_t x_497; uint8_t x_498; lean_object* x_499; 
lean_free_object(x_18);
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
lean_dec(x_492);
x_496 = lean_box(0);
x_497 = lean_unbox(x_37);
lean_dec(x_37);
x_498 = lean_unbox(x_404);
lean_dec(x_404);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_499 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_407, x_1, x_490, x_3, x_497, x_403, x_498, x_405, x_496, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_495);
lean_dec(x_403);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_19 = x_500;
x_20 = x_501;
goto block_27;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_502 = lean_ctor_get(x_499, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_499, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_504 = x_499;
} else {
 lean_dec_ref(x_499);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_504;
}
lean_ctor_set(x_505, 0, x_502);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; uint8_t x_521; lean_object* x_522; 
x_506 = lean_ctor_get(x_492, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_507 = x_492;
} else {
 lean_dec_ref(x_492);
 x_507 = lean_box(0);
}
lean_inc(x_403);
x_508 = l_Lean_MessageData_ofExpr(x_403);
x_509 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_507)) {
 x_510 = lean_alloc_ctor(7, 2, 0);
} else {
 x_510 = x_507;
 lean_ctor_set_tag(x_510, 7);
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_508);
x_511 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_511);
lean_ctor_set(x_18, 0, x_510);
x_512 = lean_ctor_get(x_490, 0);
lean_inc(x_512);
x_513 = l_Lean_MessageData_ofExpr(x_512);
x_514 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_514, 0, x_18);
lean_ctor_set(x_514, 1, x_513);
x_515 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_516 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
x_517 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_491, x_516, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_506);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_520 = lean_unbox(x_37);
lean_dec(x_37);
x_521 = lean_unbox(x_404);
lean_dec(x_404);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_522 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_407, x_1, x_490, x_3, x_520, x_403, x_521, x_405, x_518, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_519);
lean_dec(x_518);
lean_dec(x_403);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_19 = x_523;
x_20 = x_524;
goto block_27;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_525 = lean_ctor_get(x_522, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_522, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_527 = x_522;
} else {
 lean_dec_ref(x_522);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
}
}
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_free_object(x_28);
lean_dec(x_37);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_529 = lean_ctor_get(x_409, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_409, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_531 = x_409;
} else {
 lean_dec_ref(x_409);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_407);
lean_dec(x_34);
lean_dec(x_31);
if (lean_is_scalar(x_406)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_406;
}
lean_ctor_set(x_533, 0, x_404);
lean_ctor_set(x_533, 1, x_405);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_403);
lean_ctor_set(x_534, 1, x_533);
lean_ctor_set(x_28, 1, x_534);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_18);
x_19 = x_535;
x_20 = x_15;
goto block_27;
}
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_536 = lean_ctor_get(x_28, 0);
lean_inc(x_536);
lean_dec(x_28);
x_537 = lean_ctor_get(x_29, 0);
lean_inc(x_537);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_538 = x_29;
} else {
 lean_dec_ref(x_29);
 x_538 = lean_box(0);
}
x_539 = lean_ctor_get(x_30, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_30, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_541 = x_30;
} else {
 lean_dec_ref(x_30);
 x_541 = lean_box(0);
}
x_542 = lean_ctor_get(x_32, 0);
lean_inc(x_542);
lean_dec(x_32);
lean_inc(x_2);
x_543 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_542);
if (x_543 == 0)
{
lean_object* x_544; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_537);
x_544 = l_Lean_Meta_Simp_SimprocEntry_try(x_31, x_34, x_537, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
switch (lean_obj_tag(x_545)) {
case 0:
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; 
lean_dec(x_541);
lean_dec(x_538);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = lean_ctor_get(x_545, 0);
lean_inc(x_547);
lean_dec(x_545);
x_548 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_549 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_548, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_546);
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_unbox(x_550);
lean_dec(x_550);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_free_object(x_18);
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
lean_dec(x_549);
x_553 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_554 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_542, x_1, x_540, x_536, x_547, x_539, x_537, x_553, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_552);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_19 = x_555;
x_20 = x_556;
goto block_27;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_557 = lean_ctor_get(x_554, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_554, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_559 = x_554;
} else {
 lean_dec_ref(x_554);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(1, 2, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_557);
lean_ctor_set(x_560, 1, x_558);
return x_560;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_561 = lean_ctor_get(x_549, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_562 = x_549;
} else {
 lean_dec_ref(x_549);
 x_562 = lean_box(0);
}
lean_inc(x_537);
x_563 = l_Lean_MessageData_ofExpr(x_537);
x_564 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_562)) {
 x_565 = lean_alloc_ctor(7, 2, 0);
} else {
 x_565 = x_562;
 lean_ctor_set_tag(x_565, 7);
}
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_563);
x_566 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_566);
lean_ctor_set(x_18, 0, x_565);
x_567 = lean_ctor_get(x_547, 0);
lean_inc(x_567);
x_568 = l_Lean_MessageData_ofExpr(x_567);
x_569 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_569, 0, x_18);
lean_ctor_set(x_569, 1, x_568);
x_570 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_571 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
x_572 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_548, x_571, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_561);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_575 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_542, x_1, x_540, x_536, x_547, x_539, x_537, x_573, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_574);
lean_dec(x_573);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
lean_dec(x_575);
x_19 = x_576;
x_20 = x_577;
goto block_27;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_578 = lean_ctor_get(x_575, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_575, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_580 = x_575;
} else {
 lean_dec_ref(x_575);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_578);
lean_ctor_set(x_581, 1, x_579);
return x_581;
}
}
}
case 1:
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; 
lean_dec(x_541);
lean_dec(x_538);
x_582 = lean_ctor_get(x_544, 1);
lean_inc(x_582);
lean_dec(x_544);
x_583 = lean_ctor_get(x_545, 0);
lean_inc(x_583);
lean_dec(x_545);
x_584 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_585 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_584, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_582);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_unbox(x_586);
lean_dec(x_586);
if (x_587 == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_free_object(x_18);
x_588 = lean_ctor_get(x_585, 1);
lean_inc(x_588);
lean_dec(x_585);
x_589 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_590 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_542, x_1, x_540, x_536, x_583, x_539, x_537, x_589, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_588);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_19 = x_591;
x_20 = x_592;
goto block_27;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_593 = lean_ctor_get(x_590, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_590, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_595 = x_590;
} else {
 lean_dec_ref(x_590);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_594);
return x_596;
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_597 = lean_ctor_get(x_585, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_598 = x_585;
} else {
 lean_dec_ref(x_585);
 x_598 = lean_box(0);
}
lean_inc(x_537);
x_599 = l_Lean_MessageData_ofExpr(x_537);
x_600 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_598)) {
 x_601 = lean_alloc_ctor(7, 2, 0);
} else {
 x_601 = x_598;
 lean_ctor_set_tag(x_601, 7);
}
lean_ctor_set(x_601, 0, x_600);
lean_ctor_set(x_601, 1, x_599);
x_602 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_602);
lean_ctor_set(x_18, 0, x_601);
x_603 = lean_ctor_get(x_583, 0);
lean_inc(x_603);
x_604 = l_Lean_MessageData_ofExpr(x_603);
x_605 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_605, 0, x_18);
lean_ctor_set(x_605, 1, x_604);
x_606 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_607 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_607, 0, x_605);
lean_ctor_set(x_607, 1, x_606);
x_608 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_584, x_607, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_597);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_611 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_542, x_1, x_540, x_536, x_583, x_539, x_537, x_609, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_610);
lean_dec(x_609);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_19 = x_612;
x_20 = x_613;
goto block_27;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_614 = lean_ctor_get(x_611, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_611, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_616 = x_611;
} else {
 lean_dec_ref(x_611);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
}
}
default: 
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_545, 0);
lean_inc(x_618);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_619 = x_545;
} else {
 lean_dec_ref(x_545);
 x_619 = lean_box(0);
}
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_542);
x_620 = lean_ctor_get(x_544, 1);
lean_inc(x_620);
lean_dec(x_544);
if (lean_is_scalar(x_541)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_541;
}
lean_ctor_set(x_621, 0, x_539);
lean_ctor_set(x_621, 1, x_540);
if (lean_is_scalar(x_538)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_538;
}
lean_ctor_set(x_622, 0, x_537);
lean_ctor_set(x_622, 1, x_621);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_536);
lean_ctor_set(x_623, 1, x_622);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_623);
lean_ctor_set(x_18, 0, x_3);
if (lean_is_scalar(x_619)) {
 x_624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_624 = x_619;
 lean_ctor_set_tag(x_624, 1);
}
lean_ctor_set(x_624, 0, x_18);
x_19 = x_624;
x_20 = x_620;
goto block_27;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
lean_dec(x_619);
lean_dec(x_541);
lean_dec(x_538);
x_625 = lean_ctor_get(x_544, 1);
lean_inc(x_625);
lean_dec(x_544);
x_626 = lean_ctor_get(x_618, 0);
lean_inc(x_626);
lean_dec(x_618);
x_627 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_628 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_627, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_625);
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_unbox(x_629);
lean_dec(x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; uint8_t x_633; uint8_t x_634; lean_object* x_635; 
lean_free_object(x_18);
x_631 = lean_ctor_get(x_628, 1);
lean_inc(x_631);
lean_dec(x_628);
x_632 = lean_box(0);
x_633 = lean_unbox(x_536);
lean_dec(x_536);
x_634 = lean_unbox(x_539);
lean_dec(x_539);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_635 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_542, x_1, x_626, x_3, x_633, x_537, x_634, x_540, x_632, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_631);
lean_dec(x_537);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_19 = x_636;
x_20 = x_637;
goto block_27;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_638 = lean_ctor_get(x_635, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_635, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_640 = x_635;
} else {
 lean_dec_ref(x_635);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(1, 2, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_638);
lean_ctor_set(x_641, 1, x_639);
return x_641;
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; uint8_t x_657; lean_object* x_658; 
x_642 = lean_ctor_get(x_628, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 x_643 = x_628;
} else {
 lean_dec_ref(x_628);
 x_643 = lean_box(0);
}
lean_inc(x_537);
x_644 = l_Lean_MessageData_ofExpr(x_537);
x_645 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_643)) {
 x_646 = lean_alloc_ctor(7, 2, 0);
} else {
 x_646 = x_643;
 lean_ctor_set_tag(x_646, 7);
}
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
x_647 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_647);
lean_ctor_set(x_18, 0, x_646);
x_648 = lean_ctor_get(x_626, 0);
lean_inc(x_648);
x_649 = l_Lean_MessageData_ofExpr(x_648);
x_650 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_650, 0, x_18);
lean_ctor_set(x_650, 1, x_649);
x_651 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_652 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_652, 0, x_650);
lean_ctor_set(x_652, 1, x_651);
x_653 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_627, x_652, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_642);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = lean_unbox(x_536);
lean_dec(x_536);
x_657 = lean_unbox(x_539);
lean_dec(x_539);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_658 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_542, x_1, x_626, x_3, x_656, x_537, x_657, x_540, x_654, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_655);
lean_dec(x_654);
lean_dec(x_537);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
x_19 = x_659;
x_20 = x_660;
goto block_27;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_661 = lean_ctor_get(x_658, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_658, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_663 = x_658;
} else {
 lean_dec_ref(x_658);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
}
}
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_665 = lean_ctor_get(x_544, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_544, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_667 = x_544;
} else {
 lean_dec_ref(x_544);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_542);
lean_dec(x_34);
lean_dec(x_31);
if (lean_is_scalar(x_541)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_541;
}
lean_ctor_set(x_669, 0, x_539);
lean_ctor_set(x_669, 1, x_540);
if (lean_is_scalar(x_538)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_538;
}
lean_ctor_set(x_670, 0, x_537);
lean_ctor_set(x_670, 1, x_669);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_536);
lean_ctor_set(x_671, 1, x_670);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_671);
lean_ctor_set(x_18, 0, x_3);
x_672 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_672, 0, x_18);
x_19 = x_672;
x_20 = x_15;
goto block_27;
}
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; 
x_673 = lean_ctor_get(x_18, 1);
lean_inc(x_673);
lean_dec(x_18);
x_674 = lean_ctor_get(x_28, 0);
lean_inc(x_674);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_675 = x_28;
} else {
 lean_dec_ref(x_28);
 x_675 = lean_box(0);
}
x_676 = lean_ctor_get(x_29, 0);
lean_inc(x_676);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_677 = x_29;
} else {
 lean_dec_ref(x_29);
 x_677 = lean_box(0);
}
x_678 = lean_ctor_get(x_30, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_30, 1);
lean_inc(x_679);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_680 = x_30;
} else {
 lean_dec_ref(x_30);
 x_680 = lean_box(0);
}
x_681 = lean_ctor_get(x_32, 0);
lean_inc(x_681);
lean_dec(x_32);
lean_inc(x_2);
x_682 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_681);
if (x_682 == 0)
{
lean_object* x_683; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_676);
x_683 = l_Lean_Meta_Simp_SimprocEntry_try(x_31, x_673, x_676, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
switch (lean_obj_tag(x_684)) {
case 0:
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; uint8_t x_690; 
lean_dec(x_680);
lean_dec(x_677);
lean_dec(x_675);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec(x_683);
x_686 = lean_ctor_get(x_684, 0);
lean_inc(x_686);
lean_dec(x_684);
x_687 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_688 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_687, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_685);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_unbox(x_689);
lean_dec(x_689);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_688, 1);
lean_inc(x_691);
lean_dec(x_688);
x_692 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_693 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_681, x_1, x_679, x_674, x_686, x_678, x_676, x_692, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_691);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_19 = x_694;
x_20 = x_695;
goto block_27;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_696 = lean_ctor_get(x_693, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_693, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_698 = x_693;
} else {
 lean_dec_ref(x_693);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_697);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_700 = lean_ctor_get(x_688, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_701 = x_688;
} else {
 lean_dec_ref(x_688);
 x_701 = lean_box(0);
}
lean_inc(x_676);
x_702 = l_Lean_MessageData_ofExpr(x_676);
x_703 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_701)) {
 x_704 = lean_alloc_ctor(7, 2, 0);
} else {
 x_704 = x_701;
 lean_ctor_set_tag(x_704, 7);
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_702);
x_705 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
x_706 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
x_707 = lean_ctor_get(x_686, 0);
lean_inc(x_707);
x_708 = l_Lean_MessageData_ofExpr(x_707);
x_709 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_708);
x_710 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_711 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
x_712 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_687, x_711, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_700);
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_715 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_681, x_1, x_679, x_674, x_686, x_678, x_676, x_713, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_714);
lean_dec(x_713);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_19 = x_716;
x_20 = x_717;
goto block_27;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_718 = lean_ctor_get(x_715, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_715, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_720 = x_715;
} else {
 lean_dec_ref(x_715);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_719);
return x_721;
}
}
}
case 1:
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; 
lean_dec(x_680);
lean_dec(x_677);
lean_dec(x_675);
x_722 = lean_ctor_get(x_683, 1);
lean_inc(x_722);
lean_dec(x_683);
x_723 = lean_ctor_get(x_684, 0);
lean_inc(x_723);
lean_dec(x_684);
x_724 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_725 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_724, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_722);
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_unbox(x_726);
lean_dec(x_726);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_725, 1);
lean_inc(x_728);
lean_dec(x_725);
x_729 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_730 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_681, x_1, x_679, x_674, x_723, x_678, x_676, x_729, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_728);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_19 = x_731;
x_20 = x_732;
goto block_27;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_733 = lean_ctor_get(x_730, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_730, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_735 = x_730;
} else {
 lean_dec_ref(x_730);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_737 = lean_ctor_get(x_725, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_738 = x_725;
} else {
 lean_dec_ref(x_725);
 x_738 = lean_box(0);
}
lean_inc(x_676);
x_739 = l_Lean_MessageData_ofExpr(x_676);
x_740 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_738)) {
 x_741 = lean_alloc_ctor(7, 2, 0);
} else {
 x_741 = x_738;
 lean_ctor_set_tag(x_741, 7);
}
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_739);
x_742 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
x_743 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_743, 0, x_741);
lean_ctor_set(x_743, 1, x_742);
x_744 = lean_ctor_get(x_723, 0);
lean_inc(x_744);
x_745 = l_Lean_MessageData_ofExpr(x_744);
x_746 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_746, 0, x_743);
lean_ctor_set(x_746, 1, x_745);
x_747 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_748 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
x_749 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_724, x_748, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_737);
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec(x_749);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_752 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_681, x_1, x_679, x_674, x_723, x_678, x_676, x_750, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_751);
lean_dec(x_750);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
x_19 = x_753;
x_20 = x_754;
goto block_27;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_755 = lean_ctor_get(x_752, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_752, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_757 = x_752;
} else {
 lean_dec_ref(x_752);
 x_757 = lean_box(0);
}
if (lean_is_scalar(x_757)) {
 x_758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_758 = x_757;
}
lean_ctor_set(x_758, 0, x_755);
lean_ctor_set(x_758, 1, x_756);
return x_758;
}
}
}
default: 
{
lean_object* x_759; lean_object* x_760; 
x_759 = lean_ctor_get(x_684, 0);
lean_inc(x_759);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 x_760 = x_684;
} else {
 lean_dec_ref(x_684);
 x_760 = lean_box(0);
}
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_681);
x_761 = lean_ctor_get(x_683, 1);
lean_inc(x_761);
lean_dec(x_683);
if (lean_is_scalar(x_680)) {
 x_762 = lean_alloc_ctor(0, 2, 0);
} else {
 x_762 = x_680;
}
lean_ctor_set(x_762, 0, x_678);
lean_ctor_set(x_762, 1, x_679);
if (lean_is_scalar(x_677)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_677;
}
lean_ctor_set(x_763, 0, x_676);
lean_ctor_set(x_763, 1, x_762);
if (lean_is_scalar(x_675)) {
 x_764 = lean_alloc_ctor(0, 2, 0);
} else {
 x_764 = x_675;
}
lean_ctor_set(x_764, 0, x_674);
lean_ctor_set(x_764, 1, x_763);
lean_inc(x_3);
x_765 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_765, 0, x_3);
lean_ctor_set(x_765, 1, x_764);
if (lean_is_scalar(x_760)) {
 x_766 = lean_alloc_ctor(1, 1, 0);
} else {
 x_766 = x_760;
 lean_ctor_set_tag(x_766, 1);
}
lean_ctor_set(x_766, 0, x_765);
x_19 = x_766;
x_20 = x_761;
goto block_27;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; uint8_t x_772; 
lean_dec(x_760);
lean_dec(x_680);
lean_dec(x_677);
lean_dec(x_675);
x_767 = lean_ctor_get(x_683, 1);
lean_inc(x_767);
lean_dec(x_683);
x_768 = lean_ctor_get(x_759, 0);
lean_inc(x_768);
lean_dec(x_759);
x_769 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_770 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_769, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_767);
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_unbox(x_771);
lean_dec(x_771);
if (x_772 == 0)
{
lean_object* x_773; lean_object* x_774; uint8_t x_775; uint8_t x_776; lean_object* x_777; 
x_773 = lean_ctor_get(x_770, 1);
lean_inc(x_773);
lean_dec(x_770);
x_774 = lean_box(0);
x_775 = lean_unbox(x_674);
lean_dec(x_674);
x_776 = lean_unbox(x_678);
lean_dec(x_678);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_777 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_681, x_1, x_768, x_3, x_775, x_676, x_776, x_679, x_774, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_773);
lean_dec(x_676);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; lean_object* x_779; 
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_19 = x_778;
x_20 = x_779;
goto block_27;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_780 = lean_ctor_get(x_777, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_777, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 lean_ctor_release(x_777, 1);
 x_782 = x_777;
} else {
 lean_dec_ref(x_777);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(1, 2, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_780);
lean_ctor_set(x_783, 1, x_781);
return x_783;
}
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; uint8_t x_799; uint8_t x_800; lean_object* x_801; 
x_784 = lean_ctor_get(x_770, 1);
lean_inc(x_784);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 lean_ctor_release(x_770, 1);
 x_785 = x_770;
} else {
 lean_dec_ref(x_770);
 x_785 = lean_box(0);
}
lean_inc(x_676);
x_786 = l_Lean_MessageData_ofExpr(x_676);
x_787 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_785)) {
 x_788 = lean_alloc_ctor(7, 2, 0);
} else {
 x_788 = x_785;
 lean_ctor_set_tag(x_788, 7);
}
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_786);
x_789 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
x_790 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_790, 0, x_788);
lean_ctor_set(x_790, 1, x_789);
x_791 = lean_ctor_get(x_768, 0);
lean_inc(x_791);
x_792 = l_Lean_MessageData_ofExpr(x_791);
x_793 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_793, 0, x_790);
lean_ctor_set(x_793, 1, x_792);
x_794 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_795 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_795, 0, x_793);
lean_ctor_set(x_795, 1, x_794);
x_796 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_769, x_795, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_784);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec(x_796);
x_799 = lean_unbox(x_674);
lean_dec(x_674);
x_800 = lean_unbox(x_678);
lean_dec(x_678);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_801 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_681, x_1, x_768, x_3, x_799, x_676, x_800, x_679, x_797, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_798);
lean_dec(x_797);
lean_dec(x_676);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
lean_dec(x_801);
x_19 = x_802;
x_20 = x_803;
goto block_27;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_804 = lean_ctor_get(x_801, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_801, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_806 = x_801;
} else {
 lean_dec_ref(x_801);
 x_806 = lean_box(0);
}
if (lean_is_scalar(x_806)) {
 x_807 = lean_alloc_ctor(1, 2, 0);
} else {
 x_807 = x_806;
}
lean_ctor_set(x_807, 0, x_804);
lean_ctor_set(x_807, 1, x_805);
return x_807;
}
}
}
}
}
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_681);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_677);
lean_dec(x_676);
lean_dec(x_675);
lean_dec(x_674);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_808 = lean_ctor_get(x_683, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_683, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_810 = x_683;
} else {
 lean_dec_ref(x_683);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(1, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_808);
lean_ctor_set(x_811, 1, x_809);
return x_811;
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_681);
lean_dec(x_673);
lean_dec(x_31);
if (lean_is_scalar(x_680)) {
 x_812 = lean_alloc_ctor(0, 2, 0);
} else {
 x_812 = x_680;
}
lean_ctor_set(x_812, 0, x_678);
lean_ctor_set(x_812, 1, x_679);
if (lean_is_scalar(x_677)) {
 x_813 = lean_alloc_ctor(0, 2, 0);
} else {
 x_813 = x_677;
}
lean_ctor_set(x_813, 0, x_676);
lean_ctor_set(x_813, 1, x_812);
if (lean_is_scalar(x_675)) {
 x_814 = lean_alloc_ctor(0, 2, 0);
} else {
 x_814 = x_675;
}
lean_ctor_set(x_814, 0, x_674);
lean_ctor_set(x_814, 1, x_813);
lean_inc(x_3);
x_815 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_815, 0, x_3);
lean_ctor_set(x_815, 1, x_814);
x_816 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_816, 0, x_815);
x_19 = x_816;
x_20 = x_15;
goto block_27;
}
}
block_27:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_6 = x_25;
x_7 = x_23;
x_15 = x_20;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (x_1 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simprocCore___lambda__2___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_simprocCore___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-simprocs found for ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_simprocCore___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pre", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("post", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Meta_Simp_getConfig___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = l_Lean_Meta_Simp_getDtConfig(x_14);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_18 = l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(x_2, x_4, x_17, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_isEmpty___rarg(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Simp_simprocCore___closed__1;
if (lean_is_scalar(x_16)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_16;
}
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_size(x_19);
x_30 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1(x_1, x_3, x_22, x_19, x_29, x_30, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = lean_unbox(x_40);
lean_dec(x_40);
x_44 = lean_unbox(x_38);
lean_dec(x_38);
x_45 = l_Lean_Meta_Simp_simprocCore___lambda__1(x_43, x_22, x_39, x_41, x_44, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_31, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
lean_dec(x_36);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_31);
if (x_52 == 0)
{
return x_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_31, 0);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_31);
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
lean_dec(x_19);
lean_dec(x_3);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
if (x_1 == 0)
{
lean_object* x_98; 
x_98 = l_Lean_Meta_Simp_simprocCore___closed__7;
x_57 = x_98;
goto block_97;
}
else
{
lean_object* x_99; 
x_99 = l_Lean_Meta_Simp_simprocCore___closed__8;
x_57 = x_99;
goto block_97;
}
block_97:
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = l_Lean_Meta_Simp_simprocCore___closed__2;
x_63 = lean_unbox(x_60);
lean_dec(x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_free_object(x_58);
lean_dec(x_57);
lean_dec(x_16);
lean_dec(x_4);
x_64 = lean_box(0);
x_65 = lean_apply_9(x_62, x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_67 = l_Lean_Meta_Simp_simprocCore___closed__4;
lean_ctor_set_tag(x_58, 7);
lean_ctor_set(x_58, 1, x_66);
lean_ctor_set(x_58, 0, x_67);
x_68 = l_Lean_Meta_Simp_simprocCore___closed__6;
if (lean_is_scalar(x_16)) {
 x_69 = lean_alloc_ctor(7, 2, 0);
} else {
 x_69 = x_16;
 lean_ctor_set_tag(x_69, 7);
}
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_MessageData_ofExpr(x_4);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_56, x_73, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_apply_9(x_62, x_75, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_58, 0);
x_79 = lean_ctor_get(x_58, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_58);
x_80 = l_Lean_Meta_Simp_simprocCore___closed__2;
x_81 = lean_unbox(x_78);
lean_dec(x_78);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_57);
lean_dec(x_16);
lean_dec(x_4);
x_82 = lean_box(0);
x_83 = lean_apply_9(x_80, x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_85 = l_Lean_Meta_Simp_simprocCore___closed__4;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_Meta_Simp_simprocCore___closed__6;
if (lean_is_scalar(x_16)) {
 x_88 = lean_alloc_ctor(7, 2, 0);
} else {
 x_88 = x_16;
 lean_ctor_set_tag(x_88, 7);
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_MessageData_ofExpr(x_4);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_56, x_92, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_apply_9(x_80, x_94, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_95);
return x_96;
}
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_18);
if (x_100 == 0)
{
return x_18;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_18, 0);
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_18);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = lean_unbox(x_7);
lean_dec(x_7);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___lambda__3(x_1, x_18, x_3, x_4, x_19, x_6, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1(x_16, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Meta_Simp_simprocCore___lambda__1(x_15, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simprocCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_simprocCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
x_17 = l_Lean_Meta_Simp_recordSimpTheorem(x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_3);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_3);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
x_17 = l_Lean_Meta_Simp_recordSimpTheorem(x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_3);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_16);
x_18 = l_Lean_Meta_Simp_recordSimpTheorem(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_18 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
lean_inc(x_2);
x_38 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_35);
x_39 = l_Lean_Meta_Simp_SimprocEntry_tryD(x_29, x_32, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
switch (lean_obj_tag(x_40)) {
case 0:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_free_object(x_28);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_44 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_18);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_37, x_1, x_42, x_35, x_36, x_48, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_19 = x_50;
x_20 = x_51;
goto block_27;
}
else
{
uint8_t x_52; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_44);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_44, 1);
x_58 = lean_ctor_get(x_44, 0);
lean_dec(x_58);
lean_inc(x_35);
x_59 = l_Lean_MessageData_ofExpr(x_35);
x_60 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_59);
lean_ctor_set(x_44, 0, x_60);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_61);
lean_ctor_set(x_18, 0, x_44);
lean_inc(x_42);
x_62 = l_Lean_MessageData_ofExpr(x_42);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_18);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_43, x_65, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_57);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_37, x_1, x_42, x_35, x_36, x_67, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_68);
lean_dec(x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_19 = x_70;
x_20 = x_71;
goto block_27;
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
lean_dec(x_44);
lean_inc(x_35);
x_77 = l_Lean_MessageData_ofExpr(x_35);
x_78 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_80);
lean_ctor_set(x_18, 0, x_79);
lean_inc(x_42);
x_81 = l_Lean_MessageData_ofExpr(x_42);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_18);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_43, x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_76);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_37, x_1, x_42, x_35, x_36, x_86, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_87);
lean_dec(x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_19 = x_89;
x_20 = x_90;
goto block_27;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
case 1:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_free_object(x_28);
x_95 = lean_ctor_get(x_39, 1);
lean_inc(x_95);
lean_dec(x_39);
x_96 = lean_ctor_get(x_40, 0);
lean_inc(x_96);
lean_dec(x_40);
x_97 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_98 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_97, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_95);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_18);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_103 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_37, x_1, x_96, x_35, x_36, x_102, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_19 = x_104;
x_20 = x_105;
goto block_27;
}
else
{
uint8_t x_106; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_98);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_111 = lean_ctor_get(x_98, 1);
x_112 = lean_ctor_get(x_98, 0);
lean_dec(x_112);
lean_inc(x_35);
x_113 = l_Lean_MessageData_ofExpr(x_35);
x_114 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
lean_ctor_set_tag(x_98, 7);
lean_ctor_set(x_98, 1, x_113);
lean_ctor_set(x_98, 0, x_114);
x_115 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_115);
lean_ctor_set(x_18, 0, x_98);
lean_inc(x_96);
x_116 = l_Lean_MessageData_ofExpr(x_96);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_18);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_97, x_119, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_111);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_123 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_37, x_1, x_96, x_35, x_36, x_121, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_122);
lean_dec(x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_19 = x_124;
x_20 = x_125;
goto block_27;
}
else
{
uint8_t x_126; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_123);
if (x_126 == 0)
{
return x_123;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_123, 0);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_123);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_130 = lean_ctor_get(x_98, 1);
lean_inc(x_130);
lean_dec(x_98);
lean_inc(x_35);
x_131 = l_Lean_MessageData_ofExpr(x_35);
x_132 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_134);
lean_ctor_set(x_18, 0, x_133);
lean_inc(x_96);
x_135 = l_Lean_MessageData_ofExpr(x_96);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_18);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_97, x_138, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_130);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_142 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_37, x_1, x_96, x_35, x_36, x_140, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_141);
lean_dec(x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_19 = x_143;
x_20 = x_144;
goto block_27;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
default: 
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_40);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_dec(x_37);
x_151 = lean_ctor_get(x_39, 1);
lean_inc(x_151);
lean_dec(x_39);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_18);
x_19 = x_40;
x_20 = x_151;
goto block_27;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_free_object(x_40);
lean_free_object(x_28);
x_152 = lean_ctor_get(x_39, 1);
lean_inc(x_152);
lean_dec(x_39);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
x_154 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_155 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_154, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_152);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; 
lean_free_object(x_18);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = lean_box(0);
x_160 = lean_unbox(x_36);
lean_dec(x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_161 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_37, x_1, x_153, x_3, x_35, x_160, x_159, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_158);
lean_dec(x_35);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_19 = x_162;
x_20 = x_163;
goto block_27;
}
else
{
uint8_t x_164; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_161, 0);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_161);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_155);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; 
x_169 = lean_ctor_get(x_155, 1);
x_170 = lean_ctor_get(x_155, 0);
lean_dec(x_170);
lean_inc(x_35);
x_171 = l_Lean_MessageData_ofExpr(x_35);
x_172 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
lean_ctor_set_tag(x_155, 7);
lean_ctor_set(x_155, 1, x_171);
lean_ctor_set(x_155, 0, x_172);
x_173 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_173);
lean_ctor_set(x_18, 0, x_155);
lean_inc(x_153);
x_174 = l_Lean_MessageData_ofExpr(x_153);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_18);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_154, x_177, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_169);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_unbox(x_36);
lean_dec(x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_182 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_37, x_1, x_153, x_3, x_35, x_181, x_179, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_180);
lean_dec(x_179);
lean_dec(x_35);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_19 = x_183;
x_20 = x_184;
goto block_27;
}
else
{
uint8_t x_185; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
return x_182;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_182, 0);
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_182);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_189 = lean_ctor_get(x_155, 1);
lean_inc(x_189);
lean_dec(x_155);
lean_inc(x_35);
x_190 = l_Lean_MessageData_ofExpr(x_35);
x_191 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_193);
lean_ctor_set(x_18, 0, x_192);
lean_inc(x_153);
x_194 = l_Lean_MessageData_ofExpr(x_153);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_18);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_154, x_197, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_189);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_unbox(x_36);
lean_dec(x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_202 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_37, x_1, x_153, x_3, x_35, x_201, x_199, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_200);
lean_dec(x_199);
lean_dec(x_35);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_19 = x_203;
x_20 = x_204;
goto block_27;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_202, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_207 = x_202;
} else {
 lean_dec_ref(x_202);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_40, 0);
lean_inc(x_209);
lean_dec(x_40);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_37);
x_210 = lean_ctor_get(x_39, 1);
lean_inc(x_210);
lean_dec(x_39);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_18);
x_19 = x_211;
x_20 = x_210;
goto block_27;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_free_object(x_28);
x_212 = lean_ctor_get(x_39, 1);
lean_inc(x_212);
lean_dec(x_39);
x_213 = lean_ctor_get(x_209, 0);
lean_inc(x_213);
lean_dec(x_209);
x_214 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_215 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_214, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_212);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; 
lean_free_object(x_18);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
x_219 = lean_box(0);
x_220 = lean_unbox(x_36);
lean_dec(x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_221 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_37, x_1, x_213, x_3, x_35, x_220, x_219, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_218);
lean_dec(x_35);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_19 = x_222;
x_20 = x_223;
goto block_27;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_226 = x_221;
} else {
 lean_dec_ref(x_221);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_228 = lean_ctor_get(x_215, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_229 = x_215;
} else {
 lean_dec_ref(x_215);
 x_229 = lean_box(0);
}
lean_inc(x_35);
x_230 = l_Lean_MessageData_ofExpr(x_35);
x_231 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_229)) {
 x_232 = lean_alloc_ctor(7, 2, 0);
} else {
 x_232 = x_229;
 lean_ctor_set_tag(x_232, 7);
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_233);
lean_ctor_set(x_18, 0, x_232);
lean_inc(x_213);
x_234 = l_Lean_MessageData_ofExpr(x_213);
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_18);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_214, x_237, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_228);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_unbox(x_36);
lean_dec(x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_242 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_37, x_1, x_213, x_3, x_35, x_241, x_239, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_240);
lean_dec(x_239);
lean_dec(x_35);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_19 = x_243;
x_20 = x_244;
goto block_27;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_247 = x_242;
} else {
 lean_dec_ref(x_242);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
}
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_37);
lean_free_object(x_28);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_249 = !lean_is_exclusive(x_39);
if (x_249 == 0)
{
return x_39;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_39, 0);
x_251 = lean_ctor_get(x_39, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_39);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
lean_object* x_253; 
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_29);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_3);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_18);
x_19 = x_253;
x_20 = x_15;
goto block_27;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = lean_ctor_get(x_28, 0);
x_255 = lean_ctor_get(x_28, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_28);
x_256 = lean_ctor_get(x_30, 0);
lean_inc(x_256);
lean_dec(x_30);
lean_inc(x_2);
x_257 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_256);
if (x_257 == 0)
{
lean_object* x_258; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_254);
x_258 = l_Lean_Meta_Simp_SimprocEntry_tryD(x_29, x_32, x_254, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
switch (lean_obj_tag(x_259)) {
case 0:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_263 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_262, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_260);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_unbox(x_264);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_free_object(x_18);
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
lean_dec(x_263);
x_267 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_268 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_256, x_1, x_261, x_254, x_255, x_267, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_19 = x_269;
x_20 = x_270;
goto block_27;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_271 = lean_ctor_get(x_268, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_268, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_273 = x_268;
} else {
 lean_dec_ref(x_268);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_275 = lean_ctor_get(x_263, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_276 = x_263;
} else {
 lean_dec_ref(x_263);
 x_276 = lean_box(0);
}
lean_inc(x_254);
x_277 = l_Lean_MessageData_ofExpr(x_254);
x_278 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_276)) {
 x_279 = lean_alloc_ctor(7, 2, 0);
} else {
 x_279 = x_276;
 lean_ctor_set_tag(x_279, 7);
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_280);
lean_ctor_set(x_18, 0, x_279);
lean_inc(x_261);
x_281 = l_Lean_MessageData_ofExpr(x_261);
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_18);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_284 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_262, x_284, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_275);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_288 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_256, x_1, x_261, x_254, x_255, x_286, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_287);
lean_dec(x_286);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_19 = x_289;
x_20 = x_290;
goto block_27;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_291 = lean_ctor_get(x_288, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_293 = x_288;
} else {
 lean_dec_ref(x_288);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
case 1:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_295 = lean_ctor_get(x_258, 1);
lean_inc(x_295);
lean_dec(x_258);
x_296 = lean_ctor_get(x_259, 0);
lean_inc(x_296);
lean_dec(x_259);
x_297 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_298 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_297, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_295);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_free_object(x_18);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_303 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_256, x_1, x_296, x_254, x_255, x_302, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_301);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_19 = x_304;
x_20 = x_305;
goto block_27;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_306 = lean_ctor_get(x_303, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_303, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_308 = x_303;
} else {
 lean_dec_ref(x_303);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_310 = lean_ctor_get(x_298, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_311 = x_298;
} else {
 lean_dec_ref(x_298);
 x_311 = lean_box(0);
}
lean_inc(x_254);
x_312 = l_Lean_MessageData_ofExpr(x_254);
x_313 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_311)) {
 x_314 = lean_alloc_ctor(7, 2, 0);
} else {
 x_314 = x_311;
 lean_ctor_set_tag(x_314, 7);
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_312);
x_315 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_315);
lean_ctor_set(x_18, 0, x_314);
lean_inc(x_296);
x_316 = l_Lean_MessageData_ofExpr(x_296);
x_317 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_317, 0, x_18);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_319 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_297, x_319, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_310);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_323 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_256, x_1, x_296, x_254, x_255, x_321, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_322);
lean_dec(x_321);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_19 = x_324;
x_20 = x_325;
goto block_27;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_328 = x_323;
} else {
 lean_dec_ref(x_323);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
}
default: 
{
lean_object* x_330; lean_object* x_331; 
x_330 = lean_ctor_get(x_259, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_331 = x_259;
} else {
 lean_dec_ref(x_259);
 x_331 = lean_box(0);
}
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_256);
x_332 = lean_ctor_get(x_258, 1);
lean_inc(x_332);
lean_dec(x_258);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_254);
lean_ctor_set(x_333, 1, x_255);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_333);
lean_ctor_set(x_18, 0, x_3);
if (lean_is_scalar(x_331)) {
 x_334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_334 = x_331;
 lean_ctor_set_tag(x_334, 1);
}
lean_ctor_set(x_334, 0, x_18);
x_19 = x_334;
x_20 = x_332;
goto block_27;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
lean_dec(x_331);
x_335 = lean_ctor_get(x_258, 1);
lean_inc(x_335);
lean_dec(x_258);
x_336 = lean_ctor_get(x_330, 0);
lean_inc(x_336);
lean_dec(x_330);
x_337 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_338 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_337, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_335);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_unbox(x_339);
lean_dec(x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; 
lean_free_object(x_18);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec(x_338);
x_342 = lean_box(0);
x_343 = lean_unbox(x_255);
lean_dec(x_255);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_344 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_256, x_1, x_336, x_3, x_254, x_343, x_342, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_341);
lean_dec(x_254);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_19 = x_345;
x_20 = x_346;
goto block_27;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_344, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_349 = x_344;
} else {
 lean_dec_ref(x_344);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; 
x_351 = lean_ctor_get(x_338, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_352 = x_338;
} else {
 lean_dec_ref(x_338);
 x_352 = lean_box(0);
}
lean_inc(x_254);
x_353 = l_Lean_MessageData_ofExpr(x_254);
x_354 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_352)) {
 x_355 = lean_alloc_ctor(7, 2, 0);
} else {
 x_355 = x_352;
 lean_ctor_set_tag(x_355, 7);
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_353);
x_356 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_356);
lean_ctor_set(x_18, 0, x_355);
lean_inc(x_336);
x_357 = l_Lean_MessageData_ofExpr(x_336);
x_358 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_358, 0, x_18);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_360 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_337, x_360, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_351);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = lean_unbox(x_255);
lean_dec(x_255);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_365 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_256, x_1, x_336, x_3, x_254, x_364, x_362, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_363);
lean_dec(x_362);
lean_dec(x_254);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_19 = x_366;
x_20 = x_367;
goto block_27;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_368 = lean_ctor_get(x_365, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_365, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_370 = x_365;
} else {
 lean_dec_ref(x_365);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
}
}
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_372 = lean_ctor_get(x_258, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_258, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_374 = x_258;
} else {
 lean_dec_ref(x_258);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; 
lean_dec(x_256);
lean_dec(x_32);
lean_dec(x_29);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_254);
lean_ctor_set(x_376, 1, x_255);
lean_inc(x_3);
lean_ctor_set(x_18, 1, x_376);
lean_ctor_set(x_18, 0, x_3);
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_18);
x_19 = x_377;
x_20 = x_15;
goto block_27;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_378 = lean_ctor_get(x_18, 1);
lean_inc(x_378);
lean_dec(x_18);
x_379 = lean_ctor_get(x_28, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_28, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_381 = x_28;
} else {
 lean_dec_ref(x_28);
 x_381 = lean_box(0);
}
x_382 = lean_ctor_get(x_30, 0);
lean_inc(x_382);
lean_dec(x_30);
lean_inc(x_2);
x_383 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_2, x_382);
if (x_383 == 0)
{
lean_object* x_384; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_379);
x_384 = l_Lean_Meta_Simp_SimprocEntry_tryD(x_29, x_378, x_379, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
switch (lean_obj_tag(x_385)) {
case 0:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
lean_dec(x_381);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_ctor_get(x_385, 0);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_389 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_388, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_386);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_unbox(x_390);
lean_dec(x_390);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_393 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_394 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_382, x_1, x_387, x_379, x_380, x_393, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_392);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_19 = x_395;
x_20 = x_396;
goto block_27;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_399 = x_394;
} else {
 lean_dec_ref(x_394);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_401 = lean_ctor_get(x_389, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_402 = x_389;
} else {
 lean_dec_ref(x_389);
 x_402 = lean_box(0);
}
lean_inc(x_379);
x_403 = l_Lean_MessageData_ofExpr(x_379);
x_404 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_402)) {
 x_405 = lean_alloc_ctor(7, 2, 0);
} else {
 x_405 = x_402;
 lean_ctor_set_tag(x_405, 7);
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_403);
x_406 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
x_407 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
lean_inc(x_387);
x_408 = l_Lean_MessageData_ofExpr(x_387);
x_409 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_411 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_388, x_411, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_401);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_415 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_382, x_1, x_387, x_379, x_380, x_413, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_414);
lean_dec(x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_19 = x_416;
x_20 = x_417;
goto block_27;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
}
case 1:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_381);
x_422 = lean_ctor_get(x_384, 1);
lean_inc(x_422);
lean_dec(x_384);
x_423 = lean_ctor_get(x_385, 0);
lean_inc(x_423);
lean_dec(x_385);
x_424 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_425 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_424, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_422);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_unbox(x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_428);
lean_dec(x_425);
x_429 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_430 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_382, x_1, x_423, x_379, x_380, x_429, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_428);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_19 = x_431;
x_20 = x_432;
goto block_27;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_433 = lean_ctor_get(x_430, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_430, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_435 = x_430;
} else {
 lean_dec_ref(x_430);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_437 = lean_ctor_get(x_425, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_438 = x_425;
} else {
 lean_dec_ref(x_425);
 x_438 = lean_box(0);
}
lean_inc(x_379);
x_439 = l_Lean_MessageData_ofExpr(x_379);
x_440 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_438)) {
 x_441 = lean_alloc_ctor(7, 2, 0);
} else {
 x_441 = x_438;
 lean_ctor_set_tag(x_441, 7);
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_439);
x_442 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
lean_inc(x_423);
x_444 = l_Lean_MessageData_ofExpr(x_423);
x_445 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_447 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
x_448 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_424, x_447, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_437);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_451 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_382, x_1, x_423, x_379, x_380, x_449, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_450);
lean_dec(x_449);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_19 = x_452;
x_20 = x_453;
goto block_27;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_454 = lean_ctor_get(x_451, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_451, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_456 = x_451;
} else {
 lean_dec_ref(x_451);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
}
default: 
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_385, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_459 = x_385;
} else {
 lean_dec_ref(x_385);
 x_459 = lean_box(0);
}
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_382);
x_460 = lean_ctor_get(x_384, 1);
lean_inc(x_460);
lean_dec(x_384);
if (lean_is_scalar(x_381)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_381;
}
lean_ctor_set(x_461, 0, x_379);
lean_ctor_set(x_461, 1, x_380);
lean_inc(x_3);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_3);
lean_ctor_set(x_462, 1, x_461);
if (lean_is_scalar(x_459)) {
 x_463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_463 = x_459;
 lean_ctor_set_tag(x_463, 1);
}
lean_ctor_set(x_463, 0, x_462);
x_19 = x_463;
x_20 = x_460;
goto block_27;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
lean_dec(x_459);
lean_dec(x_381);
x_464 = lean_ctor_get(x_384, 1);
lean_inc(x_464);
lean_dec(x_384);
x_465 = lean_ctor_get(x_458, 0);
lean_inc(x_465);
lean_dec(x_458);
x_466 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
x_467 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_466, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_464);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_unbox(x_468);
lean_dec(x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec(x_467);
x_471 = lean_box(0);
x_472 = lean_unbox(x_380);
lean_dec(x_380);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_473 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_382, x_1, x_465, x_3, x_379, x_472, x_471, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_470);
lean_dec(x_379);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_19 = x_474;
x_20 = x_475;
goto block_27;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_476 = lean_ctor_get(x_473, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_478 = x_473;
} else {
 lean_dec_ref(x_473);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; 
x_480 = lean_ctor_get(x_467, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_481 = x_467;
} else {
 lean_dec_ref(x_467);
 x_481 = lean_box(0);
}
lean_inc(x_379);
x_482 = l_Lean_MessageData_ofExpr(x_379);
x_483 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6;
if (lean_is_scalar(x_481)) {
 x_484 = lean_alloc_ctor(7, 2, 0);
} else {
 x_484 = x_481;
 lean_ctor_set_tag(x_484, 7);
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8;
x_486 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
lean_inc(x_465);
x_487 = l_Lean_MessageData_ofExpr(x_465);
x_488 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_489 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_490 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_466, x_490, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_480);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
x_494 = lean_unbox(x_380);
lean_dec(x_380);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_495 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_382, x_1, x_465, x_3, x_379, x_494, x_492, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_493);
lean_dec(x_492);
lean_dec(x_379);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_19 = x_496;
x_20 = x_497;
goto block_27;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_498 = lean_ctor_get(x_495, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_495, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_500 = x_495;
} else {
 lean_dec_ref(x_495);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_499);
return x_501;
}
}
}
}
}
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_379);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_502 = lean_ctor_get(x_384, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_384, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_504 = x_384;
} else {
 lean_dec_ref(x_384);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_504;
}
lean_ctor_set(x_505, 0, x_502);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_382);
lean_dec(x_378);
lean_dec(x_29);
if (lean_is_scalar(x_381)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_381;
}
lean_ctor_set(x_506, 0, x_379);
lean_ctor_set(x_506, 1, x_380);
lean_inc(x_3);
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_3);
lean_ctor_set(x_507, 1, x_506);
x_508 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_508, 0, x_507);
x_19 = x_508;
x_20 = x_15;
goto block_27;
}
}
block_27:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_6 = x_25;
x_7 = x_23;
x_15 = x_20;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dsimprocCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dsimprocCore___lambda__2___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Meta_Simp_getConfig___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = l_Lean_Meta_Simp_getDtConfig(x_14);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_18 = l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(x_2, x_4, x_17, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_isEmpty___rarg(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_22 = lean_box(0);
x_23 = 0;
x_24 = lean_box(x_23);
if (lean_is_scalar(x_16)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_16;
}
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_array_size(x_19);
x_28 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1(x_1, x_3, x_22, x_19, x_27, x_28, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = l_Lean_Meta_Simp_dsimprocCore___lambda__1(x_37, x_22, x_34, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_29, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_41);
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_19);
lean_dec(x_3);
x_49 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4;
if (x_1 == 0)
{
lean_object* x_91; 
x_91 = l_Lean_Meta_Simp_simprocCore___closed__7;
x_50 = x_91;
goto block_90;
}
else
{
lean_object* x_92; 
x_92 = l_Lean_Meta_Simp_simprocCore___closed__8;
x_50 = x_92;
goto block_90;
}
block_90:
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = l_Lean_Meta_Simp_dsimprocCore___closed__1;
x_56 = lean_unbox(x_53);
lean_dec(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_51);
lean_dec(x_50);
lean_dec(x_16);
lean_dec(x_4);
x_57 = lean_box(0);
x_58 = lean_apply_9(x_55, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_60 = l_Lean_Meta_Simp_simprocCore___closed__4;
lean_ctor_set_tag(x_51, 7);
lean_ctor_set(x_51, 1, x_59);
lean_ctor_set(x_51, 0, x_60);
x_61 = l_Lean_Meta_Simp_simprocCore___closed__6;
if (lean_is_scalar(x_16)) {
 x_62 = lean_alloc_ctor(7, 2, 0);
} else {
 x_62 = x_16;
 lean_ctor_set_tag(x_62, 7);
}
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_MessageData_ofExpr(x_4);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_49, x_66, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_apply_9(x_55, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_51, 0);
x_72 = lean_ctor_get(x_51, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_51);
x_73 = l_Lean_Meta_Simp_dsimprocCore___closed__1;
x_74 = lean_unbox(x_71);
lean_dec(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_50);
lean_dec(x_16);
lean_dec(x_4);
x_75 = lean_box(0);
x_76 = lean_apply_9(x_73, x_75, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_78 = l_Lean_Meta_Simp_simprocCore___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Meta_Simp_simprocCore___closed__6;
if (lean_is_scalar(x_16)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_16;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofExpr(x_4);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_49, x_85, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_72);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_apply_9(x_73, x_87, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_88);
return x_89;
}
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_18);
if (x_93 == 0)
{
return x_18;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_18, 0);
x_95 = lean_ctor_get(x_18, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_18);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___lambda__3(x_1, x_16, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocCore___spec__1(x_16, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_dsimprocCore___lambda__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_dsimprocCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_dsimprocCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___rarg(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_1, x_9);
x_13 = lean_box(0);
x_14 = lean_array_fset(x_1, x_9, x_13);
x_15 = l_Lean_Meta_Simp_Simprocs_add(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_fset(x_14, x_9, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_array_fset(x_14, x_9, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_14);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2;
x_28 = l_Lean_Meta_Simp_Simprocs_add(x_27, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_mk(x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_mk(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_Simp_SimprocsArray_add(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_SimprocsArray_erase___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_Simp_Simprocs_erase(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_SimprocsArray_erase___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_SimprocsArray_erase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_SimprocsArray_erase___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_SimprocsArray_isErased___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_7, x_1);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocsArray_isErased(lean_object* x_1, lean_object* x_2) {
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
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_SimprocsArray_isErased___spec__1(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_SimprocsArray_isErased___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_SimprocsArray_isErased___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_isErased___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_SimprocsArray_isErased(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocArrayCore___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_17 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_33 = x_28;
} else {
 lean_dec_ref(x_28);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_17, 3);
lean_inc(x_37);
if (x_1 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_17, 0);
lean_inc(x_170);
lean_dec(x_17);
x_38 = x_170;
goto block_169;
}
else
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_17, 1);
lean_inc(x_171);
lean_dec(x_17);
x_38 = x_171;
goto block_169;
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_14 = x_19;
goto _start;
}
}
block_169:
{
lean_object* x_39; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_39 = l_Lean_Meta_Simp_simprocCore(x_1, x_38, x_37, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
switch (lean_obj_tag(x_40)) {
case 0:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_unbox(x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_45 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_35, x_44, x_43, x_10, x_11, x_12, x_13, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_ctor_set(x_40, 0, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_40);
if (lean_is_scalar(x_36)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_36;
}
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_35);
if (lean_is_scalar(x_33)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_33;
}
lean_ctor_set(x_50, 0, x_32);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_31)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_31;
}
lean_ctor_set(x_51, 0, x_30);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_18 = x_53;
x_19 = x_47;
goto block_26;
}
else
{
uint8_t x_54; 
lean_free_object(x_40);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_unbox(x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_60 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_35, x_59, x_58, x_10, x_11, x_12, x_13, x_41);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_36)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_36;
}
lean_ctor_set(x_65, 0, x_34);
lean_ctor_set(x_65, 1, x_35);
if (lean_is_scalar(x_33)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_33;
}
lean_ctor_set(x_66, 0, x_32);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_31)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_31;
}
lean_ctor_set(x_67, 0, x_30);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_18 = x_69;
x_19 = x_62;
goto block_26;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_72 = x_60;
} else {
 lean_dec_ref(x_60);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
case 1:
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_39, 1);
lean_inc(x_74);
lean_dec(x_39);
x_75 = !lean_is_exclusive(x_40);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_40, 0);
x_77 = lean_unbox(x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_78 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_35, x_77, x_76, x_10, x_11, x_12, x_13, x_74);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_ctor_set(x_40, 0, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_40);
if (lean_is_scalar(x_36)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_36;
}
lean_ctor_set(x_82, 0, x_34);
lean_ctor_set(x_82, 1, x_35);
if (lean_is_scalar(x_33)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_33;
}
lean_ctor_set(x_83, 0, x_32);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_31)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_31;
}
lean_ctor_set(x_84, 0, x_30);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_18 = x_86;
x_19 = x_80;
goto block_26;
}
else
{
uint8_t x_87; 
lean_free_object(x_40);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_78);
if (x_87 == 0)
{
return x_78;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_78, 0);
x_89 = lean_ctor_get(x_78, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_78);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_40, 0);
lean_inc(x_91);
lean_dec(x_40);
x_92 = lean_unbox(x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_93 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_35, x_92, x_91, x_10, x_11, x_12, x_13, x_74);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_36)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_36;
}
lean_ctor_set(x_98, 0, x_34);
lean_ctor_set(x_98, 1, x_35);
if (lean_is_scalar(x_33)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_33;
}
lean_ctor_set(x_99, 0, x_32);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_31)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_31;
}
lean_ctor_set(x_100, 0, x_30);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_18 = x_102;
x_19 = x_95;
goto block_26;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_103 = lean_ctor_get(x_93, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_105 = x_93;
} else {
 lean_dec_ref(x_93);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
default: 
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_40, 0);
lean_inc(x_107);
lean_dec(x_40);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_39, 1);
lean_inc(x_108);
lean_dec(x_39);
if (lean_is_scalar(x_36)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_36;
}
lean_ctor_set(x_109, 0, x_34);
lean_ctor_set(x_109, 1, x_35);
if (lean_is_scalar(x_33)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_33;
}
lean_ctor_set(x_110, 0, x_32);
lean_ctor_set(x_110, 1, x_109);
if (lean_is_scalar(x_31)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_31;
}
lean_ctor_set(x_111, 0, x_30);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_2);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_18 = x_113;
x_19 = x_108;
goto block_26;
}
else
{
uint8_t x_114; 
lean_dec(x_34);
lean_dec(x_32);
x_114 = !lean_is_exclusive(x_107);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_39, 1);
lean_inc(x_116);
lean_dec(x_39);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_115, sizeof(void*)*2);
lean_dec(x_115);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_120 = l_Lean_Meta_mkEqTrans_x3f(x_35, x_118, x_10, x_11, x_12, x_13, x_116);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = 1;
x_124 = lean_box(x_123);
if (lean_is_scalar(x_36)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_36;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
if (lean_is_scalar(x_33)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_33;
}
lean_ctor_set(x_126, 0, x_117);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_unbox(x_30);
lean_dec(x_30);
if (x_127 == 0)
{
uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = 0;
x_129 = lean_box(x_128);
if (lean_is_scalar(x_31)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_31;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
lean_inc(x_2);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_2);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_107, 0, x_131);
x_18 = x_107;
x_19 = x_122;
goto block_26;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_box(x_119);
if (lean_is_scalar(x_31)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_31;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_126);
lean_inc(x_2);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_2);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_107, 0, x_134);
x_18 = x_107;
x_19 = x_122;
goto block_26;
}
}
else
{
uint8_t x_135; 
lean_dec(x_117);
lean_free_object(x_107);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_120);
if (x_135 == 0)
{
return x_120;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_120, 0);
x_137 = lean_ctor_get(x_120, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_120);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_107, 0);
lean_inc(x_139);
lean_dec(x_107);
x_140 = lean_ctor_get(x_39, 1);
lean_inc(x_140);
lean_dec(x_39);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_139, sizeof(void*)*2);
lean_dec(x_139);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_144 = l_Lean_Meta_mkEqTrans_x3f(x_35, x_142, x_10, x_11, x_12, x_13, x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = 1;
x_148 = lean_box(x_147);
if (lean_is_scalar(x_36)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_36;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
if (lean_is_scalar(x_33)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_33;
}
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_unbox(x_30);
lean_dec(x_30);
if (x_151 == 0)
{
uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = 0;
x_153 = lean_box(x_152);
if (lean_is_scalar(x_31)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_31;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
lean_inc(x_2);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_2);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_18 = x_156;
x_19 = x_146;
goto block_26;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_box(x_143);
if (lean_is_scalar(x_31)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_31;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
lean_inc(x_2);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_2);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_18 = x_160;
x_19 = x_146;
goto block_26;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_141);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_161 = lean_ctor_get(x_144, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_144, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_163 = x_144;
} else {
 lean_dec_ref(x_144);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_39);
if (x_165 == 0)
{
return x_39;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_39, 0);
x_167 = lean_ctor_get(x_39, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_39);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_box(0);
x_13 = l_Lean_Meta_Simp_simprocCore___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_size(x_2);
x_20 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocArrayCore___spec__1(x_1, x_12, x_2, x_19, x_20, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_unbox(x_29);
lean_dec(x_29);
x_33 = l_Lean_Meta_Simp_simprocArrayCore___lambda__1(x_32, x_12, x_28, x_30, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_21, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_36);
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocArrayCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocArrayCore___spec__1(x_15, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_Simp_simprocArrayCore___lambda__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_simprocArrayCore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocArrayCore___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_array_uget(x_3, x_5);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_17, 3);
lean_inc(x_22);
if (x_1 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_17, 0);
lean_inc(x_85);
lean_dec(x_17);
x_23 = x_85;
goto block_84;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_17, 1);
lean_inc(x_86);
lean_dec(x_17);
x_23 = x_86;
goto block_84;
}
block_84:
{
lean_object* x_24; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_24 = l_Lean_Meta_Simp_dsimprocCore(x_1, x_23, x_22, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
switch (lean_obj_tag(x_25)) {
case 0:
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_25);
if (lean_is_scalar(x_21)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_21;
}
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_21)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_21;
}
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_20);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_39 = x_25;
} else {
 lean_dec_ref(x_25);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_21)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_21;
}
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_20);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
case 1:
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_24, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_25);
if (lean_is_scalar(x_21)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_21;
}
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_20);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_24, 0, x_50);
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
lean_dec(x_25);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_21)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_21;
}
lean_ctor_set(x_54, 0, x_19);
lean_ctor_set(x_54, 1, x_20);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_24, 0, x_55);
return x_24;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_dec(x_24);
x_57 = lean_ctor_get(x_25, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_58 = x_25;
} else {
 lean_dec_ref(x_25);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_21)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_21;
}
lean_ctor_set(x_61, 0, x_19);
lean_ctor_set(x_61, 1, x_20);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
}
default: 
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_25, 0);
lean_inc(x_64);
lean_dec(x_25);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; 
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_dec(x_24);
if (lean_is_scalar(x_21)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_21;
}
lean_ctor_set(x_66, 0, x_19);
lean_ctor_set(x_66, 1, x_20);
lean_inc(x_2);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_2);
lean_ctor_set(x_67, 1, x_66);
x_68 = 1;
x_69 = lean_usize_add(x_5, x_68);
x_5 = x_69;
x_6 = x_67;
x_14 = x_65;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; 
lean_dec(x_20);
lean_dec(x_19);
x_71 = lean_ctor_get(x_24, 1);
lean_inc(x_71);
lean_dec(x_24);
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec(x_64);
x_73 = 1;
x_74 = lean_box(x_73);
if (lean_is_scalar(x_21)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_21;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_2);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_75);
x_77 = 1;
x_78 = lean_usize_add(x_5, x_77);
x_5 = x_78;
x_6 = x_76;
x_14 = x_71;
goto _start;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_24);
if (x_80 == 0)
{
return x_24;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_24, 0);
x_82 = lean_ctor_get(x_24, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_24);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_size(x_2);
x_18 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocArrayCore___spec__1(x_1, x_12, x_2, x_17, x_18, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_unbox(x_25);
lean_dec(x_25);
x_28 = l_Lean_Meta_Simp_dsimprocCore___lambda__1(x_27, x_12, x_24, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocArrayCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_dsimprocArrayCore___spec__1(x_15, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_dsimprocArrayCore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backward compatibility", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Enable/disable `simproc`s (simplification procedures).", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__3;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__5;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__6;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_Meta_Simp_simprocArrayCore(x_12, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Simp_userPreSimprocs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_simprocs;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_userPreSimprocs___closed__1;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = l_Lean_Meta_Simp_simprocArrayCore(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_userPreSimprocs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPreSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
x_13 = l_Lean_Meta_Simp_simprocArrayCore(x_12, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_userPreSimprocs___closed__1;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
x_17 = l_Lean_Meta_Simp_simprocArrayCore(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_userPostSimprocs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPostSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_Meta_Simp_dsimprocArrayCore(x_12, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_userPreSimprocs___closed__1;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = l_Lean_Meta_Simp_dsimprocArrayCore(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_userPreDSimprocs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPreDSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
x_13 = l_Lean_Meta_Simp_dsimprocArrayCore(x_12, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_userPreSimprocs___closed__1;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
x_17 = l_Lean_Meta_Simp_dsimprocArrayCore(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_userPostDSimprocs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPostDSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__8;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__12;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__13;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__15;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__14;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__17;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__11;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__9;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__19;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__20;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__7;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__21;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__5;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__23;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__24;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__3;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__25;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__26;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_toSimprocEntry(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Meta_Simp_Simprocs_addCore(x_1, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lambda__3), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Meta_Simp_mkSimprocExt___closed__1;
x_5 = l_Lean_Meta_Simp_mkSimprocExt___closed__2;
x_6 = l_Lean_Meta_Simp_mkSimprocExt___closed__3;
x_7 = l_Lean_Meta_Simp_mkSimprocExt___closed__4;
x_8 = l_Lean_Meta_Simp_mkSimprocExt___closed__5;
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
x_10 = l_Lean_registerScopedEnvExtensionUnsafe___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lambda__4___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Simp_mkSimprocExt___closed__2;
x_14 = l_Lean_Meta_Simp_mkSimprocExt___closed__3;
x_15 = l_Lean_Meta_Simp_mkSimprocExt___closed__4;
x_16 = l_Lean_Meta_Simp_mkSimprocExt___closed__5;
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set(x_17, 5, x_16);
x_18 = l_Lean_registerScopedEnvExtensionUnsafe___rarg(x_17, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_mkSimprocExt___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_mkSimprocExt___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_mkSimprocExt___lambda__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
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
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_2 = l_Lean_Meta_Simp_addSimprocAttr___closed__2;
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
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_addSimprocAttr___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Simp_addSimprocAttr___closed__5;
x_3 = l_Lean_Meta_Simp_addSimprocAttr___closed__4;
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
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_addSimprocAttr___closed__1;
x_3 = l_Lean_Meta_Simp_addSimprocAttr___closed__3;
x_4 = l_Lean_Meta_Simp_addSimprocAttr___closed__6;
x_5 = l_Lean_Meta_Simp_addSimprocAttr___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpPost", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2;
x_4 = l_Lean_Meta_Simp_addSimprocAttr___closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_3, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
x_11 = l_Lean_Meta_Simp_addSimprocAttr___closed__8;
x_12 = lean_st_mk_ref(x_11, x_7);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_9, x_15);
lean_dec(x_9);
x_17 = l_Lean_Syntax_getKind(x_16);
x_18 = l_Lean_Meta_Simp_addSimprocAttr___closed__10;
x_19 = lean_name_eq(x_17, x_18);
lean_dec(x_17);
x_20 = l_Lean_Meta_Simp_addSimprocAttrCore(x_1, x_2, x_4, x_19, x_5, x_6, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_13, x_21);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_9);
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = 1;
x_36 = l_Lean_Meta_Simp_addSimprocAttrCore(x_1, x_2, x_4, x_35, x_5, x_6, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_33, x_37);
lean_dec(x_33);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_33);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_36);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_Simp_addSimprocAttr(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = 1;
x_7 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_6);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_addSimprocAttr___boxed), 7, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___boxed), 5, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Lean_registerBuiltinAttribute(x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6046_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3;
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6090_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__26;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerSimprocAttr___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerSimprocAttr___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerSimprocAttr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_registerSimprocAttr___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerSimprocAttr___spec__2(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_registerSimprocAttr___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerSimprocAttr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerSimprocAttr___spec__5(x_1, x_2, x_8);
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
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerSimprocAttr___spec__5(x_1, x_2, x_13);
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
static lean_object* _init_l_Lean_Meta_Simp_registerSimprocAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_simprocExtensionMapRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Meta_Simp_mkSimprocExt(x_4, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_Simp_mkSimprocAttr(x_1, x_2, x_7, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_Simp_registerSimprocAttr___closed__1;
x_12 = lean_st_ref_take(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l_Lean_Name_hash___override(x_1);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_17, x_30);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerSimprocAttr___spec__1(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_16, x_33);
lean_dec(x_16);
lean_inc(x_7);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_7);
lean_ctor_set(x_35, 2, x_31);
x_36 = lean_array_uset(x_17, x_30, x_35);
x_37 = lean_unsigned_to_nat(4u);
x_38 = lean_nat_mul(x_34, x_37);
x_39 = lean_unsigned_to_nat(3u);
x_40 = lean_nat_div(x_38, x_39);
lean_dec(x_38);
x_41 = lean_array_get_size(x_36);
x_42 = lean_nat_dec_le(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerSimprocAttr___spec__2(x_36);
lean_ctor_set(x_13, 1, x_43);
lean_ctor_set(x_13, 0, x_34);
x_44 = lean_st_ref_set(x_11, x_13, x_14);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_7);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_7);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_ctor_set(x_13, 1, x_36);
lean_ctor_set(x_13, 0, x_34);
x_49 = lean_st_ref_set(x_11, x_13, x_14);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_7);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_7);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_box(0);
x_55 = lean_array_uset(x_17, x_30, x_54);
lean_inc(x_7);
x_56 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerSimprocAttr___spec__5(x_1, x_7, x_31);
x_57 = lean_array_uset(x_55, x_30, x_56);
lean_ctor_set(x_13, 1, x_57);
x_58 = lean_st_ref_set(x_11, x_13, x_14);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_7);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_7);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; uint8_t x_79; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_array_get_size(x_64);
x_66 = l_Lean_Name_hash___override(x_1);
x_67 = 32;
x_68 = lean_uint64_shift_right(x_66, x_67);
x_69 = lean_uint64_xor(x_66, x_68);
x_70 = 16;
x_71 = lean_uint64_shift_right(x_69, x_70);
x_72 = lean_uint64_xor(x_69, x_71);
x_73 = lean_uint64_to_usize(x_72);
x_74 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_75 = 1;
x_76 = lean_usize_sub(x_74, x_75);
x_77 = lean_usize_land(x_73, x_76);
x_78 = lean_array_uget(x_64, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerSimprocAttr___spec__1(x_1, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_63, x_80);
lean_dec(x_63);
lean_inc(x_7);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_7);
lean_ctor_set(x_82, 2, x_78);
x_83 = lean_array_uset(x_64, x_77, x_82);
x_84 = lean_unsigned_to_nat(4u);
x_85 = lean_nat_mul(x_81, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_registerSimprocAttr___spec__2(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_st_ref_set(x_11, x_91, x_14);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_7);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_81);
lean_ctor_set(x_96, 1, x_83);
x_97 = lean_st_ref_set(x_11, x_96, x_14);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_7);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_box(0);
x_102 = lean_array_uset(x_64, x_77, x_101);
lean_inc(x_7);
x_103 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_registerSimprocAttr___spec__5(x_1, x_7, x_78);
x_104 = lean_array_uset(x_102, x_77, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_63);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_st_ref_set(x_11, x_105, x_14);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_7);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_7);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_9);
if (x_110 == 0)
{
return x_9;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_9, 0);
x_112 = lean_ctor_get(x_9, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_9);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_6);
if (x_114 == 0)
{
return x_6;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_6, 0);
x_116 = lean_ctor_get(x_6, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_6);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerSimprocAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_registerSimprocAttr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocAttr", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_addSimprocBuiltinAttr___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocExtension", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simplification procedure", 24, 24);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__6;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__3;
x_5 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__5;
x_6 = l_Lean_Meta_Simp_registerSimprocAttr(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sevalprocAttr", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocSEvalExtension", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Symbolic evaluator procedure", 28, 28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__6;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__3;
x_5 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__5;
x_6 = l_Lean_Meta_Simp_registerSimprocAttr(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declare", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_11 = l_Lean_Expr_const___override(x_1, x_2);
lean_inc(x_3);
x_12 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_3);
lean_inc(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_2);
x_14 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__2;
x_15 = l_Lean_Name_append(x_3, x_14);
x_16 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_15, x_8, x_9, x_10);
if (x_4 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__5;
x_21 = l_Lean_Expr_const___override(x_20, x_2);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_array_mk(x_22);
x_24 = l_Lean_mkAppN(x_11, x_23);
lean_dec(x_23);
x_25 = l_Lean_declareBuiltin(x_18, x_24, x_8, x_9, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__5;
x_29 = l_Lean_Expr_const___override(x_28, x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_mk(x_31);
x_33 = l_Lean_mkAppN(x_11, x_32);
lean_dec(x_32);
x_34 = l_Lean_declareBuiltin(x_26, x_33, x_8, x_9, x_27);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
x_38 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__7;
x_39 = l_Lean_Expr_const___override(x_38, x_2);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 0, x_39);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_16);
x_41 = lean_array_mk(x_40);
x_42 = l_Lean_mkAppN(x_11, x_41);
lean_dec(x_41);
x_43 = l_Lean_declareBuiltin(x_36, x_42, x_8, x_9, x_37);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__7;
x_47 = l_Lean_Expr_const___override(x_46, x_2);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_13);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_mk(x_49);
x_51 = l_Lean_mkAppN(x_11, x_50);
lean_dec(x_50);
x_52 = l_Lean_declareBuiltin(x_44, x_51, x_8, x_9, x_45);
return x_52;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1() {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2;
x_2 = l_Lean_Meta_Simp_addSimprocAttr___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_addSimprocAttr___closed__1;
x_3 = l_Lean_Meta_Simp_addSimprocAttr___closed__3;
x_4 = l_Lean_Meta_Simp_addSimprocAttr___closed__6;
x_5 = l_Lean_Meta_Simp_addSimprocAttr___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sum", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inr", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9;
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inl", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18;
x_2 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
x_10 = lean_box(0);
x_11 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4;
x_12 = lean_st_mk_ref(x_11, x_6);
if (x_9 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_130 = lean_ctor_get(x_12, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_12, 1);
lean_inc(x_131);
lean_dec(x_12);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Lean_Syntax_getArg(x_8, x_132);
lean_dec(x_8);
x_134 = l_Lean_Syntax_getKind(x_133);
x_135 = l_Lean_Meta_Simp_addSimprocAttr___closed__10;
x_136 = lean_name_eq(x_134, x_135);
lean_dec(x_134);
x_13 = x_136;
x_14 = x_130;
x_15 = x_131;
goto block_129;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_8);
x_137 = lean_ctor_get(x_12, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_12, 1);
lean_inc(x_138);
lean_dec(x_12);
x_139 = 1;
x_13 = x_139;
x_14 = x_137;
x_15 = x_138;
goto block_129;
}
block_129:
{
lean_object* x_16; lean_object* x_29; lean_object* x_30; 
x_29 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3;
lean_inc(x_1);
x_30 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_29, x_14, x_4, x_5, x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_ConstantInfo_type(x_31);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_44 = lean_string_dec_eq(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_3);
lean_dec(x_1);
x_45 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_46 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_45, x_29, x_14, x_4, x_5, x_32);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
x_16 = x_46;
goto block_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_16 = x_50;
goto block_28;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_52 = lean_string_dec_eq(x_41, x_51);
lean_dec(x_41);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_3);
lean_dec(x_1);
x_53 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_54 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_53, x_29, x_14, x_4, x_5, x_32);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
x_16 = x_54;
goto block_28;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_16 = x_58;
goto block_28;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_60 = lean_string_dec_eq(x_40, x_59);
lean_dec(x_40);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_39);
lean_dec(x_3);
lean_dec(x_1);
x_61 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_62 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_61, x_29, x_14, x_4, x_5, x_32);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
x_16 = x_62;
goto block_28;
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
x_16 = x_66;
goto block_28;
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5;
x_68 = lean_string_dec_eq(x_39, x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6;
x_70 = lean_string_dec_eq(x_39, x_69);
lean_dec(x_39);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_3);
lean_dec(x_1);
x_71 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_72 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_71, x_29, x_14, x_4, x_5, x_32);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
x_16 = x_72;
goto block_28;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_16 = x_76;
goto block_28;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_1);
x_77 = l_Lean_Expr_const___override(x_1, x_10);
x_78 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12;
x_79 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14;
x_80 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16;
x_81 = l_Lean_mkApp3(x_78, x_79, x_80, x_77);
x_82 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1(x_3, x_10, x_1, x_13, x_81, x_29, x_14, x_4, x_5, x_32);
x_16 = x_82;
goto block_28;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_39);
lean_inc(x_1);
x_83 = l_Lean_Expr_const___override(x_1, x_10);
x_84 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19;
x_85 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14;
x_86 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16;
x_87 = l_Lean_mkApp3(x_84, x_85, x_86, x_83);
x_88 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1(x_3, x_10, x_1, x_13, x_87, x_29, x_14, x_4, x_5, x_32);
x_16 = x_88;
goto block_28;
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_1);
x_89 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_90 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_89, x_29, x_14, x_4, x_5, x_32);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
x_16 = x_90;
goto block_28;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_16 = x_94;
goto block_28;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_1);
x_95 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_96 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_95, x_29, x_14, x_4, x_5, x_32);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
x_16 = x_96;
goto block_28;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_16 = x_100;
goto block_28;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_1);
x_101 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_102 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_101, x_29, x_14, x_4, x_5, x_32);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
x_16 = x_102;
goto block_28;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_16 = x_106;
goto block_28;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_1);
x_107 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_108 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_107, x_29, x_14, x_4, x_5, x_32);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
x_16 = x_108;
goto block_28;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_16 = x_112;
goto block_28;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_1);
x_113 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_114 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_113, x_29, x_14, x_4, x_5, x_32);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
x_16 = x_114;
goto block_28;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_114);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_16 = x_118;
goto block_28;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_1);
x_119 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
x_120 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_119, x_29, x_14, x_4, x_5, x_32);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
x_16 = x_120;
goto block_28;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_120);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_16 = x_124;
goto block_28;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_30);
if (x_125 == 0)
{
x_16 = x_30;
goto block_28;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_30, 0);
x_127 = lean_ctor_get(x_30, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_30);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_16 = x_128;
goto block_28;
}
}
block_28:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("addSimprocBuiltinAttr", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__2;
x_8 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not implemented yet, [-builtin_simproc]", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__2;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__3;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__5;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__7;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__8;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__9;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__10;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__11;
x_2 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__12;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__14;
x_2 = lean_unsigned_to_nat(6655u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simprocBuiltinAttr", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Builtin simplification procedure", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__15;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__17;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__18;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__19;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__20;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__22;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("addSEvalprocBuiltinAttr", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3;
x_4 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__2;
x_8 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not implemented yet, [-builtin_sevalproc]", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__14;
x_2 = lean_unsigned_to_nat(6731u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sevalprocBuiltinAttr", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Builtin symbolic evaluation procedure", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__1;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__3;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__4;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__5;
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__6;
x_3 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__8;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSimprocs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_simprocExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_8 = l_Lean_Meta_Simp_getSimprocs___rarg___closed__1;
x_9 = l_Lean_ScopedEnvExtension_getState___rarg(x_7, x_8, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_14 = l_Lean_Meta_Simp_getSimprocs___rarg___closed__1;
x_15 = l_Lean_ScopedEnvExtension_getState___rarg(x_13, x_14, x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getSimprocs___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimprocs___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getSimprocs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getSEvalSimprocs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_simprocSEvalExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_8 = l_Lean_Meta_Simp_getSEvalSimprocs___rarg___closed__1;
x_9 = l_Lean_ScopedEnvExtension_getState___rarg(x_7, x_8, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_14 = l_Lean_Meta_Simp_getSEvalSimprocs___rarg___closed__1;
x_15 = l_Lean_ScopedEnvExtension_getState___rarg(x_13, x_14, x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getSEvalSimprocs___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSEvalSimprocs___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getSEvalSimprocs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocExtensionCore_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Simp_registerSimprocAttr___closed__1;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_1);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_7, x_20);
lean_dec(x_7);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocExtensionCore_x3f___spec__1(x_1, x_21);
lean_dec(x_21);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = l_Lean_Name_hash___override(x_1);
x_28 = 32;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = 16;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = 1;
x_37 = lean_usize_sub(x_35, x_36);
x_38 = lean_usize_land(x_34, x_37);
x_39 = lean_array_uget(x_25, x_38);
lean_dec(x_25);
x_40 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocExtensionCore_x3f___spec__1(x_1, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_24);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocExtensionCore_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_getSimprocExtensionCore_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seval", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_proc", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__4;
x_7 = lean_name_append_after(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__2;
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__2;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_1);
x_7 = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(x_6, x_5);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_15 = x_4;
} else {
 lean_dec_ref(x_4);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(1, 1, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_10 = l_Lean_ScopedEnvExtension_getState___rarg(x_9, x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_15 = l_Lean_ScopedEnvExtension_getState___rarg(x_14, x_1, x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__1 = _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__1);
l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__2 = _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__2);
l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3 = _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_BuiltinSimprocs_keys___default___closed__3);
l_Lean_Meta_Simp_BuiltinSimprocs_keys___default = _init_l_Lean_Meta_Simp_BuiltinSimprocs_keys___default();
lean_mark_persistent(l_Lean_Meta_Simp_BuiltinSimprocs_keys___default);
l_Lean_Meta_Simp_BuiltinSimprocs_procs___default = _init_l_Lean_Meta_Simp_BuiltinSimprocs_procs___default();
lean_mark_persistent(l_Lean_Meta_Simp_BuiltinSimprocs_procs___default);
l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs___closed__1);
l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs = _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_60_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSimprocDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSimprocDeclsRef);
lean_dec_ref(res);
}l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__1);
l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDecl___closed__2);
l_Lean_Meta_Simp_instInhabitedSimprocDecl = _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDecl);
l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__1 = _init_l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__1);
l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2 = _init_l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default___closed__2);
l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default = _init_l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default();
lean_mark_persistent(l_Lean_Meta_Simp_SimprocDeclExtState_newEntries___default);
l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState___closed__1);
l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState = _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState);
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__2___closed__3);
l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___closed__1 = _init_l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____spec__6___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__1___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____lambda__6___closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__3);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__4 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__4);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__5 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__5);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__6 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__6);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__7 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__7);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__8 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__8);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__9 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__9);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__10 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__10);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__11 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__11);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__12 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__12);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__13 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189____closed__13);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_189_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocDeclExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocDeclExt);
lean_dec_ref(res);
}l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___lambda__1___closed__1);
l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1 = _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__1);
l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__2 = _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__2);
l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3 = _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_registerBuiltinSimprocCore___lambda__3___closed__3);
l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1 = _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1);
l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2 = _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2);
l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimproc___lambda__2___closed__1);
l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__1 = _init_l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__1);
l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2 = _init_l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__2);
l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__3 = _init_l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimproc___lambda__3___closed__3);
l_Lean_Meta_Simp_registerSimproc___closed__1 = _init_l_Lean_Meta_Simp_registerSimproc___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimproc___closed__1);
l_Lean_Meta_Simp_registerSimproc___closed__2 = _init_l_Lean_Meta_Simp_registerSimproc___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimproc___closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146____closed__2);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1146_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSimprocsRef);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1182_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSEvalprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSEvalprocsRef);
lean_dec_ref(res);
}l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1 = _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1);
l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2 = _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2);
l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3 = _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3);
l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4 = _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4);
l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5 = _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5);
l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6 = _init_l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__6);
l_Lean_Meta_Simp_eraseSimprocAttr___closed__1 = _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_eraseSimprocAttr___closed__1);
l_Lean_Meta_Simp_eraseSimprocAttr___closed__2 = _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_eraseSimprocAttr___closed__2);
l_Lean_Meta_Simp_eraseSimprocAttr___closed__3 = _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_eraseSimprocAttr___closed__3);
l_Lean_Meta_Simp_addSimprocAttrCore___closed__1 = _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttrCore___closed__1);
l_Lean_Meta_Simp_addSimprocAttrCore___closed__2 = _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttrCore___closed__2);
l_Lean_Meta_Simp_addSimprocAttrCore___closed__3 = _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttrCore___closed__3);
l_Lean_Meta_Simp_addSimprocAttrCore___closed__4 = _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttrCore___closed__4);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Simp_Simprocs_addCore___spec__9___closed__1);
l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13___closed__1 = _init_l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_Simprocs_addCore___spec__13___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Simp_Simprocs_addCore___spec__1___closed__4);
l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1 = _init_l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1);
l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__2 = _init_l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__2);
l_Lean_Meta_Simp_addSimprocBuiltinAttr___closed__1 = _init_l_Lean_Meta_Simp_addSimprocBuiltinAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocBuiltinAttr___closed__1);
l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___closed__1 = _init_l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___closed__1);
l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1 = _init_l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simprocCore___spec__1___closed__10);
l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___lambda__2___closed__1);
l_Lean_Meta_Simp_simprocCore___closed__1 = _init_l_Lean_Meta_Simp_simprocCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__1);
l_Lean_Meta_Simp_simprocCore___closed__2 = _init_l_Lean_Meta_Simp_simprocCore___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__2);
l_Lean_Meta_Simp_simprocCore___closed__3 = _init_l_Lean_Meta_Simp_simprocCore___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__3);
l_Lean_Meta_Simp_simprocCore___closed__4 = _init_l_Lean_Meta_Simp_simprocCore___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__4);
l_Lean_Meta_Simp_simprocCore___closed__5 = _init_l_Lean_Meta_Simp_simprocCore___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__5);
l_Lean_Meta_Simp_simprocCore___closed__6 = _init_l_Lean_Meta_Simp_simprocCore___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__6);
l_Lean_Meta_Simp_simprocCore___closed__7 = _init_l_Lean_Meta_Simp_simprocCore___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__7);
l_Lean_Meta_Simp_simprocCore___closed__8 = _init_l_Lean_Meta_Simp_simprocCore___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_simprocCore___closed__8);
l_Lean_Meta_Simp_dsimprocCore___closed__1 = _init_l_Lean_Meta_Simp_dsimprocCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_dsimprocCore___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__3 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__3);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__4 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__4);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__5 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__5);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__6 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439____closed__6);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5439_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocs);
lean_dec_ref(res);
}l_Lean_Meta_Simp_userPreSimprocs___closed__1 = _init_l_Lean_Meta_Simp_userPreSimprocs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_userPreSimprocs___closed__1);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__1);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__2 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__2();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__2);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__3 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__3();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__3);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__4 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__4();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__4);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__5 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__5();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__5);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__6 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__6();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__6);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__7 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__7();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__7);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__8 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__8();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__8);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__9 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__9();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__9);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__10 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__10();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__10);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__11 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__11();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__11);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__12 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__12();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__12);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__13 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__13();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__13);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__14 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__14();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__14);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__15 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__15();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__15);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__16 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__16();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__16);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__17 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__17();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__17);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__18 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__18();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__18);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__19 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__19();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__19);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__20 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__20();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__20);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__21 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__21();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__21);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__22 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__22();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__22);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__23 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__23();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__23);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__24 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__24();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__24);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__25 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__25();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__25);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__26 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__26();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774____closed__26);
l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5774_);
l_Lean_Meta_Simp_mkSimprocExt___closed__1 = _init_l_Lean_Meta_Simp_mkSimprocExt___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimprocExt___closed__1);
l_Lean_Meta_Simp_mkSimprocExt___closed__2 = _init_l_Lean_Meta_Simp_mkSimprocExt___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimprocExt___closed__2);
l_Lean_Meta_Simp_mkSimprocExt___closed__3 = _init_l_Lean_Meta_Simp_mkSimprocExt___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimprocExt___closed__3);
l_Lean_Meta_Simp_mkSimprocExt___closed__4 = _init_l_Lean_Meta_Simp_mkSimprocExt___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimprocExt___closed__4);
l_Lean_Meta_Simp_mkSimprocExt___closed__5 = _init_l_Lean_Meta_Simp_mkSimprocExt___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimprocExt___closed__5);
l_Lean_Meta_Simp_addSimprocAttr___closed__1 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__1);
l_Lean_Meta_Simp_addSimprocAttr___closed__2 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__2);
l_Lean_Meta_Simp_addSimprocAttr___closed__3 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__3);
l_Lean_Meta_Simp_addSimprocAttr___closed__4 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__4);
l_Lean_Meta_Simp_addSimprocAttr___closed__5 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__5);
l_Lean_Meta_Simp_addSimprocAttr___closed__6 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__6);
l_Lean_Meta_Simp_addSimprocAttr___closed__7 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__7);
l_Lean_Meta_Simp_addSimprocAttr___closed__8 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__8);
l_Lean_Meta_Simp_addSimprocAttr___closed__9 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__9);
l_Lean_Meta_Simp_addSimprocAttr___closed__10 = _init_l_Lean_Meta_Simp_addSimprocAttr___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_addSimprocAttr___closed__10);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6046_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocExtensionMapRef);
lean_dec_ref(res);
}l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6090_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6090_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6090_);
l_Lean_Meta_Simp_registerSimprocAttr___closed__1 = _init_l_Lean_Meta_Simp_registerSimprocAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimprocAttr___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__3 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__3);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__4 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__4);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__5 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__5);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__6 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161____closed__6);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6161_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocExtension);
lean_dec_ref(res);
}l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__3 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__3);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__4 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__4);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__5 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__5);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__6 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192____closed__6);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6192_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocSEvalExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocSEvalExtension);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__5);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__6);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lambda__1___closed__7);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18);
l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19 = _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__1___closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____lambda__2___closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__3 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__3);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__4 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__4);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__5 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__5);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__6 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__6);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__7 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__7);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__8 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__8);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__9 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__9);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__10 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__10);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__11 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__11);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__12 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__12);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__13 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__13);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__14 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__14);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__15 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__15);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__16 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__16);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__17 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__17);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__18 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__18);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__19 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__19);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__20 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__20);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__21 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__21();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__21);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__22 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__22();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655____closed__22);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6655_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__1___closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____lambda__2___closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__1 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__1);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__2 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__2);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__3 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__3);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__4 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__4);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__5 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__5);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__6 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__6);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__7 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__7);
l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__8 = _init_l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731____closed__8);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6731_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Simp_getSimprocs___rarg___closed__1 = _init_l_Lean_Meta_Simp_getSimprocs___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_getSimprocs___rarg___closed__1);
l_Lean_Meta_Simp_getSEvalSimprocs___rarg___closed__1 = _init_l_Lean_Meta_Simp_getSEvalSimprocs___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_getSEvalSimprocs___rarg___closed__1);
l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1 = _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1);
l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2 = _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2);
l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3 = _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3);
l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__4 = _init_l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
