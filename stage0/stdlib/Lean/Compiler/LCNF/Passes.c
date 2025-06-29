// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.CSE Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.PullFunDecls Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.JoinPoints Lean.Compiler.LCNF.Specialize Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.ToMono Lean.Compiler.LCNF.LambdaLifting Lean.Compiler.LCNF.FloatLetIn Lean.Compiler.LCNF.ReduceArity Lean.Compiler.LCNF.ElimDeadBranches Lean.Compiler.LCNF.StructProjCases Lean.Compiler.LCNF.ExtractClosed
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
lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__26;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__49;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__14;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__22;
static lean_object* l_Lean_Compiler_LCNF_saveBase___closed__1;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__33;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__27;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__32;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__34;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_lambdaLifting;
static lean_object* l_Lean_Compiler_LCNF_trace___closed__0;
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__30;
static lean_object* l_Lean_Compiler_LCNF_saveMono___closed__1;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__18;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_958____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__0;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__48;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_reduceArity;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__24;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1106_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__5;
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___lam__0___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__12;
extern lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_initFn___lam__1___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__31;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__9;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__47;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_958____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__38;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_extractClosed;
lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__44;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__37;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__21;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__7;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__19;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
static lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__39;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__13;
extern lean_object* l_Lean_Compiler_LCNF_findJoinPoints;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_pullInstances;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace(uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_elimDeadBranches;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_init___closed__0;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__7;
lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__3;
lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_passManagerExt;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_toMono;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__23;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__2;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__40;
extern lean_object* l_Lean_Compiler_LCNF_pullFunDecls;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__35;
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
uint8_t l_Lean_beqAttributeKind____x40_Lean_Attributes___hyg_169_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__36;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_958_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__5;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__17;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__20;
static lean_object* l_Lean_Compiler_LCNF_saveBase___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__43;
static lean_object* l_Lean_Compiler_LCNF_initFn___lam__0___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__11;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__46;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_builtinPassManager;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_init___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__16;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___lam__1___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__4;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__41;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__28;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__29;
extern lean_object* l_Lean_Compiler_LCNF_structProjCases;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
static lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__25;
static lean_object* l_Lean_Compiler_LCNF_trace___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_saveMono___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___boxed(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_specialize;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__45;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__42;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_8, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_box(0);
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(x_2, x_14, x_15, x_13, x_6, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_init___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_init___lam__0___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_box(1);
x_5 = l_Lean_Compiler_LCNF_init___closed__1;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_8);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_9);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_init___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_trace___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_trace___lam__0___boxed), 6, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_Lean_Compiler_LCNF_trace___closed__1;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_1);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_trace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_LCNF_trace(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_3, x_2, x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_19 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_20, x_5, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_12 = x_9;
x_13 = x_23;
goto block_18;
}
else
{
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_12 = x_24;
x_13 = x_25;
goto block_18;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_11, x_2, x_12);
x_2 = x_15;
x_3 = x_16;
x_6 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_array_size(x_1);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___redArg(x_7, x_8, x_1, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("saveBase", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_saveBase___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveBase___lam__0___boxed), 6, 0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = lean_box(1);
x_5 = l_Lean_Compiler_LCNF_saveBase___closed__1;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_8);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_9);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveBase_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_saveBase___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_3, x_2, x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_19 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_20, x_5, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_12 = x_9;
x_13 = x_23;
goto block_18;
}
else
{
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_12 = x_24;
x_13 = x_25;
goto block_18;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_11, x_2, x_12);
x_2 = x_15;
x_3 = x_16;
x_6 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_array_size(x_1);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___redArg(x_7, x_8, x_1, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("saveMono", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_saveMono___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveMono___lam__0___boxed), 6, 0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(1);
x_4 = lean_box(1);
x_5 = l_Lean_Compiler_LCNF_saveMono___closed__1;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_8);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_9);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_saveMono_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_saveMono___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Compiler_LCNF_cse(x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_1 = lean_box(1);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 0, 4);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 0, x_4);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 1, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 2, x_6);
x_7 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 3, x_7);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_simp(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Compiler_LCNF_floatLetIn(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_reduceJpArity(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 0, 4);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 3, x_6);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Compiler_LCNF_builtinPassManager___closed__5;
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_simp(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_simp(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Compiler_LCNF_cse(x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(1);
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_simp(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_reduceJpArity(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Compiler_LCNF_floatLetIn(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(1);
x_2 = lean_unsigned_to_nat(4u);
x_3 = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_simp(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Compiler_LCNF_floatLetIn(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(1);
x_2 = lean_unsigned_to_nat(5u);
x_3 = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_simp(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Compiler_LCNF_cse(x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_init;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__18;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_pullInstances;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__19;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__0;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__20;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__21;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__3;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_findJoinPoints;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__23;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_pullFunDecls;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__4;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__25;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__6;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__26;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_eagerLambdaLifting;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__27;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_specialize;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__28;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__7;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__8;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__30;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_saveBase;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__31;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_toMono;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__32;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__9;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__33;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__10;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__34;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_structProjCases;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__35;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__11;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__36;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__12;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__37;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_reduceArity;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__38;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_commonJoinPointArgs;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__39;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__13;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__40;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__14;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__41;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_elimDeadBranches;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__42;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_lambdaLifting;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__43;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__15;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__44;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__16;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__45;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__17;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__46;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_saveMono;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__47;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_extractClosed;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__48;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__49;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_1, x_3);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(x_4, x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_array_size(x_10);
x_12 = 0;
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(x_10, x_11, x_12, x_4, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_14;
x_7 = x_15;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = l_Lean_Compiler_LCNF_builtinPassManager;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(x_1, x_6, x_7, x_5, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_runImportedDecls(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_List_reverse___redArg(x_2);
x_4 = lean_array_mk(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_reverse___redArg(x_4);
x_6 = lean_array_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_7);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_14 = x_2;
} else {
 lean_dec_ref(x_2);
 x_14 = lean_box(0);
}
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_11);
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_runImportedDecls___boxed), 4, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_ImportM_runCoreM___redArg(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("passManagerExt", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_3 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_4 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed), 3, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_), 2, 0);
x_6 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed), 4, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_box(2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_5);
lean_ctor_set(x_13, 4, x_4);
lean_ctor_set(x_13, 5, x_3);
lean_ctor_set(x_13, 6, x_12);
x_14 = lean_unbox(x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*7, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_2);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_599____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_passManagerExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0;
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__2;
x_11 = l_Lean_PersistentEnvExtension_getState___redArg(x_10, x_7, x_6, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0;
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
lean_dec(x_17);
x_19 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__2;
x_20 = l_Lean_PersistentEnvExtension_getState___redArg(x_19, x_16, x_15, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_getPassManager___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_getPassManager___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_getPassManager(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'cpass' only 'PassInstaller's can be added via the 'cpass' attribute: ", 78, 78);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PassInstaller", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__6;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_18; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_18 = l_Lean_ConstantInfo_type(x_6);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
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
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_29 = lean_string_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_31 = lean_string_dec_eq(x_26, x_30);
lean_dec(x_26);
if (x_31 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_33 = lean_string_dec_eq(x_25, x_32);
lean_dec(x_25);
if (x_33 == 0)
{
lean_dec(x_24);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_35 = lean_string_dec_eq(x_24, x_34);
lean_dec(x_24);
if (x_35 == 0)
{
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_6);
x_36 = l_Lean_Compiler_LCNF_getPassManager___redArg(x_3, x_7);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
lean_inc(x_1);
x_39 = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(x_37, x_1, x_2, x_3, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_take(x_3, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 5);
lean_dec(x_48);
x_49 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0;
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 0, x_1);
x_50 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_49, x_47, x_42);
x_51 = l_Lean_Compiler_LCNF_addPass___closed__7;
lean_ctor_set(x_44, 5, x_51);
lean_ctor_set(x_44, 0, x_50);
x_52 = lean_st_ref_set(x_3, x_44, x_46);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_59 = lean_ctor_get(x_42, 1);
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
x_62 = lean_ctor_get(x_44, 2);
x_63 = lean_ctor_get(x_44, 3);
x_64 = lean_ctor_get(x_44, 4);
x_65 = lean_ctor_get(x_44, 6);
x_66 = lean_ctor_get(x_44, 7);
x_67 = lean_ctor_get(x_44, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_44);
x_68 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0;
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 0, x_1);
x_69 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_68, x_60, x_42);
x_70 = l_Lean_Compiler_LCNF_addPass___closed__7;
x_71 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_61);
lean_ctor_set(x_71, 2, x_62);
lean_ctor_set(x_71, 3, x_63);
lean_ctor_set(x_71, 4, x_64);
lean_ctor_set(x_71, 5, x_70);
lean_ctor_set(x_71, 6, x_65);
lean_ctor_set(x_71, 7, x_66);
lean_ctor_set(x_71, 8, x_67);
x_72 = lean_st_ref_set(x_3, x_71, x_59);
lean_dec(x_3);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_77 = lean_ctor_get(x_42, 0);
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_42);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 6);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 7);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 8);
lean_inc(x_86);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 lean_ctor_release(x_77, 6);
 lean_ctor_release(x_77, 7);
 lean_ctor_release(x_77, 8);
 x_87 = x_77;
} else {
 lean_dec_ref(x_77);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_40);
x_90 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_88, x_79, x_89);
x_91 = l_Lean_Compiler_LCNF_addPass___closed__7;
if (lean_is_scalar(x_87)) {
 x_92 = lean_alloc_ctor(0, 9, 0);
} else {
 x_92 = x_87;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_80);
lean_ctor_set(x_92, 2, x_81);
lean_ctor_set(x_92, 3, x_82);
lean_ctor_set(x_92, 4, x_83);
lean_ctor_set(x_92, 5, x_91);
lean_ctor_set(x_92, 6, x_84);
lean_ctor_set(x_92, 7, x_85);
lean_ctor_set(x_92, 8, x_86);
x_93 = lean_st_ref_set(x_3, x_92, x_78);
lean_dec(x_3);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_39);
if (x_98 == 0)
{
return x_39;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_39, 0);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_39);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_19);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_18);
lean_dec(x_1);
x_8 = x_2;
x_9 = x_3;
goto block_17;
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Compiler_LCNF_addPass___closed__1;
x_11 = l_Lean_ConstantInfo_type(x_6);
lean_dec(x_6);
x_12 = l_Lean_MessageData_ofExpr(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Compiler_LCNF_addPass___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(x_15, x_8, x_9, x_7);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
}
else
{
uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_5);
if (x_102 == 0)
{
return x_5;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_5, 0);
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_5);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___lam__0___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___lam__0___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn___lam__0___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_LCNF_initFn___lam__0___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_6 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___lam__1___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid attribute 'cpass', must be global", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___lam__1___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn___lam__1___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_beqAttributeKind____x40_Lean_Attributes___hyg_169_(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_initFn___lam__1___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_13 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(x_12, x_4, x_5, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_addPass(x_1, x_4, x_5, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
return x_14;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Passes", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(958u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cpass", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler passes for the code generator", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Passes___hyg_958_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(1);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_4 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_958_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_958____boxed), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_958____boxed), 6, 0);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
x_6 = l_Lean_registerBuiltinAttribute(x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_958____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_958____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_1106_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_saveBase___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_1106_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1106u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Passes___hyg_958_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_1106_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_saveMono___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_1106_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_trace___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1106_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
x_9 = lean_unbox(x_3);
x_10 = l_Lean_registerTraceClass(x_8, x_9, x_4, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_1106_;
x_13 = lean_unbox(x_3);
x_14 = l_Lean_registerTraceClass(x_12, x_13, x_4, x_11);
return x_14;
}
else
{
return x_10;
}
}
else
{
return x_6;
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_StructProjCases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CSE(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullFunDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_JoinPoints(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Specialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToMono(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LambdaLifting(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FloatLetIn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceArity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_StructProjCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExtractClosed(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_init___closed__0 = _init_l_Lean_Compiler_LCNF_init___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_init___closed__0);
l_Lean_Compiler_LCNF_init___closed__1 = _init_l_Lean_Compiler_LCNF_init___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_init___closed__1);
l_Lean_Compiler_LCNF_init = _init_l_Lean_Compiler_LCNF_init();
lean_mark_persistent(l_Lean_Compiler_LCNF_init);
l_Lean_Compiler_LCNF_trace___closed__0 = _init_l_Lean_Compiler_LCNF_trace___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_trace___closed__0);
l_Lean_Compiler_LCNF_trace___closed__1 = _init_l_Lean_Compiler_LCNF_trace___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_trace___closed__1);
l_Lean_Compiler_LCNF_saveBase___closed__0 = _init_l_Lean_Compiler_LCNF_saveBase___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase___closed__0);
l_Lean_Compiler_LCNF_saveBase___closed__1 = _init_l_Lean_Compiler_LCNF_saveBase___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase___closed__1);
l_Lean_Compiler_LCNF_saveBase = _init_l_Lean_Compiler_LCNF_saveBase();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase);
l_Lean_Compiler_LCNF_saveMono___closed__0 = _init_l_Lean_Compiler_LCNF_saveMono___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono___closed__0);
l_Lean_Compiler_LCNF_saveMono___closed__1 = _init_l_Lean_Compiler_LCNF_saveMono___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono___closed__1);
l_Lean_Compiler_LCNF_saveMono = _init_l_Lean_Compiler_LCNF_saveMono();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono);
l_Lean_Compiler_LCNF_builtinPassManager___closed__0 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__0);
l_Lean_Compiler_LCNF_builtinPassManager___closed__1 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__1);
l_Lean_Compiler_LCNF_builtinPassManager___closed__2 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__2);
l_Lean_Compiler_LCNF_builtinPassManager___closed__3 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__3);
l_Lean_Compiler_LCNF_builtinPassManager___closed__4 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__4);
l_Lean_Compiler_LCNF_builtinPassManager___closed__5 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__5);
l_Lean_Compiler_LCNF_builtinPassManager___closed__6 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__6);
l_Lean_Compiler_LCNF_builtinPassManager___closed__7 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__7);
l_Lean_Compiler_LCNF_builtinPassManager___closed__8 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__8);
l_Lean_Compiler_LCNF_builtinPassManager___closed__9 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__9);
l_Lean_Compiler_LCNF_builtinPassManager___closed__10 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__10);
l_Lean_Compiler_LCNF_builtinPassManager___closed__11 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__11);
l_Lean_Compiler_LCNF_builtinPassManager___closed__12 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__12);
l_Lean_Compiler_LCNF_builtinPassManager___closed__13 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__13);
l_Lean_Compiler_LCNF_builtinPassManager___closed__14 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__14);
l_Lean_Compiler_LCNF_builtinPassManager___closed__15 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__15);
l_Lean_Compiler_LCNF_builtinPassManager___closed__16 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__16);
l_Lean_Compiler_LCNF_builtinPassManager___closed__17 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__17);
l_Lean_Compiler_LCNF_builtinPassManager___closed__18 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__18);
l_Lean_Compiler_LCNF_builtinPassManager___closed__19 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__19);
l_Lean_Compiler_LCNF_builtinPassManager___closed__20 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__20);
l_Lean_Compiler_LCNF_builtinPassManager___closed__21 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__21);
l_Lean_Compiler_LCNF_builtinPassManager___closed__22 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__22);
l_Lean_Compiler_LCNF_builtinPassManager___closed__23 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__23);
l_Lean_Compiler_LCNF_builtinPassManager___closed__24 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__24);
l_Lean_Compiler_LCNF_builtinPassManager___closed__25 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__25);
l_Lean_Compiler_LCNF_builtinPassManager___closed__26 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__26);
l_Lean_Compiler_LCNF_builtinPassManager___closed__27 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__27);
l_Lean_Compiler_LCNF_builtinPassManager___closed__28 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__28);
l_Lean_Compiler_LCNF_builtinPassManager___closed__29 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__29);
l_Lean_Compiler_LCNF_builtinPassManager___closed__30 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__30);
l_Lean_Compiler_LCNF_builtinPassManager___closed__31 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__31();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__31);
l_Lean_Compiler_LCNF_builtinPassManager___closed__32 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__32();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__32);
l_Lean_Compiler_LCNF_builtinPassManager___closed__33 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__33();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__33);
l_Lean_Compiler_LCNF_builtinPassManager___closed__34 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__34();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__34);
l_Lean_Compiler_LCNF_builtinPassManager___closed__35 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__35();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__35);
l_Lean_Compiler_LCNF_builtinPassManager___closed__36 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__36();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__36);
l_Lean_Compiler_LCNF_builtinPassManager___closed__37 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__37();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__37);
l_Lean_Compiler_LCNF_builtinPassManager___closed__38 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__38();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__38);
l_Lean_Compiler_LCNF_builtinPassManager___closed__39 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__39();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__39);
l_Lean_Compiler_LCNF_builtinPassManager___closed__40 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__40();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__40);
l_Lean_Compiler_LCNF_builtinPassManager___closed__41 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__41();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__41);
l_Lean_Compiler_LCNF_builtinPassManager___closed__42 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__42();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__42);
l_Lean_Compiler_LCNF_builtinPassManager___closed__43 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__43();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__43);
l_Lean_Compiler_LCNF_builtinPassManager___closed__44 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__44();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__44);
l_Lean_Compiler_LCNF_builtinPassManager___closed__45 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__45();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__45);
l_Lean_Compiler_LCNF_builtinPassManager___closed__46 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__46();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__46);
l_Lean_Compiler_LCNF_builtinPassManager___closed__47 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__47();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__47);
l_Lean_Compiler_LCNF_builtinPassManager___closed__48 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__48();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__48);
l_Lean_Compiler_LCNF_builtinPassManager___closed__49 = _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__49();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager___closed__49);
l_Lean_Compiler_LCNF_builtinPassManager = _init_l_Lean_Compiler_LCNF_builtinPassManager();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_599_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_599_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_599_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_599_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_599_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_599_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_599_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_passManagerExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_passManagerExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0);
l_Lean_Compiler_LCNF_getPassManager___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getPassManager___redArg___closed__1);
l_Lean_Compiler_LCNF_getPassManager___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getPassManager___redArg___closed__2);
l_Lean_Compiler_LCNF_addPass___closed__0 = _init_l_Lean_Compiler_LCNF_addPass___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__0);
l_Lean_Compiler_LCNF_addPass___closed__1 = _init_l_Lean_Compiler_LCNF_addPass___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__1);
l_Lean_Compiler_LCNF_addPass___closed__2 = _init_l_Lean_Compiler_LCNF_addPass___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__2);
l_Lean_Compiler_LCNF_addPass___closed__3 = _init_l_Lean_Compiler_LCNF_addPass___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__3);
l_Lean_Compiler_LCNF_addPass___closed__4 = _init_l_Lean_Compiler_LCNF_addPass___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__4);
l_Lean_Compiler_LCNF_addPass___closed__5 = _init_l_Lean_Compiler_LCNF_addPass___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__5);
l_Lean_Compiler_LCNF_addPass___closed__6 = _init_l_Lean_Compiler_LCNF_addPass___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__6);
l_Lean_Compiler_LCNF_addPass___closed__7 = _init_l_Lean_Compiler_LCNF_addPass___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__7);
l_Lean_Compiler_LCNF_initFn___lam__0___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___lam__0___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___lam__0___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___lam__0___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___lam__0___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___lam__0___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___lam__1___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___lam__1___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___lam__1___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___lam__1___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___lam__1___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___lam__1___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Passes___hyg_958_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Passes___hyg_958_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Passes___hyg_958_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_958_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_1106_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_1106_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Passes___hyg_1106_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_1106_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_1106_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Passes___hyg_1106_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_1106_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_1106_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Passes___hyg_1106_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_1106_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_1106_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Passes___hyg_1106_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1106_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
