// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: Init Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.CSE Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.PullFunDecls Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.JoinPoints Lean.Compiler.LCNF.Specialize Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.ToMono Lean.Compiler.LCNF.LambdaLifting Lean.Compiler.LCNF.FloatLetIn Lean.Compiler.LCNF.ReduceArity Lean.Compiler.LCNF.ElimDeadBranches
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
lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_init___closed__2;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__9;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__26;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__18;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__22;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__10;
static lean_object* l_Lean_Compiler_LCNF_saveBase___closed__4;
static lean_object* l_Lean_Compiler_LCNF_saveBase___closed__1;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__33;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__19;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__21;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__27;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_init___elambda__1___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__32;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__4;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__34;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__10;
static lean_object* l_Lean_Compiler_LCNF_init___closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__16;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__4___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__8;
extern lean_object* l_Lean_Compiler_LCNF_lambdaLifting;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256_(lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__2;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__30;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__3(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_saveMono___closed__1;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__2;
static lean_object* l_Lean_Compiler_LCNF_saveMono___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__6;
static lean_object* l_Lean_Compiler_LCNF_saveBase___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__6;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__13;
extern lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__7;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__48;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__4;
extern lean_object* l_Lean_Compiler_LCNF_reduceArity;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__24;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_init___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__5;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__6;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportM_runCoreM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__12;
extern lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__31;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__9;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__47;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__38;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__11;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__22;
lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__44;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__37;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__21;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__7;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__1;
lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__19;
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__8;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__39;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__13;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__5;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076_(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_findJoinPoints;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3;
static lean_object* l_Lean_Compiler_LCNF_saveMono___closed__2;
static lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_pullInstances;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace(uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_elimDeadBranches;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_saveBase___closed__3;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__7;
lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_passManagerExt;
static lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_toMono;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__5;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__12;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__23;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__20;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__2;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__40;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_declareBuiltin___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_pullFunDecls;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__35;
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__15;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__9;
static lean_object* l_Lean_Compiler_LCNF_saveMono___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__4(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__36;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__6;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__5;
static lean_object* l_Lean_Compiler_LCNF_trace___closed__3;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__17;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__20;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__43;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__11;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__46;
static lean_object* l_Lean_Compiler_LCNF_init___closed__3;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_builtinPassManager;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__9;
static lean_object* l_Lean_Compiler_LCNF_init___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__8;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__16;
lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__17;
static lean_object* l_Lean_Compiler_LCNF_trace___closed__2;
uint8_t l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_367_(uint8_t, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__4;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__41;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__4;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__7;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPassManager;
static lean_object* l_Lean_Compiler_LCNF_addPass___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__28;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__29;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__25;
static lean_object* l_Lean_Compiler_LCNF_trace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_specialize;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__45;
static lean_object* l_Lean_Compiler_LCNF_builtinPassManager___closed__42;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_init___elambda__1___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_Compiler_LCNF_Decl_saveBase(x_11, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_init___elambda__1___spec__1(x_1, x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("init", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_init___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_init___elambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Lean_Compiler_LCNF_init___closed__2;
x_4 = l_Lean_Compiler_LCNF_init___closed__3;
x_5 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_init___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_init___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_init___elambda__1___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_init___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trace", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_trace___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_trace___elambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_trace___closed__2;
x_4 = l_Lean_Compiler_LCNF_trace___closed__3;
x_5 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_trace___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_Decl_saveBase(x_8, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("saveBase", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_saveBase___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveBase___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_saveBase___closed__2;
x_2 = l_Lean_Compiler_LCNF_saveBase___closed__3;
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_saveBase___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_saveBase___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_Decl_saveMono(x_8, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("saveMono", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_saveMono___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveMono___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_saveMono___closed__2;
x_2 = l_Lean_Compiler_LCNF_saveMono___closed__3;
x_3 = 1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_saveMono___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_saveMono___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_cse(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
lean_ctor_set_uint8(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_floatLetIn(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_reduceJpArity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
lean_ctor_set_uint8(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__6;
x_2 = lean_unsigned_to_nat(1u);
x_3 = 0;
x_4 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Compiler_LCNF_cse(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
x_2 = lean_unsigned_to_nat(3u);
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_reduceJpArity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 1;
x_3 = l_Lean_Compiler_LCNF_extendJoinPointContext(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Compiler_LCNF_floatLetIn(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
x_2 = lean_unsigned_to_nat(4u);
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Compiler_LCNF_floatLetIn(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = l_Lean_Compiler_LCNF_extendJoinPointContext(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__2;
x_2 = lean_unsigned_to_nat(5u);
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Compiler_LCNF_cse(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(29u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__19;
x_2 = l_Lean_Compiler_LCNF_init;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__20;
x_2 = l_Lean_Compiler_LCNF_pullInstances;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__21;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__22;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__23;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__24;
x_2 = l_Lean_Compiler_LCNF_findJoinPoints;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__25;
x_2 = l_Lean_Compiler_LCNF_pullFunDecls;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__26;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__27;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__28;
x_2 = l_Lean_Compiler_LCNF_eagerLambdaLifting;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__29;
x_2 = l_Lean_Compiler_LCNF_specialize;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__30;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__31;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__9;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__32;
x_2 = l_Lean_Compiler_LCNF_saveBase;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__33;
x_2 = l_Lean_Compiler_LCNF_toMono;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__34;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__35;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__36;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__37;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__38;
x_2 = l_Lean_Compiler_LCNF_reduceArity;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__39;
x_2 = l_Lean_Compiler_LCNF_commonJoinPointArgs;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__40;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__41;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__15;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__42;
x_2 = l_Lean_Compiler_LCNF_elimDeadBranches;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__43;
x_2 = l_Lean_Compiler_LCNF_lambdaLifting;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__44;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__45;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__46;
x_2 = l_Lean_Compiler_LCNF_builtinPassManager___closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__47;
x_2 = l_Lean_Compiler_LCNF_saveMono;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_builtinPassManager___closed__48;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__1(x_10, x_12, x_13, x_4, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_15;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_builtinPassManager;
x_9 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__2(x_1, x_6, x_7, x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_runImportedDecls___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_runImportedDecls___boxed), 4, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_ImportM_runCoreM___rarg(x_5, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_List_reverse___rarg(x_2);
x_4 = l_List_redLength___rarg(x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = l_List_toArrayAux___rarg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("passManagerExt", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
x_3 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_builtinPassManager;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__6;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__3), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__4___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__1___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__5;
x_5 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__7;
x_6 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__8;
x_7 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__9;
x_8 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__10;
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_9, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getPassManager___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_instInhabitedPassManager;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_passManagerExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_getPassManager___rarg___closed__1;
x_8 = l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2;
x_9 = l_Lean_PersistentEnvExtension_getState___rarg(x_7, x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_getPassManager___rarg___closed__1;
x_15 = l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2;
x_16 = l_Lean_PersistentEnvExtension_getState___rarg(x_14, x_15, x_13);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getPassManager___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_getPassManager___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_getPassManager(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'cpass' only 'PassInstaller's can be added via the 'cpass' attribute: ", 78);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PassInstaller", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_addPass___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_addPass___closed__8;
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
x_5 = l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_ConstantInfo_type(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_20 = l_Lean_MessageData_ofExpr(x_8);
x_21 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_24, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
x_27 = lean_string_dec_eq(x_16, x_26);
lean_dec(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_28 = l_Lean_MessageData_ofExpr(x_8);
x_29 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_32, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3;
x_35 = lean_string_dec_eq(x_15, x_34);
lean_dec(x_15);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
lean_dec(x_1);
x_36 = l_Lean_MessageData_ofExpr(x_8);
x_37 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_40, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Compiler_LCNF_addPass___closed__5;
x_43 = lean_string_dec_eq(x_14, x_42);
lean_dec(x_14);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_44 = l_Lean_MessageData_ofExpr(x_8);
x_45 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_48, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
x_50 = l_Lean_Compiler_LCNF_getPassManager___rarg(x_3, x_7);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_3);
lean_inc(x_1);
x_53 = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(x_51, x_1, x_2, x_3, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_take(x_3, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_54);
x_61 = l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2;
x_62 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_61, x_59, x_60);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 6);
lean_inc(x_67);
lean_dec(x_57);
x_68 = l_Lean_Compiler_LCNF_addPass___closed__9;
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_63);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_65);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set(x_69, 5, x_66);
lean_ctor_set(x_69, 6, x_67);
x_70 = lean_st_ref_set(x_3, x_69, x_58);
lean_dec(x_3);
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
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_53);
if (x_77 == 0)
{
return x_53;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_53, 0);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_53);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_81 = l_Lean_MessageData_ofExpr(x_8);
x_82 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_85, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_87 = l_Lean_MessageData_ofExpr(x_8);
x_88 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_91, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_93 = l_Lean_MessageData_ofExpr(x_8);
x_94 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_97, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_99 = l_Lean_MessageData_ofExpr(x_8);
x_100 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_103, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_9);
lean_dec(x_1);
x_105 = l_Lean_MessageData_ofExpr(x_8);
x_106 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_109, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_1);
x_111 = l_Lean_MessageData_ofExpr(x_8);
x_112 = l_Lean_Compiler_LCNF_addPass___closed__2;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Compiler_LCNF_addPass___closed__4;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_115, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_5);
if (x_117 == 0)
{
return x_5;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_5, 0);
x_119 = lean_ctor_get(x_5, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_5);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_addPass(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid attribute 'cpass', must be global", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_367_(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__2;
x_12 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(x_11, x_4, x_5, x_8);
lean_dec(x_5);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__1(x_1, x_17, x_4, x_5, x_8);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attribute cannot be erased", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__1;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__2;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__3;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__8;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Passes", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__10;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__14;
x_2 = lean_unsigned_to_nat(1076u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cpass", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compiler passes for the code generator", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__15;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__17;
x_3 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__18;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__19;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__20;
x_3 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__22;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
x_2 = l_Lean_Compiler_LCNF_saveBase___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__14;
x_2 = lean_unsigned_to_nat(1256u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
x_2 = l_Lean_Compiler_LCNF_saveMono___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2;
x_2 = l_Lean_Compiler_LCNF_trace___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__1;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__3;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__4;
x_11 = l_Lean_registerTraceClass(x_10, x_3, x_4, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Compiler_LCNF_init___closed__1 = _init_l_Lean_Compiler_LCNF_init___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_init___closed__1);
l_Lean_Compiler_LCNF_init___closed__2 = _init_l_Lean_Compiler_LCNF_init___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_init___closed__2);
l_Lean_Compiler_LCNF_init___closed__3 = _init_l_Lean_Compiler_LCNF_init___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_init___closed__3);
l_Lean_Compiler_LCNF_init___closed__4 = _init_l_Lean_Compiler_LCNF_init___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_init___closed__4);
l_Lean_Compiler_LCNF_init = _init_l_Lean_Compiler_LCNF_init();
lean_mark_persistent(l_Lean_Compiler_LCNF_init);
l_Lean_Compiler_LCNF_trace___closed__1 = _init_l_Lean_Compiler_LCNF_trace___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_trace___closed__1);
l_Lean_Compiler_LCNF_trace___closed__2 = _init_l_Lean_Compiler_LCNF_trace___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_trace___closed__2);
l_Lean_Compiler_LCNF_trace___closed__3 = _init_l_Lean_Compiler_LCNF_trace___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_trace___closed__3);
l_Lean_Compiler_LCNF_saveBase___closed__1 = _init_l_Lean_Compiler_LCNF_saveBase___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase___closed__1);
l_Lean_Compiler_LCNF_saveBase___closed__2 = _init_l_Lean_Compiler_LCNF_saveBase___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase___closed__2);
l_Lean_Compiler_LCNF_saveBase___closed__3 = _init_l_Lean_Compiler_LCNF_saveBase___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase___closed__3);
l_Lean_Compiler_LCNF_saveBase___closed__4 = _init_l_Lean_Compiler_LCNF_saveBase___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase___closed__4);
l_Lean_Compiler_LCNF_saveBase = _init_l_Lean_Compiler_LCNF_saveBase();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase);
l_Lean_Compiler_LCNF_saveMono___closed__1 = _init_l_Lean_Compiler_LCNF_saveMono___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono___closed__1);
l_Lean_Compiler_LCNF_saveMono___closed__2 = _init_l_Lean_Compiler_LCNF_saveMono___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono___closed__2);
l_Lean_Compiler_LCNF_saveMono___closed__3 = _init_l_Lean_Compiler_LCNF_saveMono___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono___closed__3);
l_Lean_Compiler_LCNF_saveMono___closed__4 = _init_l_Lean_Compiler_LCNF_saveMono___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono___closed__4);
l_Lean_Compiler_LCNF_saveMono = _init_l_Lean_Compiler_LCNF_saveMono();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono);
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
l_Lean_Compiler_LCNF_builtinPassManager = _init_l_Lean_Compiler_LCNF_builtinPassManager();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634____closed__10);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_634_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_passManagerExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_passManagerExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_getPassManager___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_getPassManager___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getPassManager___rarg___closed__1);
l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2 = _init_l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getPassManager___rarg___closed__2);
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
l_Lean_Compiler_LCNF_addPass___closed__8 = _init_l_Lean_Compiler_LCNF_addPass___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__8);
l_Lean_Compiler_LCNF_addPass___closed__9 = _init_l_Lean_Compiler_LCNF_addPass___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_addPass___closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__2___closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____lambda__3___closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__18);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__19 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__19);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__20 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__20);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__21 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__21);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__22 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076____closed__22);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1076_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256____closed__4);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_1256_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
