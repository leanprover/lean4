// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM Lean.Compiler.IR.CtorLayout Lean.CoreM Lean.Environment
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
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__32;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__5;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__21;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__31;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__39;
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__0;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__33;
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__5;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__30;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__0____x40_Lean_Compiler_IR_ToIR___hyg_1189_;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
static lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__38;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Environment_addExtraName(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__3;
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__15;
static lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__19;
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__13;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__29;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__23;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedCtorInfo;
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__1;
extern lean_object* l_Lean_IR_declMapExt;
static lean_object* l_Lean_IR_ToIR_lowerType___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__2;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__3;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__2;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_ctorInfoExt;
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__14;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__11;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__6;
static lean_object* l_Lean_IR_ToIR_lowerType___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__18;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__22;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__7;
static lean_object* l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__35;
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__0;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__0;
lean_object* l_List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
static lean_object* l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__2;
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__26;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__8;
static lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__1;
static lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_scalarTypeExt;
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__7;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__24;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__37;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_get_ctor_layout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__27;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__17;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__6;
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__28;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_uint16_to_nat(uint16_t);
static lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo_fillCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_getCtorInfo_fillCache_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__4;
static lean_object* l_Lean_IR_ToIR_getCtorInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__9;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__36;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__34;
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIR___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_1189_(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__3;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__20;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_dummy_extern_decl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__25;
static lean_object* l_Lean_IR_ToIR_lowerType___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__10;
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_M_run___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_M_run___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_IR_ToIR_M_run___redArg___closed__5;
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_apply_4(x_1, x_7, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_9 = x_5;
} else {
 lean_dec_ref(x_5);
 x_9 = lean_box(0);
}
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_21, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = lean_ctor_get(x_7, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_7, 0);
lean_dec(x_39);
lean_inc(x_8);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_8);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_20, x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_35);
x_44 = lean_array_uset(x_21, x_34, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_44);
lean_ctor_set(x_7, 1, x_51);
lean_ctor_set(x_7, 0, x_42);
x_10 = x_7;
goto block_19;
}
else
{
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_42);
x_10 = x_7;
goto block_19;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_7);
lean_inc(x_8);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_8);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_20, x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_35);
x_56 = lean_array_uset(x_21, x_34, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_63);
x_10 = x_64;
goto block_19;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_56);
x_10 = x_65;
goto block_19;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
x_10 = x_7;
goto block_19;
}
block_19:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_8, x_11);
if (lean_is_scalar(x_9)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_9;
}
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_st_ref_set(x_2, x_13, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_box(0);
x_22 = lean_array_get_size(x_12);
x_23 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_12, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = lean_ctor_get(x_7, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_7, 0);
lean_dec(x_39);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_11, x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_35);
x_44 = lean_array_uset(x_12, x_34, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_44);
lean_ctor_set(x_7, 1, x_51);
lean_ctor_set(x_7, 0, x_42);
x_14 = x_7;
goto block_21;
}
else
{
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_42);
x_14 = x_7;
goto block_21;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_7);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_2);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_11, x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_35);
x_56 = lean_array_uset(x_12, x_34, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_63);
x_14 = x_64;
goto block_21;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_56);
x_14 = x_65;
goto block_21;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_14 = x_7;
goto block_21;
}
block_21:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
if (lean_is_scalar(x_10)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_10;
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_st_ref_set(x_3, x_15, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_ctor_set(x_4, 1, x_9);
x_10 = lean_st_ref_set(x_1, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_st_ref_set(x_1, x_19, x_5);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_newVar___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_9 = x_5;
} else {
 lean_dec_ref(x_5);
 x_9 = lean_box(0);
}
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_21, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = lean_ctor_get(x_7, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_7, 0);
lean_dec(x_39);
lean_inc(x_8);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_8);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_20, x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_35);
x_44 = lean_array_uset(x_21, x_34, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_44);
lean_ctor_set(x_7, 1, x_51);
lean_ctor_set(x_7, 0, x_42);
x_10 = x_7;
goto block_19;
}
else
{
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_42);
x_10 = x_7;
goto block_19;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_7);
lean_inc(x_8);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_8);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_20, x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_35);
x_56 = lean_array_uset(x_21, x_34, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_63);
x_10 = x_64;
goto block_19;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_56);
x_10 = x_65;
goto block_19;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
x_10 = x_7;
goto block_19;
}
block_19:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_8, x_11);
if (lean_is_scalar(x_9)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_9;
}
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_st_ref_set(x_2, x_13, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_9 = x_5;
} else {
 lean_dec_ref(x_5);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = lean_box(0);
x_21 = lean_array_get_size(x_11);
x_22 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_23 = 32;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = 16;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_31 = 1;
x_32 = lean_usize_sub(x_30, x_31);
x_33 = lean_usize_land(x_29, x_32);
x_34 = lean_array_uget(x_11, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_37 = lean_ctor_get(x_6, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_6, 0);
lean_dec(x_38);
x_39 = lean_box(2);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_10, x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_34);
x_43 = lean_array_uset(x_11, x_33, x_42);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_nat_mul(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_43);
lean_ctor_set(x_6, 1, x_50);
lean_ctor_set(x_6, 0, x_41);
x_13 = x_6;
goto block_20;
}
else
{
lean_ctor_set(x_6, 1, x_43);
lean_ctor_set(x_6, 0, x_41);
x_13 = x_6;
goto block_20;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_6);
x_51 = lean_box(2);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_10, x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_34);
x_55 = lean_array_uset(x_11, x_33, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
x_13 = x_63;
goto block_20;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_55);
x_13 = x_64;
goto block_20;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_13 = x_6;
goto block_20;
}
block_20:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_9;
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_st_ref_set(x_2, x_14, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ir_find_env_decl(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ir_find_env_decl(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declMapExt;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_30; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 7);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 8);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
x_16 = l_Lean_IR_ToIR_addDecl___redArg___closed__0;
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_17 = x_30;
goto block_29;
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l_Lean_Environment_addExtraName(x_7, x_17);
x_19 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_16, x_18, x_1);
x_20 = l_Lean_IR_ToIR_addDecl___redArg___closed__3;
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(0, 9, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_10);
lean_ctor_set(x_21, 4, x_11);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_21, 6, x_12);
lean_ctor_set(x_21, 7, x_13);
lean_ctor_set(x_21, 8, x_14);
x_22 = lean_st_ref_set(x_2, x_21, x_6);
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
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* x_1) {
_start:
{
uint64_t x_2; 
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
case 2:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_13 = lean_uint8_to_nat(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
case 3:
{
uint16_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get_uint16(x_1, 0);
lean_dec(x_1);
x_16 = lean_uint16_to_nat(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 4:
{
uint32_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get_uint32(x_1, 0);
lean_dec(x_1);
x_19 = lean_uint32_to_nat(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
default: 
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_2 = x_21;
goto block_5;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_uint64_to_nat(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
static lean_object* _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Data.PersistentHashMap", 27, 27);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.PersistentHashMap.find!", 28, 28);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not in the map", 21, 21);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(170u);
x_4 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__1;
x_5 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_10 = x_3;
} else {
 lean_dec_ref(x_3);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_6);
lean_ctor_set(x_4, 1, x_8);
lean_inc(x_6);
x_17 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_11, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3;
lean_inc(x_2);
x_19 = lean_panic_fn(x_2, x_18);
x_12 = x_19;
goto block_16;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_12 = x_20;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_9, x_6, x_12);
if (lean_is_scalar(x_10)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_10;
}
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_3 = x_14;
x_4 = x_7;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_33; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_25 = x_3;
} else {
 lean_dec_ref(x_3);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_23);
lean_inc(x_21);
x_33 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_26, x_21);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3;
lean_inc(x_2);
x_35 = lean_panic_fn(x_2, x_34);
x_28 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_28 = x_36;
goto block_32;
}
block_32:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_24, x_21, x_28);
if (lean_is_scalar(x_25)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_25;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_3 = x_30;
x_4 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_10 = x_3;
} else {
 lean_dec_ref(x_3);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_6);
lean_ctor_set(x_4, 1, x_8);
lean_inc(x_6);
x_17 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_11, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3;
lean_inc(x_2);
x_19 = lean_panic_fn(x_2, x_18);
x_12 = x_19;
goto block_16;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_12 = x_20;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_9, x_6, x_12);
if (lean_is_scalar(x_10)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_10;
}
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg(x_1, x_2, x_14, x_7);
return x_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_33; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_25 = x_3;
} else {
 lean_dec_ref(x_3);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_23);
lean_inc(x_21);
x_33 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_26, x_21);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3;
lean_inc(x_2);
x_35 = lean_panic_fn(x_2, x_34);
x_28 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_28 = x_36;
goto block_32;
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_24, x_21, x_28);
if (lean_is_scalar(x_25)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_25;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg(x_1, x_2, x_30, x_22);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_List_lengthTR___redArg(x_6);
x_9 = l_List_lengthTR___redArg(x_7);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___closed__0;
lean_inc(x_6);
x_12 = l_List_takeTR_go___redArg(x_6, x_6, x_10, x_11);
lean_dec(x_6);
x_13 = l_List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0___redArg(x_3, x_1, x_5, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__1), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_registerEnvExtension___redArg(x_5, x_6, x_8, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_18 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = lean_box(0);
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_35 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = lean_box(0);
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_55 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = lean_box(0);
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, x_5);
return x_68;
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerEnumToScalarType.fillCache", 44, 44);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected valid constructor name", 31, 31);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__2;
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_unsigned_to_nat(91u);
x_4 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__1;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_2);
x_29 = l_Lean_Environment_find_x3f(x_2, x_12, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_free_object(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
goto block_26;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 6)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Expr_isForall(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_free_object(x_4);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_13;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_36 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__4;
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
else
{
lean_dec(x_30);
lean_free_object(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
goto block_26;
}
}
block_26:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__3;
x_19 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0(x_18, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_13;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_8 = x_20;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_53 = lean_box(0);
x_54 = lean_unbox(x_53);
lean_inc(x_2);
x_55 = l_Lean_Environment_find_x3f(x_2, x_38, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
goto block_52;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 6)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Expr_isForall(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_inc(x_1);
{
lean_object* _tmp_3 = x_39;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_62 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__4;
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_9);
return x_64;
}
}
else
{
lean_dec(x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
goto block_52;
}
}
block_52:
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__3;
x_45 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0(x_44, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_39;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_8 = x_46;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(3);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_4, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_inc(x_13);
x_16 = l_Lean_Environment_find_x3f(x_13, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = x_12;
goto block_9;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__0;
lean_inc(x_19);
x_22 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg(x_21, x_13, x_20, x_19, x_21, x_2, x_3, x_4, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_List_lengthTR___redArg(x_19);
lean_dec(x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(256u);
x_31 = lean_nat_dec_lt(x_27, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(65536u);
x_33 = lean_nat_dec_lt(x_27, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_cstr_to_nat("4294967296");
x_35 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_27);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
lean_ctor_set(x_22, 0, x_36);
return x_22;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__1;
lean_ctor_set(x_22, 0, x_37);
return x_22;
}
}
else
{
lean_object* x_38; 
lean_dec(x_27);
x_38 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__2;
lean_ctor_set(x_22, 0, x_38);
return x_22;
}
}
else
{
lean_object* x_39; 
lean_dec(x_27);
x_39 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__3;
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; 
lean_dec(x_27);
x_40 = lean_box(0);
lean_ctor_set(x_22, 0, x_40);
return x_22;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l_List_lengthTR___redArg(x_19);
lean_dec(x_19);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_unsigned_to_nat(256u);
x_46 = lean_nat_dec_lt(x_42, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(65536u);
x_48 = lean_nat_dec_lt(x_42, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_cstr_to_nat("4294967296");
x_50 = lean_nat_dec_lt(x_42, x_49);
lean_dec(x_42);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__1;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_42);
x_55 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__2;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_41);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_42);
x_57 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__3;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_41);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_19);
x_61 = !lean_is_exclusive(x_22);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_22, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_24, 0);
lean_inc(x_63);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_63);
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_dec(x_22);
x_65 = lean_ctor_get(x_24, 0);
lean_inc(x_65);
lean_dec(x_24);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_19);
x_67 = !lean_is_exclusive(x_22);
if (x_67 == 0)
{
return x_22;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_22, 0);
x_69 = lean_ctor_get(x_22, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_22);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = x_12;
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__1;
x_2 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__0;
x_3 = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_10 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__3;
x_11 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_10, x_1, x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_12, x_2);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_18 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__3;
x_19 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_18, x_1, x_16, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_20, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg(x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_6, x_1, x_2);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_10, x_1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 5);
lean_dec(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
x_14 = l_Lean_EnvExtension_modifyState___redArg(x_1, x_10, x_13, x_12);
x_15 = l_Lean_IR_ToIR_addDecl___redArg___closed__3;
lean_ctor_set(x_7, 5, x_15);
lean_ctor_set(x_7, 0, x_14);
x_16 = lean_st_ref_set(x_4, x_7, x_8);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
x_27 = lean_ctor_get(x_7, 4);
x_28 = lean_ctor_get(x_7, 6);
x_29 = lean_ctor_get(x_7, 7);
x_30 = lean_ctor_get(x_7, 8);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_32 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(x_32, 0, x_2);
lean_closure_set(x_32, 1, x_3);
x_33 = l_Lean_EnvExtension_modifyState___redArg(x_1, x_23, x_32, x_31);
x_34 = l_Lean_IR_ToIR_addDecl___redArg___closed__3;
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_28);
lean_ctor_set(x_35, 7, x_29);
lean_ctor_set(x_35, 8, x_30);
x_36 = lean_st_ref_set(x_4, x_35, x_8);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_scalarTypeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_ToIR_lowerEnumToScalarType___closed__0;
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg(x_6, x_1, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache(x_1, x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(x_6, x_1, x_11, x_4, x_12);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_18 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = lean_box(0);
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_35 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = lean_box(0);
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_55 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = lean_box(0);
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, x_5);
return x_68;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt8", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt16", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt64", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("USize", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Float", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Float32", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerType", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid type", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerType___closed__10;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(131u);
x_4 = l_Lean_IR_ToIR_lowerType___closed__9;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
x_36 = l_Lean_IR_ToIR_lowerType___closed__0;
x_37 = lean_string_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_IR_ToIR_lowerType___closed__1;
x_39 = lean_string_dec_eq(x_35, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_IR_ToIR_lowerType___closed__2;
x_41 = lean_string_dec_eq(x_35, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_IR_ToIR_lowerType___closed__3;
x_43 = lean_string_dec_eq(x_35, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_IR_ToIR_lowerType___closed__4;
x_45 = lean_string_dec_eq(x_35, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_IR_ToIR_lowerType___closed__5;
x_47 = lean_string_dec_eq(x_35, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_IR_ToIR_lowerType___closed__6;
x_49 = lean_string_dec_eq(x_35, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_IR_ToIR_lowerType___closed__7;
x_51 = lean_string_dec_eq(x_35, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_IR_ToIR_lowerType___closed__8;
x_53 = lean_string_dec_eq(x_35, x_52);
lean_dec(x_35);
if (x_53 == 0)
{
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_33;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(6);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_5);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(9);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_5);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_5);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(4);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_5);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_box(2);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
}
else
{
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = x_5;
goto block_9;
}
}
else
{
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = x_5;
goto block_9;
}
}
else
{
lean_dec(x_34);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_33;
}
}
else
{
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_33;
}
block_33:
{
lean_object* x_15; 
x_15 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(7);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
case 5:
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
if (lean_obj_tag(x_68) == 4)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_69, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
x_74 = lean_box(7);
lean_ctor_set(x_70, 0, x_74);
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_box(7);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_70, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
lean_dec(x_71);
lean_ctor_set(x_70, 0, x_80);
return x_70;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_70, 1);
lean_inc(x_81);
lean_dec(x_70);
x_82 = lean_ctor_get(x_71, 0);
lean_inc(x_82);
lean_dec(x_71);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_70);
if (x_84 == 0)
{
return x_70;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_70, 0);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_70);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_68);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_box(7);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_5);
return x_89;
}
}
case 7:
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(7);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_5);
return x_91;
}
default: 
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_1);
x_92 = l_Lean_IR_ToIR_lowerType___closed__11;
x_93 = l_panic___at___Lean_IR_ToIR_lowerType_spec__0(x_92, x_2, x_3, x_4, x_5);
return x_93;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__0____x40_Lean_Compiler_IR_ToIR___hyg_1189_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_initFn___closed__0____x40_Lean_Compiler_IR_ToIR___hyg_1189_;
x_2 = l_Lean_IR_instInhabitedCtorInfo;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_1189_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_;
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_getCtorInfo_fillCache_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_18 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_;
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_35 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_;
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_55 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_;
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, x_5);
return x_68;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.getCtorInfo.fillCache", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unrecognized constructor", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__1;
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_unsigned_to_nat(153u);
x_4 = l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo_fillCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_ir_get_ctor_layout(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_11);
lean_free_object(x_6);
lean_dec(x_1);
x_12 = l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__2;
x_13 = l_panic___at___Lean_IR_ToIR_getCtorInfo_fillCache_spec__0(x_12, x_2, x_3, x_4, x_9);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_1);
x_18 = lean_array_mk(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 2);
x_23 = lean_ctor_get(x_14, 3);
x_24 = lean_ctor_get(x_14, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_array_mk(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_6);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ir_get_ctor_layout(x_30, x_1);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_31);
lean_dec(x_1);
x_32 = l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__2;
x_33 = l_panic___at___Lean_IR_ToIR_getCtorInfo_fillCache_spec__0(x_32, x_2, x_3, x_4, x_29);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 4);
lean_inc(x_39);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 x_40 = x_34;
} else {
 lean_dec_ref(x_34);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 5, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_39);
x_42 = lean_array_mk(x_36);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_getCtorInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_ctorInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_ToIR_getCtorInfo___closed__0;
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg(x_6, x_1, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_IR_ToIR_getCtorInfo_fillCache(x_1, x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(x_6, x_1, x_11, x_4, x_12);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_18 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = l_Lean_IR_instInhabitedArg;
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_35 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = l_Lean_IR_instInhabitedArg;
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_55 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = l_Lean_IR_instInhabitedArg;
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, x_5);
return x_68;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerArg", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected value", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(161u);
x_4 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_st_ref_get(x_2, x_5);
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
x_15 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_6);
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
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_6, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_7);
x_29 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_30 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_29, x_2, x_3, x_4, x_11);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
switch (lean_obj_tag(x_31)) {
case 0:
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_free_object(x_7);
x_35 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_36 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_35, x_2, x_3, x_4, x_11);
return x_36;
}
default: 
{
lean_object* x_37; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_box(1);
lean_ctor_set(x_7, 0, x_37);
return x_7;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_dec(x_7);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_array_get_size(x_39);
x_41 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_6);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_39, x_52);
lean_dec(x_39);
x_54 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_6, x_53);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_56 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_55, x_2, x_3, x_4, x_38);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_38);
return x_61;
}
case 1:
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
x_62 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_63 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_62, x_2, x_3, x_4, x_38);
return x_63;
}
default: 
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_38);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_box(1);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1;
x_2 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerProj___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(6);
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_Lean_IR_ToIR_lowerProj___closed__0;
return x_4;
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_box(7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
case 2:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_17);
x_18 = lean_box(5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_box(5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
default: 
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_3, 2);
x_27 = lean_ctor_get(x_3, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_ctor_get(x_2, 3);
x_30 = lean_nat_add(x_28, x_29);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 0, x_30);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_ctor_get(x_3, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_2, 3);
x_37 = lean_nat_add(x_35, x_36);
x_38 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerProj(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_9 = l_Lean_IR_ToIR_bindVar___redArg(x_6, x_2, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_IR_ToIR_lowerType(x_7, x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_8);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_18 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = lean_box(13);
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_35 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = lean_box(13);
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1;
x_55 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2;
lean_inc(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = lean_box(13);
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, x_5);
return x_68;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerAlt.loop", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mismatched fields and params", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerAlt_loop___closed__1;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(395u);
x_4 = l_Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_48; lean_object* x_55; uint8_t x_56; 
x_55 = lean_array_get_size(x_4);
x_56 = lean_nat_dec_lt(x_6, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_48 = x_57;
goto block_54;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_array_fget(x_4, x_6);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_48 = x_59;
goto block_54;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_IR_ToIR_lowerAlt_loop___closed__2;
x_16 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_15, x_11, x_12, x_13, x_14);
return x_16;
}
block_47:
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_IR_ToIR_lowerCode(x_2, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_dec(x_19);
lean_dec(x_2);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
goto block_17;
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_1);
x_23 = l_Lean_IR_ToIR_lowerProj(x_1, x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_IR_ToIR_bindVar___redArg(x_27, x_7, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_6, x_31);
lean_dec(x_6);
x_33 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_32, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_26);
lean_ctor_set(x_39, 3, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
return x_33;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_23);
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = l_Lean_IR_ToIR_bindErased___redArg(x_41, x_7, x_10);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_6, x_44);
lean_dec(x_6);
x_6 = x_45;
x_10 = x_43;
goto _start;
}
}
}
}
block_54:
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_array_get_size(x_5);
x_50 = lean_nat_dec_lt(x_6, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_18 = x_48;
x_19 = x_51;
goto block_47;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_array_fget(x_5, x_6);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_18 = x_48;
x_19 = x_53;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_IR_ToIR_lowerParam(x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_12);
x_2 = x_17;
x_3 = x_18;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_IR_ToIR_lowerArg(x_10, x_4, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_12);
x_2 = x_17;
x_3 = x_18;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_5(x_1, x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_16, x_3, x_13);
x_3 = x_18;
x_4 = x_19;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedArg;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(203u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(195u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all local functions should be λ-lifted", 39, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__3;
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(211u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(208u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_IR_ToIR_lowerLet(x_20, x_21, x_2, x_3, x_4, x_5);
return x_22;
}
case 1:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_24 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_23, x_2, x_3, x_4, x_5);
return x_24;
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 4);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_27, x_2, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_size(x_28);
x_34 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_33, x_34, x_28, x_2, x_3, x_4, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Lean_IR_ToIR_lowerCode(x_29, x_2, x_3, x_4, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_IR_ToIR_lowerCode(x_26, x_2, x_3, x_4, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 2, x_39);
lean_ctor_set(x_47, 3, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_31);
return x_41;
}
}
else
{
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
}
else
{
uint8_t x_49; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
case 3:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_st_ref_get(x_2, x_5);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
x_62 = lean_array_get_size(x_60);
x_63 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_53);
x_64 = 32;
x_65 = lean_uint64_shift_right(x_63, x_64);
x_66 = lean_uint64_xor(x_63, x_65);
x_67 = 16;
x_68 = lean_uint64_shift_right(x_66, x_67);
x_69 = lean_uint64_xor(x_66, x_68);
x_70 = lean_uint64_to_usize(x_69);
x_71 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_72 = 1;
x_73 = lean_usize_sub(x_71, x_72);
x_74 = lean_usize_land(x_70, x_73);
x_75 = lean_array_uget(x_60, x_74);
lean_dec(x_60);
x_76 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_53, x_75);
lean_dec(x_75);
lean_dec(x_53);
if (lean_obj_tag(x_76) == 0)
{
lean_free_object(x_57);
lean_dec(x_54);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_58;
goto block_19;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
switch (lean_obj_tag(x_77)) {
case 0:
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_77);
lean_free_object(x_57);
lean_dec(x_54);
x_78 = l_Lean_IR_ToIR_lowerCode___closed__2;
x_79 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_78, x_2, x_3, x_4, x_58);
return x_79;
}
case 1:
{
lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_array_size(x_54);
x_82 = 0;
x_83 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_81, x_82, x_54, x_2, x_3, x_4, x_58);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_ctor_set_tag(x_57, 12);
lean_ctor_set(x_57, 1, x_85);
lean_ctor_set(x_57, 0, x_80);
lean_ctor_set(x_83, 0, x_57);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_83, 0);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_83);
lean_ctor_set_tag(x_57, 12);
lean_ctor_set(x_57, 1, x_86);
lean_ctor_set(x_57, 0, x_80);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_57);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_80);
lean_free_object(x_57);
x_89 = !lean_is_exclusive(x_83);
if (x_89 == 0)
{
return x_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_83, 0);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_83);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
default: 
{
lean_free_object(x_57);
lean_dec(x_54);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_58;
goto block_19;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; size_t x_102; size_t x_103; size_t x_104; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; 
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_dec(x_57);
x_94 = lean_array_get_size(x_93);
x_95 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_53);
x_96 = 32;
x_97 = lean_uint64_shift_right(x_95, x_96);
x_98 = lean_uint64_xor(x_95, x_97);
x_99 = 16;
x_100 = lean_uint64_shift_right(x_98, x_99);
x_101 = lean_uint64_xor(x_98, x_100);
x_102 = lean_uint64_to_usize(x_101);
x_103 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_104 = 1;
x_105 = lean_usize_sub(x_103, x_104);
x_106 = lean_usize_land(x_102, x_105);
x_107 = lean_array_uget(x_93, x_106);
lean_dec(x_93);
x_108 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_53, x_107);
lean_dec(x_107);
lean_dec(x_53);
if (lean_obj_tag(x_108) == 0)
{
lean_dec(x_54);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_58;
goto block_19;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
switch (lean_obj_tag(x_109)) {
case 0:
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_109);
lean_dec(x_54);
x_110 = l_Lean_IR_ToIR_lowerCode___closed__2;
x_111 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_110, x_2, x_3, x_4, x_58);
return x_111;
}
case 1:
{
lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_array_size(x_54);
x_114 = 0;
x_115 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_113, x_114, x_54, x_2, x_3, x_4, x_58);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_116);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_112);
x_121 = lean_ctor_get(x_115, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_123 = x_115;
} else {
 lean_dec_ref(x_115);
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
}
default: 
{
lean_dec(x_54);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_58;
goto block_19;
}
}
}
}
}
case 4:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
lean_dec(x_1);
x_126 = lean_st_ref_get(x_2, x_5);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = !lean_is_exclusive(x_125);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; size_t x_144; size_t x_145; size_t x_146; size_t x_147; size_t x_148; lean_object* x_149; lean_object* x_150; 
x_132 = lean_ctor_get(x_125, 0);
x_133 = lean_ctor_get(x_125, 1);
x_134 = lean_ctor_get(x_125, 2);
x_135 = lean_ctor_get(x_125, 3);
x_136 = lean_array_get_size(x_130);
x_137 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_134);
x_138 = 32;
x_139 = lean_uint64_shift_right(x_137, x_138);
x_140 = lean_uint64_xor(x_137, x_139);
x_141 = 16;
x_142 = lean_uint64_shift_right(x_140, x_141);
x_143 = lean_uint64_xor(x_140, x_142);
x_144 = lean_uint64_to_usize(x_143);
x_145 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_146 = 1;
x_147 = lean_usize_sub(x_145, x_146);
x_148 = lean_usize_land(x_144, x_147);
x_149 = lean_array_uget(x_130, x_148);
lean_dec(x_130);
x_150 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_134, x_149);
lean_dec(x_149);
lean_dec(x_134);
if (lean_obj_tag(x_150) == 0)
{
lean_free_object(x_125);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_129;
goto block_12;
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec(x_150);
switch (lean_obj_tag(x_151)) {
case 0:
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_153 = l_Lean_IR_ToIR_lowerType(x_133, x_2, x_3, x_4, x_129);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_152);
x_156 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerAlt), 6, 1);
lean_closure_set(x_156, 0, x_152);
x_157 = lean_array_size(x_135);
x_158 = 0;
x_159 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_156, x_157, x_158, x_135, x_2, x_3, x_4, x_155);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_159, 0);
lean_ctor_set_tag(x_125, 10);
lean_ctor_set(x_125, 3, x_161);
lean_ctor_set(x_125, 2, x_154);
lean_ctor_set(x_125, 1, x_152);
lean_ctor_set(x_159, 0, x_125);
return x_159;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_159, 0);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_159);
lean_ctor_set_tag(x_125, 10);
lean_ctor_set(x_125, 3, x_162);
lean_ctor_set(x_125, 2, x_154);
lean_ctor_set(x_125, 1, x_152);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_125);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_154);
lean_dec(x_152);
lean_free_object(x_125);
lean_dec(x_132);
x_165 = !lean_is_exclusive(x_159);
if (x_165 == 0)
{
return x_159;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_159, 0);
x_167 = lean_ctor_get(x_159, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_159);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_152);
lean_free_object(x_125);
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = !lean_is_exclusive(x_153);
if (x_169 == 0)
{
return x_153;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_153, 0);
x_171 = lean_ctor_get(x_153, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_153);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
case 1:
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_151);
lean_free_object(x_125);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
x_173 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_174 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_173, x_2, x_3, x_4, x_129);
return x_174;
}
default: 
{
lean_free_object(x_125);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_129;
goto block_12;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; size_t x_187; size_t x_188; size_t x_189; size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
x_175 = lean_ctor_get(x_125, 0);
x_176 = lean_ctor_get(x_125, 1);
x_177 = lean_ctor_get(x_125, 2);
x_178 = lean_ctor_get(x_125, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_125);
x_179 = lean_array_get_size(x_130);
x_180 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_177);
x_181 = 32;
x_182 = lean_uint64_shift_right(x_180, x_181);
x_183 = lean_uint64_xor(x_180, x_182);
x_184 = 16;
x_185 = lean_uint64_shift_right(x_183, x_184);
x_186 = lean_uint64_xor(x_183, x_185);
x_187 = lean_uint64_to_usize(x_186);
x_188 = lean_usize_of_nat(x_179);
lean_dec(x_179);
x_189 = 1;
x_190 = lean_usize_sub(x_188, x_189);
x_191 = lean_usize_land(x_187, x_190);
x_192 = lean_array_uget(x_130, x_191);
lean_dec(x_130);
x_193 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_177, x_192);
lean_dec(x_192);
lean_dec(x_177);
if (lean_obj_tag(x_193) == 0)
{
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_129;
goto block_12;
}
else
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
switch (lean_obj_tag(x_194)) {
case 0:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_196 = l_Lean_IR_ToIR_lowerType(x_176, x_2, x_3, x_4, x_129);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; size_t x_201; lean_object* x_202; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
lean_inc(x_195);
x_199 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerAlt), 6, 1);
lean_closure_set(x_199, 0, x_195);
x_200 = lean_array_size(x_178);
x_201 = 0;
x_202 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_199, x_200, x_201, x_178, x_2, x_3, x_4, x_198);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_206, 0, x_175);
lean_ctor_set(x_206, 1, x_195);
lean_ctor_set(x_206, 2, x_197);
lean_ctor_set(x_206, 3, x_203);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_175);
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_202, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_210 = x_202;
} else {
 lean_dec_ref(x_202);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_195);
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_212 = lean_ctor_get(x_196, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_196, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_214 = x_196;
} else {
 lean_dec_ref(x_196);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
case 1:
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_194);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
x_216 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_217 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_216, x_2, x_3, x_4, x_129);
return x_217;
}
default: 
{
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_129;
goto block_12;
}
}
}
}
}
case 5:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; size_t x_238; size_t x_239; size_t x_240; size_t x_241; size_t x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_4);
lean_dec(x_3);
x_218 = lean_ctor_get(x_1, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_219 = x_1;
} else {
 lean_dec_ref(x_1);
 x_219 = lean_box(0);
}
x_220 = lean_st_ref_get(x_2, x_5);
lean_dec(x_2);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_228 = lean_ctor_get(x_221, 0);
lean_inc(x_228);
lean_dec(x_221);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_array_get_size(x_229);
x_231 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_218);
x_232 = 32;
x_233 = lean_uint64_shift_right(x_231, x_232);
x_234 = lean_uint64_xor(x_231, x_233);
x_235 = 16;
x_236 = lean_uint64_shift_right(x_234, x_235);
x_237 = lean_uint64_xor(x_234, x_236);
x_238 = lean_uint64_to_usize(x_237);
x_239 = lean_usize_of_nat(x_230);
lean_dec(x_230);
x_240 = 1;
x_241 = lean_usize_sub(x_239, x_240);
x_242 = lean_usize_land(x_238, x_241);
x_243 = lean_array_uget(x_229, x_242);
lean_dec(x_229);
x_244 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_218, x_243);
lean_dec(x_243);
lean_dec(x_218);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_246 = l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(x_245);
x_224 = x_246;
goto block_227;
}
else
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
lean_dec(x_244);
switch (lean_obj_tag(x_247)) {
case 0:
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
x_224 = x_247;
goto block_227;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_247, 0);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_224 = x_250;
goto block_227;
}
}
case 1:
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_247);
x_251 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_252 = l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(x_251);
x_224 = x_252;
goto block_227;
}
default: 
{
lean_object* x_253; 
x_253 = lean_box(1);
x_224 = x_253;
goto block_227;
}
}
}
block_227:
{
lean_object* x_225; lean_object* x_226; 
if (lean_is_scalar(x_219)) {
 x_225 = lean_alloc_ctor(11, 1, 0);
} else {
 x_225 = x_219;
 lean_ctor_set_tag(x_225, 11);
}
lean_ctor_set(x_225, 0, x_224);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_222);
return x_226;
}
}
default: 
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_box(13);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_5);
return x_255;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_11 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_10, x_6, x_7, x_8, x_9);
return x_11;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_IR_ToIR_lowerCode___closed__2;
x_18 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_17, x_13, x_14, x_15, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_IR_ToIR_getCtorInfo(x_7, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_14, x_8, x_15, x_16, x_3, x_4, x_5, x_12);
lean_dec(x_15);
lean_dec(x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_17, 0, x_11);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_11);
lean_dec(x_14);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_27, x_8, x_28, x_29, x_3, x_4, x_5, x_12);
lean_dec(x_28);
lean_dec(x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = l_Lean_IR_ToIR_lowerCode(x_45, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_2, 0, x_48);
lean_ctor_set(x_46, 0, x_2);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_2, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_free_object(x_2);
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
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
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
lean_dec(x_2);
x_57 = l_Lean_IR_ToIR_lowerCode(x_56, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_20; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_20 = lean_nat_dec_lt(x_7, x_10);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = lean_array_get(x_22, x_1, x_7);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_8, x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_29);
x_31 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_24);
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
x_44 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_24, x_43);
lean_dec(x_43);
lean_dec(x_24);
if (lean_obj_tag(x_44) == 0)
{
x_12 = x_6;
x_13 = x_28;
goto block_16;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
lean_inc(x_2);
x_51 = lean_array_get(x_2, x_3, x_7);
if (lean_obj_tag(x_51) == 1)
{
lean_dec(x_51);
goto block_50;
}
else
{
lean_dec(x_51);
if (x_4 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
x_12 = x_6;
x_13 = x_28;
goto block_16;
}
else
{
goto block_50;
}
}
block_50:
{
lean_object* x_48; lean_object* x_49; 
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_array_push(x_6, x_48);
x_12 = x_49;
x_13 = x_28;
goto block_16;
}
}
else
{
lean_dec(x_45);
x_12 = x_6;
x_13 = x_28;
goto block_16;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_23);
lean_inc(x_2);
x_52 = lean_array_get(x_2, x_3, x_7);
if (lean_obj_tag(x_52) == 1)
{
lean_dec(x_52);
goto block_19;
}
else
{
lean_dec(x_52);
if (x_4 == 0)
{
x_12 = x_6;
x_13 = x_9;
goto block_16;
}
else
{
goto block_19;
}
}
}
}
block_16:
{
lean_object* x_14; 
x_14 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_6 = x_12;
x_7 = x_14;
x_9 = x_13;
goto _start;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(1);
x_18 = lean_array_push(x_6, x_17);
x_12 = x_18;
x_13 = x_9;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_13);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("projection of non-inductive type", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(257u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(271u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_unsigned_to_nat(366u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Quot", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcInv", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("axiom '", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("thm unsupported by code generator", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__15;
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_unsigned_to_nat(365u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__17;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quot ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__21;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("induct unsupported by code generator", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__23;
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_unsigned_to_nat(364u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: args.isEmpty\n          ", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(292u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__28;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__30;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__34;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__32;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__37;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(373u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
x_37 = lean_box(0);
switch (lean_obj_tag(x_36)) {
case 0:
{
uint8_t x_38; 
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = l_Lean_IR_ToIR_lowerLitValue(x_39);
lean_ctor_set_tag(x_36, 11);
lean_ctor_set(x_36, 0, x_40);
x_41 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_36, x_3, x_4, x_5, x_6);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l_Lean_IR_ToIR_lowerLitValue(x_42);
x_44 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_44, x_3, x_4, x_5, x_6);
return x_45;
}
}
case 1:
{
lean_object* x_46; 
lean_dec(x_35);
x_46 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_46;
}
case 2:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_48 = lean_ctor_get(x_1, 3);
lean_dec(x_48);
x_49 = lean_ctor_get(x_1, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_36, 2);
lean_inc(x_54);
lean_dec(x_36);
x_55 = lean_st_ref_get(x_3, x_6);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_array_get_size(x_59);
x_61 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_54);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_59, x_72);
lean_dec(x_59);
x_74 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_54, x_73);
lean_dec(x_73);
lean_dec(x_54);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_1);
lean_dec(x_35);
lean_dec(x_2);
x_75 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_76 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_75, x_3, x_4, x_5, x_58);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec(x_74);
switch (lean_obj_tag(x_77)) {
case 0:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_get(x_5, x_58);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
x_84 = lean_unbox(x_83);
x_85 = l_Lean_Environment_find_x3f(x_82, x_52, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_78);
lean_dec(x_53);
lean_free_object(x_1);
lean_dec(x_35);
lean_dec(x_2);
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_81;
goto block_34;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 5)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_87, 4);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l_List_get_x21Internal___redArg(x_89, x_88, x_90);
lean_dec(x_88);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_92 = l_Lean_IR_ToIR_getCtorInfo(x_91, x_3, x_4, x_5, x_81);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_array_get(x_37, x_96, x_53);
lean_dec(x_53);
lean_dec(x_96);
x_98 = l_Lean_IR_ToIR_lowerProj(x_78, x_95, x_97);
lean_dec(x_95);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_3, x_94);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_ctor_set(x_1, 3, x_107);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set(x_105, 0, x_1);
return x_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_105);
lean_ctor_set(x_1, 3, x_108);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_103);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_free_object(x_1);
return x_105;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_98);
lean_free_object(x_1);
x_111 = l_Lean_IR_ToIR_bindErased___redArg(x_35, x_3, x_94);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_112);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_78);
lean_dec(x_53);
lean_free_object(x_1);
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_92);
if (x_114 == 0)
{
return x_92;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_92, 0);
x_116 = lean_ctor_get(x_92, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_92);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_dec(x_86);
lean_dec(x_78);
lean_dec(x_53);
lean_free_object(x_1);
lean_dec(x_35);
lean_dec(x_2);
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_81;
goto block_34;
}
}
}
case 1:
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_77);
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_1);
lean_dec(x_35);
lean_dec(x_2);
x_118 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_119 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_118, x_3, x_4, x_5, x_58);
return x_119;
}
default: 
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_1);
x_120 = l_Lean_IR_ToIR_bindErased___redArg(x_35, x_3, x_58);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; size_t x_139; size_t x_140; size_t x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_1);
x_123 = lean_ctor_get(x_36, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_36, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_36, 2);
lean_inc(x_125);
lean_dec(x_36);
x_126 = lean_st_ref_get(x_3, x_6);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_array_get_size(x_130);
x_132 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_125);
x_133 = 32;
x_134 = lean_uint64_shift_right(x_132, x_133);
x_135 = lean_uint64_xor(x_132, x_134);
x_136 = 16;
x_137 = lean_uint64_shift_right(x_135, x_136);
x_138 = lean_uint64_xor(x_135, x_137);
x_139 = lean_uint64_to_usize(x_138);
x_140 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_141 = 1;
x_142 = lean_usize_sub(x_140, x_141);
x_143 = lean_usize_land(x_139, x_142);
x_144 = lean_array_uget(x_130, x_143);
lean_dec(x_130);
x_145 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_125, x_144);
lean_dec(x_144);
lean_dec(x_125);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_35);
lean_dec(x_2);
x_146 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_147 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_146, x_3, x_4, x_5, x_129);
return x_147;
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
lean_dec(x_145);
switch (lean_obj_tag(x_148)) {
case 0:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_st_ref_get(x_5, x_129);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_box(0);
x_155 = lean_unbox(x_154);
x_156 = l_Lean_Environment_find_x3f(x_153, x_123, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_dec(x_149);
lean_dec(x_124);
lean_dec(x_35);
lean_dec(x_2);
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_152;
goto block_34;
}
else
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec(x_156);
if (lean_obj_tag(x_157) == 5)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_ctor_get(x_158, 4);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_box(0);
x_161 = lean_unsigned_to_nat(0u);
x_162 = l_List_get_x21Internal___redArg(x_160, x_159, x_161);
lean_dec(x_159);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_163 = l_Lean_IR_ToIR_getCtorInfo(x_162, x_3, x_4, x_5, x_152);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = lean_array_get(x_37, x_167, x_124);
lean_dec(x_124);
lean_dec(x_167);
x_169 = l_Lean_IR_ToIR_lowerProj(x_149, x_166, x_168);
lean_dec(x_166);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_3, x_165);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_172);
lean_ctor_set(x_180, 3, x_177);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_171);
return x_176;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_169);
x_182 = l_Lean_IR_ToIR_bindErased___redArg(x_35, x_3, x_165);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_183);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_149);
lean_dec(x_124);
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = lean_ctor_get(x_163, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_163, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_187 = x_163;
} else {
 lean_dec_ref(x_163);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_dec(x_157);
lean_dec(x_149);
lean_dec(x_124);
lean_dec(x_35);
lean_dec(x_2);
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_152;
goto block_34;
}
}
}
case 1:
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_148);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_35);
lean_dec(x_2);
x_189 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_190 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_189, x_3, x_4, x_5, x_129);
return x_190;
}
default: 
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_124);
lean_dec(x_123);
x_191 = l_Lean_IR_ToIR_bindErased___redArg(x_35, x_3, x_129);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_192);
return x_193;
}
}
}
}
}
case 3:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = lean_ctor_get(x_36, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_36, 2);
lean_inc(x_195);
lean_dec(x_36);
x_196 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_197 = l_Lean_IR_instInhabitedArg;
if (lean_obj_tag(x_194) == 1)
{
lean_object* x_847; 
x_847 = lean_ctor_get(x_194, 0);
lean_inc(x_847);
if (lean_obj_tag(x_847) == 1)
{
lean_object* x_848; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; uint8_t x_852; 
x_849 = lean_ctor_get(x_194, 1);
lean_inc(x_849);
x_850 = lean_ctor_get(x_847, 1);
lean_inc(x_850);
lean_dec(x_847);
x_851 = l_Lean_IR_ToIR_lowerLet___closed__32;
x_852 = lean_string_dec_eq(x_850, x_851);
lean_dec(x_850);
if (x_852 == 0)
{
lean_dec(x_849);
x_198 = x_194;
x_199 = x_3;
x_200 = x_4;
x_201 = x_5;
x_202 = x_6;
goto block_846;
}
else
{
lean_object* x_853; uint8_t x_854; 
lean_dec(x_194);
x_853 = l_Lean_IR_ToIR_lowerLet___closed__33;
x_854 = lean_string_dec_eq(x_849, x_853);
if (x_854 == 0)
{
lean_object* x_855; lean_object* x_856; 
x_855 = l_Lean_Name_str___override(x_848, x_851);
x_856 = l_Lean_Name_str___override(x_855, x_849);
x_198 = x_856;
x_199 = x_3;
x_200 = x_4;
x_201 = x_5;
x_202 = x_6;
goto block_846;
}
else
{
uint8_t x_857; 
lean_dec(x_849);
lean_dec(x_196);
x_857 = !lean_is_exclusive(x_1);
if (x_857 == 0)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; size_t x_862; size_t x_863; lean_object* x_864; 
x_858 = lean_ctor_get(x_1, 3);
lean_dec(x_858);
x_859 = lean_ctor_get(x_1, 2);
lean_dec(x_859);
x_860 = lean_ctor_get(x_1, 1);
lean_dec(x_860);
x_861 = lean_ctor_get(x_1, 0);
lean_dec(x_861);
x_862 = lean_array_size(x_195);
x_863 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_864 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_862, x_863, x_195, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; uint8_t x_871; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_3, x_866);
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
x_870 = l_Lean_IR_ToIR_newVar___redArg(x_3, x_869);
x_871 = !lean_is_exclusive(x_870);
if (x_871 == 0)
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_870, 0);
x_873 = lean_ctor_get(x_870, 1);
x_874 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_873);
if (lean_obj_tag(x_874) == 0)
{
uint8_t x_875; 
x_875 = !lean_is_exclusive(x_874);
if (x_875 == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_876 = lean_ctor_get(x_874, 0);
x_877 = lean_box(7);
x_878 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_879 = lean_unsigned_to_nat(0u);
x_880 = lean_array_get(x_197, x_865, x_879);
lean_dec(x_865);
lean_inc(x_872);
x_881 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_881, 0, x_872);
x_882 = l_Lean_IR_ToIR_lowerLet___closed__36;
x_883 = lean_array_push(x_882, x_880);
x_884 = lean_array_push(x_883, x_881);
lean_ctor_set_tag(x_870, 6);
lean_ctor_set(x_870, 1, x_884);
lean_ctor_set(x_870, 0, x_878);
lean_ctor_set(x_1, 3, x_876);
lean_ctor_set(x_1, 2, x_870);
lean_ctor_set(x_1, 1, x_877);
lean_ctor_set(x_1, 0, x_868);
x_885 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_886 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_886, 0, x_872);
lean_ctor_set(x_886, 1, x_877);
lean_ctor_set(x_886, 2, x_885);
lean_ctor_set(x_886, 3, x_1);
lean_ctor_set(x_874, 0, x_886);
return x_874;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_887 = lean_ctor_get(x_874, 0);
x_888 = lean_ctor_get(x_874, 1);
lean_inc(x_888);
lean_inc(x_887);
lean_dec(x_874);
x_889 = lean_box(7);
x_890 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_891 = lean_unsigned_to_nat(0u);
x_892 = lean_array_get(x_197, x_865, x_891);
lean_dec(x_865);
lean_inc(x_872);
x_893 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_893, 0, x_872);
x_894 = l_Lean_IR_ToIR_lowerLet___closed__36;
x_895 = lean_array_push(x_894, x_892);
x_896 = lean_array_push(x_895, x_893);
lean_ctor_set_tag(x_870, 6);
lean_ctor_set(x_870, 1, x_896);
lean_ctor_set(x_870, 0, x_890);
lean_ctor_set(x_1, 3, x_887);
lean_ctor_set(x_1, 2, x_870);
lean_ctor_set(x_1, 1, x_889);
lean_ctor_set(x_1, 0, x_868);
x_897 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_898 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_898, 0, x_872);
lean_ctor_set(x_898, 1, x_889);
lean_ctor_set(x_898, 2, x_897);
lean_ctor_set(x_898, 3, x_1);
x_899 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_888);
return x_899;
}
}
else
{
lean_free_object(x_870);
lean_dec(x_872);
lean_dec(x_868);
lean_dec(x_865);
lean_free_object(x_1);
return x_874;
}
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_900 = lean_ctor_get(x_870, 0);
x_901 = lean_ctor_get(x_870, 1);
lean_inc(x_901);
lean_inc(x_900);
lean_dec(x_870);
x_902 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_901);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_905 = x_902;
} else {
 lean_dec_ref(x_902);
 x_905 = lean_box(0);
}
x_906 = lean_box(7);
x_907 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_908 = lean_unsigned_to_nat(0u);
x_909 = lean_array_get(x_197, x_865, x_908);
lean_dec(x_865);
lean_inc(x_900);
x_910 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_910, 0, x_900);
x_911 = l_Lean_IR_ToIR_lowerLet___closed__36;
x_912 = lean_array_push(x_911, x_909);
x_913 = lean_array_push(x_912, x_910);
x_914 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_914, 0, x_907);
lean_ctor_set(x_914, 1, x_913);
lean_ctor_set(x_1, 3, x_903);
lean_ctor_set(x_1, 2, x_914);
lean_ctor_set(x_1, 1, x_906);
lean_ctor_set(x_1, 0, x_868);
x_915 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_916 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_916, 0, x_900);
lean_ctor_set(x_916, 1, x_906);
lean_ctor_set(x_916, 2, x_915);
lean_ctor_set(x_916, 3, x_1);
if (lean_is_scalar(x_905)) {
 x_917 = lean_alloc_ctor(0, 2, 0);
} else {
 x_917 = x_905;
}
lean_ctor_set(x_917, 0, x_916);
lean_ctor_set(x_917, 1, x_904);
return x_917;
}
else
{
lean_dec(x_900);
lean_dec(x_868);
lean_dec(x_865);
lean_free_object(x_1);
return x_902;
}
}
}
else
{
uint8_t x_918; 
lean_free_object(x_1);
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_918 = !lean_is_exclusive(x_864);
if (x_918 == 0)
{
return x_864;
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_864, 0);
x_920 = lean_ctor_get(x_864, 1);
lean_inc(x_920);
lean_inc(x_919);
lean_dec(x_864);
x_921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
return x_921;
}
}
}
else
{
size_t x_922; size_t x_923; lean_object* x_924; 
lean_dec(x_1);
x_922 = lean_array_size(x_195);
x_923 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_924 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_922, x_923, x_195, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_924) == 0)
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
lean_dec(x_924);
x_927 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_3, x_926);
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_930 = l_Lean_IR_ToIR_newVar___redArg(x_3, x_929);
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_933 = x_930;
} else {
 lean_dec_ref(x_930);
 x_933 = lean_box(0);
}
x_934 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_932);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_934, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_937 = x_934;
} else {
 lean_dec_ref(x_934);
 x_937 = lean_box(0);
}
x_938 = lean_box(7);
x_939 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_940 = lean_unsigned_to_nat(0u);
x_941 = lean_array_get(x_197, x_925, x_940);
lean_dec(x_925);
lean_inc(x_931);
x_942 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_942, 0, x_931);
x_943 = l_Lean_IR_ToIR_lowerLet___closed__36;
x_944 = lean_array_push(x_943, x_941);
x_945 = lean_array_push(x_944, x_942);
if (lean_is_scalar(x_933)) {
 x_946 = lean_alloc_ctor(6, 2, 0);
} else {
 x_946 = x_933;
 lean_ctor_set_tag(x_946, 6);
}
lean_ctor_set(x_946, 0, x_939);
lean_ctor_set(x_946, 1, x_945);
x_947 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_947, 0, x_928);
lean_ctor_set(x_947, 1, x_938);
lean_ctor_set(x_947, 2, x_946);
lean_ctor_set(x_947, 3, x_935);
x_948 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_949 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_949, 0, x_931);
lean_ctor_set(x_949, 1, x_938);
lean_ctor_set(x_949, 2, x_948);
lean_ctor_set(x_949, 3, x_947);
if (lean_is_scalar(x_937)) {
 x_950 = lean_alloc_ctor(0, 2, 0);
} else {
 x_950 = x_937;
}
lean_ctor_set(x_950, 0, x_949);
lean_ctor_set(x_950, 1, x_936);
return x_950;
}
else
{
lean_dec(x_933);
lean_dec(x_931);
lean_dec(x_928);
lean_dec(x_925);
return x_934;
}
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_951 = lean_ctor_get(x_924, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_924, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_953 = x_924;
} else {
 lean_dec_ref(x_924);
 x_953 = lean_box(0);
}
if (lean_is_scalar(x_953)) {
 x_954 = lean_alloc_ctor(1, 2, 0);
} else {
 x_954 = x_953;
}
lean_ctor_set(x_954, 0, x_951);
lean_ctor_set(x_954, 1, x_952);
return x_954;
}
}
}
}
}
else
{
lean_dec(x_848);
lean_dec(x_847);
x_198 = x_194;
x_199 = x_3;
x_200 = x_4;
x_201 = x_5;
x_202 = x_6;
goto block_846;
}
}
else
{
lean_dec(x_847);
x_198 = x_194;
x_199 = x_3;
x_200 = x_4;
x_201 = x_5;
x_202 = x_6;
goto block_846;
}
}
else
{
x_198 = x_194;
x_199 = x_3;
x_200 = x_4;
x_201 = x_5;
x_202 = x_6;
goto block_846;
}
block_846:
{
size_t x_203; size_t x_204; lean_object* x_205; 
x_203 = lean_array_size(x_195);
x_204 = 0;
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_195);
x_205 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_203, x_204, x_195, x_199, x_200, x_201, x_202);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_206);
lean_inc(x_198);
lean_inc(x_2);
lean_inc(x_1);
x_208 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_198, x_206, x_199, x_200, x_201, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_st_ref_get(x_201, x_210);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_box(0);
x_217 = lean_unbox(x_216);
lean_inc(x_198);
lean_inc(x_215);
x_218 = l_Lean_Environment_find_x3f(x_215, x_198, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_215);
lean_free_object(x_211);
lean_dec(x_206);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_219 = l_Lean_IR_ToIR_lowerLet___closed__5;
x_220 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_219, x_199, x_200, x_201, x_214);
return x_220;
}
else
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_218, 0);
lean_inc(x_221);
lean_dec(x_218);
switch (lean_obj_tag(x_221)) {
case 0:
{
uint8_t x_222; 
lean_dec(x_215);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_221, 0);
lean_dec(x_223);
x_224 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_225 = lean_name_eq(x_198, x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_227 = lean_name_eq(x_198, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
lean_free_object(x_211);
lean_inc(x_198);
x_228 = l_Lean_IR_ToIR_findDecl___redArg(x_198, x_201, x_214);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_231 = lean_ctor_get(x_228, 1);
x_232 = lean_ctor_get(x_228, 0);
lean_dec(x_232);
x_233 = lean_box(x_227);
x_234 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 2, 1);
lean_closure_set(x_234, 0, x_233);
x_235 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_236 = lean_box(1);
x_237 = lean_unbox(x_236);
x_238 = l_Lean_Name_toString(x_198, x_237, x_234);
lean_ctor_set_tag(x_221, 3);
lean_ctor_set(x_221, 0, x_238);
lean_ctor_set_tag(x_228, 5);
lean_ctor_set(x_228, 1, x_221);
lean_ctor_set(x_228, 0, x_235);
x_239 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_240 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_240, 0, x_228);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_MessageData_ofFormat(x_240);
x_242 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_241, x_200, x_201, x_231);
lean_dec(x_201);
lean_dec(x_200);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_243 = lean_ctor_get(x_228, 1);
lean_inc(x_243);
lean_dec(x_228);
x_244 = lean_box(x_227);
x_245 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 2, 1);
lean_closure_set(x_245, 0, x_244);
x_246 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_247 = lean_box(1);
x_248 = lean_unbox(x_247);
x_249 = l_Lean_Name_toString(x_198, x_248, x_245);
lean_ctor_set_tag(x_221, 3);
lean_ctor_set(x_221, 0, x_249);
x_250 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_250, 0, x_246);
lean_ctor_set(x_250, 1, x_221);
x_251 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_252 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_MessageData_ofFormat(x_252);
x_254 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_253, x_200, x_201, x_243);
lean_dec(x_201);
lean_dec(x_200);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_free_object(x_221);
x_255 = lean_ctor_get(x_228, 1);
lean_inc(x_255);
lean_dec(x_228);
x_256 = lean_ctor_get(x_229, 0);
lean_inc(x_256);
lean_dec(x_229);
x_257 = lean_array_get_size(x_206);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_7 = x_200;
x_8 = x_198;
x_9 = x_255;
x_10 = x_199;
x_11 = x_257;
x_12 = x_206;
x_13 = x_201;
x_14 = x_258;
goto block_27;
}
}
else
{
lean_object* x_259; 
lean_free_object(x_221);
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_box(13);
lean_ctor_set(x_211, 0, x_259);
return x_211;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_free_object(x_221);
lean_free_object(x_211);
lean_dec(x_198);
x_260 = lean_unsigned_to_nat(2u);
x_261 = lean_array_get(x_197, x_206, x_260);
lean_dec(x_206);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec(x_261);
x_263 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_262, x_199, x_200, x_201, x_214);
return x_263;
}
else
{
lean_object* x_264; 
x_264 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_199, x_200, x_201, x_214);
return x_264;
}
}
}
else
{
lean_object* x_265; uint8_t x_266; 
lean_dec(x_221);
x_265 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_266 = lean_name_eq(x_198, x_265);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_268 = lean_name_eq(x_198, x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_free_object(x_211);
lean_inc(x_198);
x_269 = l_Lean_IR_ToIR_findDecl___redArg(x_198, x_201, x_214);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_272 = x_269;
} else {
 lean_dec_ref(x_269);
 x_272 = lean_box(0);
}
x_273 = lean_box(x_268);
x_274 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 2, 1);
lean_closure_set(x_274, 0, x_273);
x_275 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_276 = lean_box(1);
x_277 = lean_unbox(x_276);
x_278 = l_Lean_Name_toString(x_198, x_277, x_274);
x_279 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_279, 0, x_278);
if (lean_is_scalar(x_272)) {
 x_280 = lean_alloc_ctor(5, 2, 0);
} else {
 x_280 = x_272;
 lean_ctor_set_tag(x_280, 5);
}
lean_ctor_set(x_280, 0, x_275);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_282 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_MessageData_ofFormat(x_282);
x_284 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_283, x_200, x_201, x_271);
lean_dec(x_201);
lean_dec(x_200);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_269, 1);
lean_inc(x_285);
lean_dec(x_269);
x_286 = lean_ctor_get(x_270, 0);
lean_inc(x_286);
lean_dec(x_270);
x_287 = lean_array_get_size(x_206);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_7 = x_200;
x_8 = x_198;
x_9 = x_285;
x_10 = x_199;
x_11 = x_287;
x_12 = x_206;
x_13 = x_201;
x_14 = x_288;
goto block_27;
}
}
else
{
lean_object* x_289; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_289 = lean_box(13);
lean_ctor_set(x_211, 0, x_289);
return x_211;
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_free_object(x_211);
lean_dec(x_198);
x_290 = lean_unsigned_to_nat(2u);
x_291 = lean_array_get(x_197, x_206, x_290);
lean_dec(x_206);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec(x_291);
x_293 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_292, x_199, x_200, x_201, x_214);
return x_293;
}
else
{
lean_object* x_294; 
x_294 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_199, x_200, x_201, x_214);
return x_294;
}
}
}
}
case 2:
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_221);
lean_dec(x_215);
lean_free_object(x_211);
lean_dec(x_206);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_295 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_296 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_295, x_199, x_200, x_201, x_214);
return x_296;
}
case 4:
{
uint8_t x_297; 
lean_dec(x_215);
lean_free_object(x_211);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
x_297 = !lean_is_exclusive(x_221);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = lean_ctor_get(x_221, 0);
lean_dec(x_298);
x_299 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_300 = lean_name_eq(x_198, x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_301 = lean_box(x_300);
x_302 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 2, 1);
lean_closure_set(x_302, 0, x_301);
x_303 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_304 = lean_box(1);
x_305 = lean_unbox(x_304);
x_306 = l_Lean_Name_toString(x_198, x_305, x_302);
lean_ctor_set_tag(x_221, 3);
lean_ctor_set(x_221, 0, x_306);
x_307 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_221);
x_308 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_309 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = l_Lean_MessageData_ofFormat(x_309);
x_311 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_310, x_200, x_201, x_214);
lean_dec(x_201);
lean_dec(x_200);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; 
lean_free_object(x_221);
lean_dec(x_198);
x_312 = lean_unsigned_to_nat(2u);
x_313 = lean_array_get(x_197, x_206, x_312);
lean_dec(x_206);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec(x_313);
x_315 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_314, x_199, x_200, x_201, x_214);
return x_315;
}
else
{
lean_object* x_316; 
x_316 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_199, x_200, x_201, x_214);
return x_316;
}
}
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_221);
x_317 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_318 = lean_name_eq(x_198, x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_319 = lean_box(x_318);
x_320 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 2, 1);
lean_closure_set(x_320, 0, x_319);
x_321 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_322 = lean_box(1);
x_323 = lean_unbox(x_322);
x_324 = l_Lean_Name_toString(x_198, x_323, x_320);
x_325 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_326, 0, x_321);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_328 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_MessageData_ofFormat(x_328);
x_330 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_329, x_200, x_201, x_214);
lean_dec(x_201);
lean_dec(x_200);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_198);
x_331 = lean_unsigned_to_nat(2u);
x_332 = lean_array_get(x_197, x_206, x_331);
lean_dec(x_206);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec(x_332);
x_334 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_333, x_199, x_200, x_201, x_214);
return x_334;
}
else
{
lean_object* x_335; 
x_335 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_199, x_200, x_201, x_214);
return x_335;
}
}
}
}
case 5:
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_221);
lean_dec(x_215);
lean_free_object(x_211);
lean_dec(x_206);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_336 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_337 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_336, x_199, x_200, x_201, x_214);
return x_337;
}
case 6:
{
uint8_t x_338; 
lean_free_object(x_211);
lean_dec(x_196);
x_338 = !lean_is_exclusive(x_221);
if (x_338 == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_ctor_get(x_221, 0);
lean_inc(x_198);
x_340 = l_Lean_isExtern(x_215, x_198);
if (x_340 == 0)
{
uint8_t x_341; 
lean_dec(x_206);
x_341 = !lean_is_exclusive(x_1);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_342 = lean_ctor_get(x_1, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_1, 2);
lean_dec(x_343);
x_344 = lean_ctor_get(x_1, 1);
lean_dec(x_344);
x_345 = lean_ctor_get(x_1, 0);
lean_dec(x_345);
x_346 = lean_ctor_get(x_339, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_339, 2);
lean_inc(x_347);
x_348 = lean_ctor_get(x_339, 3);
lean_inc(x_348);
lean_dec(x_339);
x_349 = !lean_is_exclusive(x_346);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_346, 0);
x_351 = lean_ctor_get(x_346, 2);
lean_dec(x_351);
x_352 = lean_ctor_get(x_346, 1);
lean_dec(x_352);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_353 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_350, x_199, x_200, x_201, x_214);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_347);
lean_free_object(x_221);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_356 = l_Lean_IR_ToIR_getCtorInfo(x_198, x_199, x_200, x_201, x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = lean_ctor_get(x_357, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_361 = lean_array_get_size(x_195);
x_362 = l_Array_extract___redArg(x_195, x_348, x_361);
lean_dec(x_195);
x_363 = lean_unsigned_to_nat(0u);
x_364 = l_Lean_IR_ToIR_lowerLet___closed__25;
x_365 = lean_array_get_size(x_360);
x_366 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_346, 2, x_366);
lean_ctor_set(x_346, 1, x_365);
lean_ctor_set(x_346, 0, x_363);
x_367 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_362, x_37, x_360, x_340, x_346, x_364, x_363, x_199, x_358);
lean_dec(x_346);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_369);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_370, 0);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
x_374 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_359, x_360, x_362, x_372, x_199, x_200, x_201, x_373);
lean_dec(x_362);
lean_dec(x_360);
if (lean_obj_tag(x_374) == 0)
{
uint8_t x_375; 
x_375 = !lean_is_exclusive(x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_374, 0);
x_377 = lean_box(7);
lean_ctor_set(x_370, 1, x_368);
lean_ctor_set(x_370, 0, x_359);
lean_ctor_set(x_1, 3, x_376);
lean_ctor_set(x_1, 2, x_370);
lean_ctor_set(x_1, 1, x_377);
lean_ctor_set(x_1, 0, x_372);
lean_ctor_set(x_374, 0, x_1);
return x_374;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_378 = lean_ctor_get(x_374, 0);
x_379 = lean_ctor_get(x_374, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_374);
x_380 = lean_box(7);
lean_ctor_set(x_370, 1, x_368);
lean_ctor_set(x_370, 0, x_359);
lean_ctor_set(x_1, 3, x_378);
lean_ctor_set(x_1, 2, x_370);
lean_ctor_set(x_1, 1, x_380);
lean_ctor_set(x_1, 0, x_372);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_1);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
else
{
lean_free_object(x_370);
lean_dec(x_372);
lean_dec(x_368);
lean_dec(x_359);
lean_free_object(x_1);
return x_374;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_370, 0);
x_383 = lean_ctor_get(x_370, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_370);
lean_inc(x_382);
x_384 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_359, x_360, x_362, x_382, x_199, x_200, x_201, x_383);
lean_dec(x_362);
lean_dec(x_360);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_387 = x_384;
} else {
 lean_dec_ref(x_384);
 x_387 = lean_box(0);
}
x_388 = lean_box(7);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_359);
lean_ctor_set(x_389, 1, x_368);
lean_ctor_set(x_1, 3, x_385);
lean_ctor_set(x_1, 2, x_389);
lean_ctor_set(x_1, 1, x_388);
lean_ctor_set(x_1, 0, x_382);
if (lean_is_scalar(x_387)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_387;
}
lean_ctor_set(x_390, 0, x_1);
lean_ctor_set(x_390, 1, x_386);
return x_390;
}
else
{
lean_dec(x_382);
lean_dec(x_368);
lean_dec(x_359);
lean_free_object(x_1);
return x_384;
}
}
}
else
{
uint8_t x_391; 
lean_free_object(x_346);
lean_dec(x_348);
lean_free_object(x_1);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_391 = !lean_is_exclusive(x_356);
if (x_391 == 0)
{
return x_356;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_356, 0);
x_393 = lean_ctor_get(x_356, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_356);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
else
{
lean_object* x_395; uint8_t x_396; 
lean_free_object(x_346);
lean_dec(x_348);
lean_dec(x_198);
x_395 = lean_ctor_get(x_353, 1);
lean_inc(x_395);
lean_dec(x_353);
x_396 = !lean_is_exclusive(x_354);
if (x_396 == 0)
{
lean_object* x_397; uint8_t x_398; 
x_397 = lean_ctor_get(x_354, 0);
x_398 = l_Array_isEmpty___redArg(x_195);
lean_dec(x_195);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
lean_free_object(x_354);
lean_dec(x_397);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
lean_dec(x_35);
lean_dec(x_2);
x_399 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_400 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_399, x_199, x_200, x_201, x_395);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_401 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_395);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = l_Lean_IR_ToIR_lowerCode(x_2, x_199, x_200, x_201, x_403);
if (lean_obj_tag(x_404) == 0)
{
uint8_t x_405; 
x_405 = !lean_is_exclusive(x_404);
if (x_405 == 0)
{
lean_object* x_406; 
x_406 = lean_ctor_get(x_404, 0);
lean_ctor_set_tag(x_354, 0);
lean_ctor_set(x_354, 0, x_347);
lean_ctor_set_tag(x_221, 11);
lean_ctor_set(x_221, 0, x_354);
lean_ctor_set(x_1, 3, x_406);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_397);
lean_ctor_set(x_1, 0, x_402);
lean_ctor_set(x_404, 0, x_1);
return x_404;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_404, 0);
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_404);
lean_ctor_set_tag(x_354, 0);
lean_ctor_set(x_354, 0, x_347);
lean_ctor_set_tag(x_221, 11);
lean_ctor_set(x_221, 0, x_354);
lean_ctor_set(x_1, 3, x_407);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_397);
lean_ctor_set(x_1, 0, x_402);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_1);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
else
{
lean_dec(x_402);
lean_free_object(x_354);
lean_dec(x_397);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
return x_404;
}
}
}
else
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_ctor_get(x_354, 0);
lean_inc(x_410);
lean_dec(x_354);
x_411 = l_Array_isEmpty___redArg(x_195);
lean_dec(x_195);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_410);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
lean_dec(x_35);
lean_dec(x_2);
x_412 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_413 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_412, x_199, x_200, x_201, x_395);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_395);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = l_Lean_IR_ToIR_lowerCode(x_2, x_199, x_200, x_201, x_416);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_420 = x_417;
} else {
 lean_dec_ref(x_417);
 x_420 = lean_box(0);
}
x_421 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set_tag(x_221, 11);
lean_ctor_set(x_221, 0, x_421);
lean_ctor_set(x_1, 3, x_418);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_410);
lean_ctor_set(x_1, 0, x_415);
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_1);
lean_ctor_set(x_422, 1, x_419);
return x_422;
}
else
{
lean_dec(x_415);
lean_dec(x_410);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
return x_417;
}
}
}
}
}
else
{
uint8_t x_423; 
lean_free_object(x_346);
lean_dec(x_348);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_423 = !lean_is_exclusive(x_353);
if (x_423 == 0)
{
return x_353;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_353, 0);
x_425 = lean_ctor_get(x_353, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_353);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
else
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_346, 0);
lean_inc(x_427);
lean_dec(x_346);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_428 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_427, x_199, x_200, x_201, x_214);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_347);
lean_free_object(x_221);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_431 = l_Lean_IR_ToIR_getCtorInfo(x_198, x_199, x_200, x_201, x_430);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
lean_dec(x_432);
x_436 = lean_array_get_size(x_195);
x_437 = l_Array_extract___redArg(x_195, x_348, x_436);
lean_dec(x_195);
x_438 = lean_unsigned_to_nat(0u);
x_439 = l_Lean_IR_ToIR_lowerLet___closed__25;
x_440 = lean_array_get_size(x_435);
x_441 = lean_unsigned_to_nat(1u);
x_442 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_442, 0, x_438);
lean_ctor_set(x_442, 1, x_440);
lean_ctor_set(x_442, 2, x_441);
x_443 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_437, x_37, x_435, x_340, x_442, x_439, x_438, x_199, x_433);
lean_dec(x_442);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_445);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_449 = x_446;
} else {
 lean_dec_ref(x_446);
 x_449 = lean_box(0);
}
lean_inc(x_447);
x_450 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_434, x_435, x_437, x_447, x_199, x_200, x_201, x_448);
lean_dec(x_437);
lean_dec(x_435);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_453 = x_450;
} else {
 lean_dec_ref(x_450);
 x_453 = lean_box(0);
}
x_454 = lean_box(7);
if (lean_is_scalar(x_449)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_449;
}
lean_ctor_set(x_455, 0, x_434);
lean_ctor_set(x_455, 1, x_444);
lean_ctor_set(x_1, 3, x_451);
lean_ctor_set(x_1, 2, x_455);
lean_ctor_set(x_1, 1, x_454);
lean_ctor_set(x_1, 0, x_447);
if (lean_is_scalar(x_453)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_453;
}
lean_ctor_set(x_456, 0, x_1);
lean_ctor_set(x_456, 1, x_452);
return x_456;
}
else
{
lean_dec(x_449);
lean_dec(x_447);
lean_dec(x_444);
lean_dec(x_434);
lean_free_object(x_1);
return x_450;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_348);
lean_free_object(x_1);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_457 = lean_ctor_get(x_431, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_431, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_459 = x_431;
} else {
 lean_dec_ref(x_431);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_457);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; 
lean_dec(x_348);
lean_dec(x_198);
x_461 = lean_ctor_get(x_428, 1);
lean_inc(x_461);
lean_dec(x_428);
x_462 = lean_ctor_get(x_429, 0);
lean_inc(x_462);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 x_463 = x_429;
} else {
 lean_dec_ref(x_429);
 x_463 = lean_box(0);
}
x_464 = l_Array_isEmpty___redArg(x_195);
lean_dec(x_195);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
lean_dec(x_35);
lean_dec(x_2);
x_465 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_466 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_465, x_199, x_200, x_201, x_461);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_461);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = l_Lean_IR_ToIR_lowerCode(x_2, x_199, x_200, x_201, x_469);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_474 = lean_alloc_ctor(0, 1, 0);
} else {
 x_474 = x_463;
 lean_ctor_set_tag(x_474, 0);
}
lean_ctor_set(x_474, 0, x_347);
lean_ctor_set_tag(x_221, 11);
lean_ctor_set(x_221, 0, x_474);
lean_ctor_set(x_1, 3, x_471);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_462);
lean_ctor_set(x_1, 0, x_468);
if (lean_is_scalar(x_473)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_473;
}
lean_ctor_set(x_475, 0, x_1);
lean_ctor_set(x_475, 1, x_472);
return x_475;
}
else
{
lean_dec(x_468);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
return x_470;
}
}
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_348);
lean_dec(x_347);
lean_free_object(x_1);
lean_free_object(x_221);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_476 = lean_ctor_get(x_428, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_428, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_478 = x_428;
} else {
 lean_dec_ref(x_428);
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
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_1);
x_480 = lean_ctor_get(x_339, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_339, 2);
lean_inc(x_481);
x_482 = lean_ctor_get(x_339, 3);
lean_inc(x_482);
lean_dec(x_339);
x_483 = lean_ctor_get(x_480, 0);
lean_inc(x_483);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 lean_ctor_release(x_480, 2);
 x_484 = x_480;
} else {
 lean_dec_ref(x_480);
 x_484 = lean_box(0);
}
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_485 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_483, x_199, x_200, x_201, x_214);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
lean_dec(x_481);
lean_free_object(x_221);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_488 = l_Lean_IR_ToIR_getCtorInfo(x_198, x_199, x_200, x_201, x_487);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_ctor_get(x_489, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_492);
lean_dec(x_489);
x_493 = lean_array_get_size(x_195);
x_494 = l_Array_extract___redArg(x_195, x_482, x_493);
lean_dec(x_195);
x_495 = lean_unsigned_to_nat(0u);
x_496 = l_Lean_IR_ToIR_lowerLet___closed__25;
x_497 = lean_array_get_size(x_492);
x_498 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_484)) {
 x_499 = lean_alloc_ctor(0, 3, 0);
} else {
 x_499 = x_484;
}
lean_ctor_set(x_499, 0, x_495);
lean_ctor_set(x_499, 1, x_497);
lean_ctor_set(x_499, 2, x_498);
x_500 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_494, x_37, x_492, x_340, x_499, x_496, x_495, x_199, x_490);
lean_dec(x_499);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_502);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_506 = x_503;
} else {
 lean_dec_ref(x_503);
 x_506 = lean_box(0);
}
lean_inc(x_504);
x_507 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_491, x_492, x_494, x_504, x_199, x_200, x_201, x_505);
lean_dec(x_494);
lean_dec(x_492);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_510 = x_507;
} else {
 lean_dec_ref(x_507);
 x_510 = lean_box(0);
}
x_511 = lean_box(7);
if (lean_is_scalar(x_506)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_506;
}
lean_ctor_set(x_512, 0, x_491);
lean_ctor_set(x_512, 1, x_501);
x_513 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_513, 0, x_504);
lean_ctor_set(x_513, 1, x_511);
lean_ctor_set(x_513, 2, x_512);
lean_ctor_set(x_513, 3, x_508);
if (lean_is_scalar(x_510)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_510;
}
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_509);
return x_514;
}
else
{
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_501);
lean_dec(x_491);
return x_507;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_484);
lean_dec(x_482);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_515 = lean_ctor_get(x_488, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_488, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_517 = x_488;
} else {
 lean_dec_ref(x_488);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
lean_dec(x_484);
lean_dec(x_482);
lean_dec(x_198);
x_519 = lean_ctor_get(x_485, 1);
lean_inc(x_519);
lean_dec(x_485);
x_520 = lean_ctor_get(x_486, 0);
lean_inc(x_520);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_521 = x_486;
} else {
 lean_dec_ref(x_486);
 x_521 = lean_box(0);
}
x_522 = l_Array_isEmpty___redArg(x_195);
lean_dec(x_195);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_481);
lean_free_object(x_221);
lean_dec(x_35);
lean_dec(x_2);
x_523 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_524 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_523, x_199, x_200, x_201, x_519);
return x_524;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_525 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_519);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = l_Lean_IR_ToIR_lowerCode(x_2, x_199, x_200, x_201, x_527);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_531 = x_528;
} else {
 lean_dec_ref(x_528);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_532 = lean_alloc_ctor(0, 1, 0);
} else {
 x_532 = x_521;
 lean_ctor_set_tag(x_532, 0);
}
lean_ctor_set(x_532, 0, x_481);
lean_ctor_set_tag(x_221, 11);
lean_ctor_set(x_221, 0, x_532);
x_533 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_533, 0, x_526);
lean_ctor_set(x_533, 1, x_520);
lean_ctor_set(x_533, 2, x_221);
lean_ctor_set(x_533, 3, x_529);
if (lean_is_scalar(x_531)) {
 x_534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_534 = x_531;
}
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_530);
return x_534;
}
else
{
lean_dec(x_526);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_481);
lean_free_object(x_221);
return x_528;
}
}
}
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_484);
lean_dec(x_482);
lean_dec(x_481);
lean_free_object(x_221);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_535 = lean_ctor_get(x_485, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_485, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_537 = x_485;
} else {
 lean_dec_ref(x_485);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_535);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
}
}
else
{
lean_object* x_539; 
lean_free_object(x_221);
lean_dec(x_339);
lean_dec(x_195);
lean_dec(x_35);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_206);
lean_inc(x_198);
lean_inc(x_2);
lean_inc(x_1);
x_539 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_198, x_206, x_199, x_200, x_201, x_214);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_542, 0, x_198);
lean_ctor_set(x_542, 1, x_206);
x_543 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_542, x_199, x_200, x_201, x_541);
return x_543;
}
else
{
uint8_t x_544; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_544 = !lean_is_exclusive(x_539);
if (x_544 == 0)
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_ctor_get(x_539, 0);
lean_dec(x_545);
x_546 = lean_ctor_get(x_540, 0);
lean_inc(x_546);
lean_dec(x_540);
lean_ctor_set(x_539, 0, x_546);
return x_539;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_539, 1);
lean_inc(x_547);
lean_dec(x_539);
x_548 = lean_ctor_get(x_540, 0);
lean_inc(x_548);
lean_dec(x_540);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_547);
return x_549;
}
}
}
else
{
uint8_t x_550; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_550 = !lean_is_exclusive(x_539);
if (x_550 == 0)
{
return x_539;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_539, 0);
x_552 = lean_ctor_get(x_539, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_539);
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
return x_553;
}
}
}
}
else
{
lean_object* x_554; uint8_t x_555; 
x_554 = lean_ctor_get(x_221, 0);
lean_inc(x_554);
lean_dec(x_221);
lean_inc(x_198);
x_555 = l_Lean_isExtern(x_215, x_198);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_206);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_556 = x_1;
} else {
 lean_dec_ref(x_1);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_554, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_554, 2);
lean_inc(x_558);
x_559 = lean_ctor_get(x_554, 3);
lean_inc(x_559);
lean_dec(x_554);
x_560 = lean_ctor_get(x_557, 0);
lean_inc(x_560);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 lean_ctor_release(x_557, 2);
 x_561 = x_557;
} else {
 lean_dec_ref(x_557);
 x_561 = lean_box(0);
}
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_562 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_560, x_199, x_200, x_201, x_214);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; 
lean_dec(x_558);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
lean_dec(x_562);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_565 = l_Lean_IR_ToIR_getCtorInfo(x_198, x_199, x_200, x_201, x_564);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec(x_565);
x_568 = lean_ctor_get(x_566, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_566, 1);
lean_inc(x_569);
lean_dec(x_566);
x_570 = lean_array_get_size(x_195);
x_571 = l_Array_extract___redArg(x_195, x_559, x_570);
lean_dec(x_195);
x_572 = lean_unsigned_to_nat(0u);
x_573 = l_Lean_IR_ToIR_lowerLet___closed__25;
x_574 = lean_array_get_size(x_569);
x_575 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_561)) {
 x_576 = lean_alloc_ctor(0, 3, 0);
} else {
 x_576 = x_561;
}
lean_ctor_set(x_576, 0, x_572);
lean_ctor_set(x_576, 1, x_574);
lean_ctor_set(x_576, 2, x_575);
x_577 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_571, x_37, x_569, x_555, x_576, x_573, x_572, x_199, x_567);
lean_dec(x_576);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_580 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_579);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_583 = x_580;
} else {
 lean_dec_ref(x_580);
 x_583 = lean_box(0);
}
lean_inc(x_581);
x_584 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_568, x_569, x_571, x_581, x_199, x_200, x_201, x_582);
lean_dec(x_571);
lean_dec(x_569);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_587 = x_584;
} else {
 lean_dec_ref(x_584);
 x_587 = lean_box(0);
}
x_588 = lean_box(7);
if (lean_is_scalar(x_583)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_583;
}
lean_ctor_set(x_589, 0, x_568);
lean_ctor_set(x_589, 1, x_578);
if (lean_is_scalar(x_556)) {
 x_590 = lean_alloc_ctor(0, 4, 0);
} else {
 x_590 = x_556;
}
lean_ctor_set(x_590, 0, x_581);
lean_ctor_set(x_590, 1, x_588);
lean_ctor_set(x_590, 2, x_589);
lean_ctor_set(x_590, 3, x_585);
if (lean_is_scalar(x_587)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_587;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_586);
return x_591;
}
else
{
lean_dec(x_583);
lean_dec(x_581);
lean_dec(x_578);
lean_dec(x_568);
lean_dec(x_556);
return x_584;
}
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_556);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_592 = lean_ctor_get(x_565, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_565, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_594 = x_565;
} else {
 lean_dec_ref(x_565);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
return x_595;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; uint8_t x_599; 
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_198);
x_596 = lean_ctor_get(x_562, 1);
lean_inc(x_596);
lean_dec(x_562);
x_597 = lean_ctor_get(x_563, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_598 = x_563;
} else {
 lean_dec_ref(x_563);
 x_598 = lean_box(0);
}
x_599 = l_Array_isEmpty___redArg(x_195);
lean_dec(x_195);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; 
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_35);
lean_dec(x_2);
x_600 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_601 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_600, x_199, x_200, x_201, x_596);
return x_601;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_602 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_596);
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = l_Lean_IR_ToIR_lowerCode(x_2, x_199, x_200, x_201, x_604);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_608 = x_605;
} else {
 lean_dec_ref(x_605);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_609 = lean_alloc_ctor(0, 1, 0);
} else {
 x_609 = x_598;
 lean_ctor_set_tag(x_609, 0);
}
lean_ctor_set(x_609, 0, x_558);
x_610 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_610, 0, x_609);
if (lean_is_scalar(x_556)) {
 x_611 = lean_alloc_ctor(0, 4, 0);
} else {
 x_611 = x_556;
}
lean_ctor_set(x_611, 0, x_603);
lean_ctor_set(x_611, 1, x_597);
lean_ctor_set(x_611, 2, x_610);
lean_ctor_set(x_611, 3, x_606);
if (lean_is_scalar(x_608)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_608;
}
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_607);
return x_612;
}
else
{
lean_dec(x_603);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_558);
lean_dec(x_556);
return x_605;
}
}
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_613 = lean_ctor_get(x_562, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_562, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_615 = x_562;
} else {
 lean_dec_ref(x_562);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
else
{
lean_object* x_617; 
lean_dec(x_554);
lean_dec(x_195);
lean_dec(x_35);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_206);
lean_inc(x_198);
lean_inc(x_2);
lean_inc(x_1);
x_617 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_198, x_206, x_199, x_200, x_201, x_214);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_620, 0, x_198);
lean_ctor_set(x_620, 1, x_206);
x_621 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_620, x_199, x_200, x_201, x_619);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_622 = lean_ctor_get(x_617, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_623 = x_617;
} else {
 lean_dec_ref(x_617);
 x_623 = lean_box(0);
}
x_624 = lean_ctor_get(x_618, 0);
lean_inc(x_624);
lean_dec(x_618);
if (lean_is_scalar(x_623)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_623;
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_622);
return x_625;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_626 = lean_ctor_get(x_617, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_617, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_628 = x_617;
} else {
 lean_dec_ref(x_617);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
}
}
}
case 7:
{
uint8_t x_630; 
lean_dec(x_215);
lean_free_object(x_211);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_630 = !lean_is_exclusive(x_221);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_631 = lean_ctor_get(x_221, 0);
lean_dec(x_631);
x_632 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_633 = lean_box(1);
x_634 = lean_unbox(x_633);
x_635 = l_Lean_Name_toString(x_198, x_634, x_196);
lean_ctor_set_tag(x_221, 3);
lean_ctor_set(x_221, 0, x_635);
x_636 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_636, 0, x_632);
lean_ctor_set(x_636, 1, x_221);
x_637 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_638 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
x_639 = l_Lean_MessageData_ofFormat(x_638);
x_640 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_639, x_200, x_201, x_214);
lean_dec(x_201);
lean_dec(x_200);
return x_640;
}
else
{
lean_object* x_641; lean_object* x_642; uint8_t x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_221);
x_641 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_642 = lean_box(1);
x_643 = lean_unbox(x_642);
x_644 = l_Lean_Name_toString(x_198, x_643, x_196);
x_645 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_645, 0, x_644);
x_646 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_646, 0, x_641);
lean_ctor_set(x_646, 1, x_645);
x_647 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_648 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
x_649 = l_Lean_MessageData_ofFormat(x_648);
x_650 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_649, x_200, x_201, x_214);
lean_dec(x_201);
lean_dec(x_200);
return x_650;
}
}
default: 
{
lean_object* x_651; 
lean_dec(x_221);
lean_dec(x_215);
lean_free_object(x_211);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_206);
lean_inc(x_198);
lean_inc(x_2);
lean_inc(x_1);
x_651 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_198, x_206, x_199, x_200, x_201, x_214);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_654, 0, x_198);
lean_ctor_set(x_654, 1, x_206);
x_655 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_654, x_199, x_200, x_201, x_653);
return x_655;
}
else
{
uint8_t x_656; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_656 = !lean_is_exclusive(x_651);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; 
x_657 = lean_ctor_get(x_651, 0);
lean_dec(x_657);
x_658 = lean_ctor_get(x_652, 0);
lean_inc(x_658);
lean_dec(x_652);
lean_ctor_set(x_651, 0, x_658);
return x_651;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_651, 1);
lean_inc(x_659);
lean_dec(x_651);
x_660 = lean_ctor_get(x_652, 0);
lean_inc(x_660);
lean_dec(x_652);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
}
else
{
uint8_t x_662; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_662 = !lean_is_exclusive(x_651);
if (x_662 == 0)
{
return x_651;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_651, 0);
x_664 = lean_ctor_get(x_651, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_651);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
}
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; lean_object* x_671; 
x_666 = lean_ctor_get(x_211, 0);
x_667 = lean_ctor_get(x_211, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_211);
x_668 = lean_ctor_get(x_666, 0);
lean_inc(x_668);
lean_dec(x_666);
x_669 = lean_box(0);
x_670 = lean_unbox(x_669);
lean_inc(x_198);
lean_inc(x_668);
x_671 = l_Lean_Environment_find_x3f(x_668, x_198, x_670);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; 
lean_dec(x_668);
lean_dec(x_206);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_672 = l_Lean_IR_ToIR_lowerLet___closed__5;
x_673 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_672, x_199, x_200, x_201, x_667);
return x_673;
}
else
{
lean_object* x_674; 
x_674 = lean_ctor_get(x_671, 0);
lean_inc(x_674);
lean_dec(x_671);
switch (lean_obj_tag(x_674)) {
case 0:
{
lean_object* x_675; lean_object* x_676; uint8_t x_677; 
lean_dec(x_668);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 x_675 = x_674;
} else {
 lean_dec_ref(x_674);
 x_675 = lean_box(0);
}
x_676 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_677 = lean_name_eq(x_198, x_676);
if (x_677 == 0)
{
lean_object* x_678; uint8_t x_679; 
x_678 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_679 = lean_name_eq(x_198, x_678);
if (x_679 == 0)
{
lean_object* x_680; lean_object* x_681; 
lean_inc(x_198);
x_680 = l_Lean_IR_ToIR_findDecl___redArg(x_198, x_201, x_667);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_683 = x_680;
} else {
 lean_dec_ref(x_680);
 x_683 = lean_box(0);
}
x_684 = lean_box(x_679);
x_685 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 2, 1);
lean_closure_set(x_685, 0, x_684);
x_686 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_687 = lean_box(1);
x_688 = lean_unbox(x_687);
x_689 = l_Lean_Name_toString(x_198, x_688, x_685);
if (lean_is_scalar(x_675)) {
 x_690 = lean_alloc_ctor(3, 1, 0);
} else {
 x_690 = x_675;
 lean_ctor_set_tag(x_690, 3);
}
lean_ctor_set(x_690, 0, x_689);
if (lean_is_scalar(x_683)) {
 x_691 = lean_alloc_ctor(5, 2, 0);
} else {
 x_691 = x_683;
 lean_ctor_set_tag(x_691, 5);
}
lean_ctor_set(x_691, 0, x_686);
lean_ctor_set(x_691, 1, x_690);
x_692 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_693 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
x_694 = l_Lean_MessageData_ofFormat(x_693);
x_695 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_694, x_200, x_201, x_682);
lean_dec(x_201);
lean_dec(x_200);
return x_695;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_675);
x_696 = lean_ctor_get(x_680, 1);
lean_inc(x_696);
lean_dec(x_680);
x_697 = lean_ctor_get(x_681, 0);
lean_inc(x_697);
lean_dec(x_681);
x_698 = lean_array_get_size(x_206);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
lean_dec(x_697);
x_7 = x_200;
x_8 = x_198;
x_9 = x_696;
x_10 = x_199;
x_11 = x_698;
x_12 = x_206;
x_13 = x_201;
x_14 = x_699;
goto block_27;
}
}
else
{
lean_object* x_700; lean_object* x_701; 
lean_dec(x_675);
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_700 = lean_box(13);
x_701 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_701, 0, x_700);
lean_ctor_set(x_701, 1, x_667);
return x_701;
}
}
else
{
lean_object* x_702; lean_object* x_703; 
lean_dec(x_675);
lean_dec(x_198);
x_702 = lean_unsigned_to_nat(2u);
x_703 = lean_array_get(x_197, x_206, x_702);
lean_dec(x_206);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
lean_dec(x_703);
x_705 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_704, x_199, x_200, x_201, x_667);
return x_705;
}
else
{
lean_object* x_706; 
x_706 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_199, x_200, x_201, x_667);
return x_706;
}
}
}
case 2:
{
lean_object* x_707; lean_object* x_708; 
lean_dec(x_674);
lean_dec(x_668);
lean_dec(x_206);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_707 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_708 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_707, x_199, x_200, x_201, x_667);
return x_708;
}
case 4:
{
lean_object* x_709; lean_object* x_710; uint8_t x_711; 
lean_dec(x_668);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 x_709 = x_674;
} else {
 lean_dec_ref(x_674);
 x_709 = lean_box(0);
}
x_710 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_711 = lean_name_eq(x_198, x_710);
if (x_711 == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_712 = lean_box(x_711);
x_713 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 2, 1);
lean_closure_set(x_713, 0, x_712);
x_714 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_715 = lean_box(1);
x_716 = lean_unbox(x_715);
x_717 = l_Lean_Name_toString(x_198, x_716, x_713);
if (lean_is_scalar(x_709)) {
 x_718 = lean_alloc_ctor(3, 1, 0);
} else {
 x_718 = x_709;
 lean_ctor_set_tag(x_718, 3);
}
lean_ctor_set(x_718, 0, x_717);
x_719 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_719, 0, x_714);
lean_ctor_set(x_719, 1, x_718);
x_720 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_721 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_721, 0, x_719);
lean_ctor_set(x_721, 1, x_720);
x_722 = l_Lean_MessageData_ofFormat(x_721);
x_723 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_722, x_200, x_201, x_667);
lean_dec(x_201);
lean_dec(x_200);
return x_723;
}
else
{
lean_object* x_724; lean_object* x_725; 
lean_dec(x_709);
lean_dec(x_198);
x_724 = lean_unsigned_to_nat(2u);
x_725 = lean_array_get(x_197, x_206, x_724);
lean_dec(x_206);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
lean_dec(x_725);
x_727 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_726, x_199, x_200, x_201, x_667);
return x_727;
}
else
{
lean_object* x_728; 
x_728 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_199, x_200, x_201, x_667);
return x_728;
}
}
}
case 5:
{
lean_object* x_729; lean_object* x_730; 
lean_dec(x_674);
lean_dec(x_668);
lean_dec(x_206);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_729 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_730 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_729, x_199, x_200, x_201, x_667);
return x_730;
}
case 6:
{
lean_object* x_731; lean_object* x_732; uint8_t x_733; 
lean_dec(x_196);
x_731 = lean_ctor_get(x_674, 0);
lean_inc(x_731);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 x_732 = x_674;
} else {
 lean_dec_ref(x_674);
 x_732 = lean_box(0);
}
lean_inc(x_198);
x_733 = l_Lean_isExtern(x_668, x_198);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_206);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_734 = x_1;
} else {
 lean_dec_ref(x_1);
 x_734 = lean_box(0);
}
x_735 = lean_ctor_get(x_731, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_731, 2);
lean_inc(x_736);
x_737 = lean_ctor_get(x_731, 3);
lean_inc(x_737);
lean_dec(x_731);
x_738 = lean_ctor_get(x_735, 0);
lean_inc(x_738);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 lean_ctor_release(x_735, 2);
 x_739 = x_735;
} else {
 lean_dec_ref(x_735);
 x_739 = lean_box(0);
}
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_740 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_738, x_199, x_200, x_201, x_667);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; 
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; 
lean_dec(x_736);
lean_dec(x_732);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec(x_740);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
x_743 = l_Lean_IR_ToIR_getCtorInfo(x_198, x_199, x_200, x_201, x_742);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_ctor_get(x_744, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_744, 1);
lean_inc(x_747);
lean_dec(x_744);
x_748 = lean_array_get_size(x_195);
x_749 = l_Array_extract___redArg(x_195, x_737, x_748);
lean_dec(x_195);
x_750 = lean_unsigned_to_nat(0u);
x_751 = l_Lean_IR_ToIR_lowerLet___closed__25;
x_752 = lean_array_get_size(x_747);
x_753 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_739)) {
 x_754 = lean_alloc_ctor(0, 3, 0);
} else {
 x_754 = x_739;
}
lean_ctor_set(x_754, 0, x_750);
lean_ctor_set(x_754, 1, x_752);
lean_ctor_set(x_754, 2, x_753);
x_755 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_749, x_37, x_747, x_733, x_754, x_751, x_750, x_199, x_745);
lean_dec(x_754);
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
x_758 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_757);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_761 = x_758;
} else {
 lean_dec_ref(x_758);
 x_761 = lean_box(0);
}
lean_inc(x_759);
x_762 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_746, x_747, x_749, x_759, x_199, x_200, x_201, x_760);
lean_dec(x_749);
lean_dec(x_747);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_763 = lean_ctor_get(x_762, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_762, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_762)) {
 lean_ctor_release(x_762, 0);
 lean_ctor_release(x_762, 1);
 x_765 = x_762;
} else {
 lean_dec_ref(x_762);
 x_765 = lean_box(0);
}
x_766 = lean_box(7);
if (lean_is_scalar(x_761)) {
 x_767 = lean_alloc_ctor(0, 2, 0);
} else {
 x_767 = x_761;
}
lean_ctor_set(x_767, 0, x_746);
lean_ctor_set(x_767, 1, x_756);
if (lean_is_scalar(x_734)) {
 x_768 = lean_alloc_ctor(0, 4, 0);
} else {
 x_768 = x_734;
}
lean_ctor_set(x_768, 0, x_759);
lean_ctor_set(x_768, 1, x_766);
lean_ctor_set(x_768, 2, x_767);
lean_ctor_set(x_768, 3, x_763);
if (lean_is_scalar(x_765)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_765;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_764);
return x_769;
}
else
{
lean_dec(x_761);
lean_dec(x_759);
lean_dec(x_756);
lean_dec(x_746);
lean_dec(x_734);
return x_762;
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec(x_734);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_770 = lean_ctor_get(x_743, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_743, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_772 = x_743;
} else {
 lean_dec_ref(x_743);
 x_772 = lean_box(0);
}
if (lean_is_scalar(x_772)) {
 x_773 = lean_alloc_ctor(1, 2, 0);
} else {
 x_773 = x_772;
}
lean_ctor_set(x_773, 0, x_770);
lean_ctor_set(x_773, 1, x_771);
return x_773;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; uint8_t x_777; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec(x_198);
x_774 = lean_ctor_get(x_740, 1);
lean_inc(x_774);
lean_dec(x_740);
x_775 = lean_ctor_get(x_741, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 x_776 = x_741;
} else {
 lean_dec_ref(x_741);
 x_776 = lean_box(0);
}
x_777 = l_Array_isEmpty___redArg(x_195);
lean_dec(x_195);
if (x_777 == 0)
{
lean_object* x_778; lean_object* x_779; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_736);
lean_dec(x_734);
lean_dec(x_732);
lean_dec(x_35);
lean_dec(x_2);
x_778 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_779 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_778, x_199, x_200, x_201, x_774);
return x_779;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_780 = l_Lean_IR_ToIR_bindVar___redArg(x_35, x_199, x_774);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_783 = l_Lean_IR_ToIR_lowerCode(x_2, x_199, x_200, x_201, x_782);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_786 = x_783;
} else {
 lean_dec_ref(x_783);
 x_786 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_787 = lean_alloc_ctor(0, 1, 0);
} else {
 x_787 = x_776;
 lean_ctor_set_tag(x_787, 0);
}
lean_ctor_set(x_787, 0, x_736);
if (lean_is_scalar(x_732)) {
 x_788 = lean_alloc_ctor(11, 1, 0);
} else {
 x_788 = x_732;
 lean_ctor_set_tag(x_788, 11);
}
lean_ctor_set(x_788, 0, x_787);
if (lean_is_scalar(x_734)) {
 x_789 = lean_alloc_ctor(0, 4, 0);
} else {
 x_789 = x_734;
}
lean_ctor_set(x_789, 0, x_781);
lean_ctor_set(x_789, 1, x_775);
lean_ctor_set(x_789, 2, x_788);
lean_ctor_set(x_789, 3, x_784);
if (lean_is_scalar(x_786)) {
 x_790 = lean_alloc_ctor(0, 2, 0);
} else {
 x_790 = x_786;
}
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_785);
return x_790;
}
else
{
lean_dec(x_781);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_736);
lean_dec(x_734);
lean_dec(x_732);
return x_783;
}
}
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec(x_736);
lean_dec(x_734);
lean_dec(x_732);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
x_791 = lean_ctor_get(x_740, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_740, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_793 = x_740;
} else {
 lean_dec_ref(x_740);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
}
else
{
lean_object* x_795; 
lean_dec(x_732);
lean_dec(x_731);
lean_dec(x_195);
lean_dec(x_35);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_206);
lean_inc(x_198);
lean_inc(x_2);
lean_inc(x_1);
x_795 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_198, x_206, x_199, x_200, x_201, x_667);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; 
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
x_798 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_798, 0, x_198);
lean_ctor_set(x_798, 1, x_206);
x_799 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_798, x_199, x_200, x_201, x_797);
return x_799;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_800 = lean_ctor_get(x_795, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_801 = x_795;
} else {
 lean_dec_ref(x_795);
 x_801 = lean_box(0);
}
x_802 = lean_ctor_get(x_796, 0);
lean_inc(x_802);
lean_dec(x_796);
if (lean_is_scalar(x_801)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_801;
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_800);
return x_803;
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_804 = lean_ctor_get(x_795, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_795, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_806 = x_795;
} else {
 lean_dec_ref(x_795);
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
case 7:
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
lean_dec(x_668);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 x_808 = x_674;
} else {
 lean_dec_ref(x_674);
 x_808 = lean_box(0);
}
x_809 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_810 = lean_box(1);
x_811 = lean_unbox(x_810);
x_812 = l_Lean_Name_toString(x_198, x_811, x_196);
if (lean_is_scalar(x_808)) {
 x_813 = lean_alloc_ctor(3, 1, 0);
} else {
 x_813 = x_808;
 lean_ctor_set_tag(x_813, 3);
}
lean_ctor_set(x_813, 0, x_812);
x_814 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_814, 0, x_809);
lean_ctor_set(x_814, 1, x_813);
x_815 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_816 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_816, 0, x_814);
lean_ctor_set(x_816, 1, x_815);
x_817 = l_Lean_MessageData_ofFormat(x_816);
x_818 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_817, x_200, x_201, x_667);
lean_dec(x_201);
lean_dec(x_200);
return x_818;
}
default: 
{
lean_object* x_819; 
lean_dec(x_674);
lean_dec(x_668);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_206);
lean_inc(x_198);
lean_inc(x_2);
lean_inc(x_1);
x_819 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_198, x_206, x_199, x_200, x_201, x_667);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
x_822 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_822, 0, x_198);
lean_ctor_set(x_822, 1, x_206);
x_823 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_822, x_199, x_200, x_201, x_821);
return x_823;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_824 = lean_ctor_get(x_819, 1);
lean_inc(x_824);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_825 = x_819;
} else {
 lean_dec_ref(x_819);
 x_825 = lean_box(0);
}
x_826 = lean_ctor_get(x_820, 0);
lean_inc(x_826);
lean_dec(x_820);
if (lean_is_scalar(x_825)) {
 x_827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_827 = x_825;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_824);
return x_827;
}
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_2);
lean_dec(x_1);
x_828 = lean_ctor_get(x_819, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_819, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_830 = x_819;
} else {
 lean_dec_ref(x_819);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(1, 2, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_828);
lean_ctor_set(x_831, 1, x_829);
return x_831;
}
}
}
}
}
}
else
{
uint8_t x_832; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_832 = !lean_is_exclusive(x_208);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; 
x_833 = lean_ctor_get(x_208, 0);
lean_dec(x_833);
x_834 = lean_ctor_get(x_209, 0);
lean_inc(x_834);
lean_dec(x_209);
lean_ctor_set(x_208, 0, x_834);
return x_208;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_835 = lean_ctor_get(x_208, 1);
lean_inc(x_835);
lean_dec(x_208);
x_836 = lean_ctor_get(x_209, 0);
lean_inc(x_836);
lean_dec(x_209);
x_837 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_835);
return x_837;
}
}
}
else
{
uint8_t x_838; 
lean_dec(x_206);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_838 = !lean_is_exclusive(x_208);
if (x_838 == 0)
{
return x_208;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_208, 0);
x_840 = lean_ctor_get(x_208, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_208);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
else
{
uint8_t x_842; 
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_842 = !lean_is_exclusive(x_205);
if (x_842 == 0)
{
return x_205;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_843 = lean_ctor_get(x_205, 0);
x_844 = lean_ctor_get(x_205, 1);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_205);
x_845 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set(x_845, 1, x_844);
return x_845;
}
}
}
}
default: 
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; uint8_t x_961; 
lean_dec(x_35);
x_955 = lean_ctor_get(x_36, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_36, 1);
lean_inc(x_956);
lean_dec(x_36);
x_957 = lean_st_ref_get(x_3, x_6);
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
lean_dec(x_958);
x_960 = lean_ctor_get(x_957, 1);
lean_inc(x_960);
lean_dec(x_957);
x_961 = !lean_is_exclusive(x_959);
if (x_961 == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; uint64_t x_965; uint64_t x_966; uint64_t x_967; uint64_t x_968; uint64_t x_969; uint64_t x_970; uint64_t x_971; size_t x_972; size_t x_973; size_t x_974; size_t x_975; size_t x_976; lean_object* x_977; lean_object* x_978; 
x_962 = lean_ctor_get(x_959, 1);
x_963 = lean_ctor_get(x_959, 0);
lean_dec(x_963);
x_964 = lean_array_get_size(x_962);
x_965 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_955);
x_966 = 32;
x_967 = lean_uint64_shift_right(x_965, x_966);
x_968 = lean_uint64_xor(x_965, x_967);
x_969 = 16;
x_970 = lean_uint64_shift_right(x_968, x_969);
x_971 = lean_uint64_xor(x_968, x_970);
x_972 = lean_uint64_to_usize(x_971);
x_973 = lean_usize_of_nat(x_964);
lean_dec(x_964);
x_974 = 1;
x_975 = lean_usize_sub(x_973, x_974);
x_976 = lean_usize_land(x_972, x_975);
x_977 = lean_array_uget(x_962, x_976);
lean_dec(x_962);
x_978 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_955, x_977);
lean_dec(x_977);
lean_dec(x_955);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; 
lean_free_object(x_959);
lean_dec(x_956);
lean_dec(x_2);
lean_dec(x_1);
x_979 = l_Lean_IR_ToIR_lowerLet___closed__39;
x_980 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_979, x_3, x_4, x_5, x_960);
return x_980;
}
else
{
lean_object* x_981; 
x_981 = lean_ctor_get(x_978, 0);
lean_inc(x_981);
lean_dec(x_978);
switch (lean_obj_tag(x_981)) {
case 0:
{
lean_object* x_982; size_t x_983; size_t x_984; lean_object* x_985; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
lean_dec(x_981);
x_983 = lean_array_size(x_956);
x_984 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_985 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_983, x_984, x_956, x_3, x_4, x_5, x_960);
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec(x_985);
lean_ctor_set_tag(x_959, 8);
lean_ctor_set(x_959, 1, x_986);
lean_ctor_set(x_959, 0, x_982);
x_988 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_959, x_3, x_4, x_5, x_987);
return x_988;
}
else
{
uint8_t x_989; 
lean_dec(x_982);
lean_free_object(x_959);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_989 = !lean_is_exclusive(x_985);
if (x_989 == 0)
{
return x_985;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_985, 0);
x_991 = lean_ctor_get(x_985, 1);
lean_inc(x_991);
lean_inc(x_990);
lean_dec(x_985);
x_992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_992, 0, x_990);
lean_ctor_set(x_992, 1, x_991);
return x_992;
}
}
}
case 1:
{
lean_object* x_993; lean_object* x_994; 
lean_dec(x_981);
lean_free_object(x_959);
lean_dec(x_956);
lean_dec(x_2);
lean_dec(x_1);
x_993 = l_Lean_IR_ToIR_lowerLet___closed__39;
x_994 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_993, x_3, x_4, x_5, x_960);
return x_994;
}
default: 
{
lean_object* x_995; 
lean_free_object(x_959);
lean_dec(x_956);
x_995 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_960);
return x_995;
}
}
}
}
else
{
lean_object* x_996; lean_object* x_997; uint64_t x_998; uint64_t x_999; uint64_t x_1000; uint64_t x_1001; uint64_t x_1002; uint64_t x_1003; uint64_t x_1004; size_t x_1005; size_t x_1006; size_t x_1007; size_t x_1008; size_t x_1009; lean_object* x_1010; lean_object* x_1011; 
x_996 = lean_ctor_get(x_959, 1);
lean_inc(x_996);
lean_dec(x_959);
x_997 = lean_array_get_size(x_996);
x_998 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_955);
x_999 = 32;
x_1000 = lean_uint64_shift_right(x_998, x_999);
x_1001 = lean_uint64_xor(x_998, x_1000);
x_1002 = 16;
x_1003 = lean_uint64_shift_right(x_1001, x_1002);
x_1004 = lean_uint64_xor(x_1001, x_1003);
x_1005 = lean_uint64_to_usize(x_1004);
x_1006 = lean_usize_of_nat(x_997);
lean_dec(x_997);
x_1007 = 1;
x_1008 = lean_usize_sub(x_1006, x_1007);
x_1009 = lean_usize_land(x_1005, x_1008);
x_1010 = lean_array_uget(x_996, x_1009);
lean_dec(x_996);
x_1011 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_955, x_1010);
lean_dec(x_1010);
lean_dec(x_955);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; 
lean_dec(x_956);
lean_dec(x_2);
lean_dec(x_1);
x_1012 = l_Lean_IR_ToIR_lowerLet___closed__39;
x_1013 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_1012, x_3, x_4, x_5, x_960);
return x_1013;
}
else
{
lean_object* x_1014; 
x_1014 = lean_ctor_get(x_1011, 0);
lean_inc(x_1014);
lean_dec(x_1011);
switch (lean_obj_tag(x_1014)) {
case 0:
{
lean_object* x_1015; size_t x_1016; size_t x_1017; lean_object* x_1018; 
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
lean_dec(x_1014);
x_1016 = lean_array_size(x_956);
x_1017 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1018 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_1016, x_1017, x_956, x_3, x_4, x_5, x_960);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
lean_dec(x_1018);
x_1021 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_1021, 0, x_1015);
lean_ctor_set(x_1021, 1, x_1019);
x_1022 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1021, x_3, x_4, x_5, x_1020);
return x_1022;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_1015);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1023 = lean_ctor_get(x_1018, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1018, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 x_1025 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1025 = lean_box(0);
}
if (lean_is_scalar(x_1025)) {
 x_1026 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1026 = x_1025;
}
lean_ctor_set(x_1026, 0, x_1023);
lean_ctor_set(x_1026, 1, x_1024);
return x_1026;
}
}
case 1:
{
lean_object* x_1027; lean_object* x_1028; 
lean_dec(x_1014);
lean_dec(x_956);
lean_dec(x_2);
lean_dec(x_1);
x_1027 = l_Lean_IR_ToIR_lowerLet___closed__39;
x_1028 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_1027, x_3, x_4, x_5, x_960);
return x_1028;
}
default: 
{
lean_object* x_1029; 
lean_dec(x_956);
x_1029 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_960);
return x_1029;
}
}
}
}
}
}
block_27:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_nat_dec_lt(x_11, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_11, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_19 = l_Array_extract___redArg(x_12, x_18, x_15);
x_20 = l_Array_extract___redArg(x_12, x_15, x_11);
lean_dec(x_12);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_21, x_20, x_10, x_7, x_13, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_11);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_12);
x_24 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_23, x_10, x_7, x_13, x_9);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_11);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_12);
x_26 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_25, x_10, x_7, x_13, x_9);
return x_26;
}
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_IR_ToIR_lowerLet___closed__2;
x_33 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_32, x_28, x_29, x_30, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_11 = x_1;
} else {
 lean_dec_ref(x_1);
 x_11 = lean_box(0);
}
x_12 = l_Lean_IR_ToIR_bindVar___redArg(x_9, x_5, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_IR_ToIR_newVar___redArg(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_39; 
lean_dec(x_10);
x_39 = lean_box(7);
x_19 = x_39;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_17;
goto block_38;
}
case 3:
{
lean_object* x_40; 
lean_dec(x_10);
x_40 = lean_box(7);
x_19 = x_40;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_17;
goto block_38;
}
case 7:
{
lean_object* x_41; 
lean_dec(x_10);
x_41 = lean_box(7);
x_19 = x_41;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_17;
goto block_38;
}
default: 
{
lean_object* x_42; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = l_Lean_IR_ToIR_lowerType(x_10, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_19 = x_43;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_44;
goto block_38;
}
else
{
uint8_t x_45; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
block_38:
{
lean_object* x_24; 
x_24 = l_Lean_IR_ToIR_lowerCode(x_2, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_box(7);
lean_inc(x_16);
if (lean_is_scalar(x_18)) {
 x_28 = lean_alloc_ctor(8, 2, 0);
} else {
 x_28 = x_18;
 lean_ctor_set_tag(x_28, 8);
}
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_4);
if (lean_is_scalar(x_11)) {
 x_29 = lean_alloc_ctor(0, 4, 0);
} else {
 x_29 = x_11;
}
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_26);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_24, 0, x_30);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_box(7);
lean_inc(x_16);
if (lean_is_scalar(x_18)) {
 x_34 = lean_alloc_ctor(8, 2, 0);
} else {
 x_34 = x_18;
 lean_ctor_set_tag(x_34, 8);
}
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_4);
if (lean_is_scalar(x_11)) {
 x_35 = lean_alloc_ctor(0, 4, 0);
} else {
 x_35 = x_11;
}
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_31);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_3);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_IR_ToIR_bindErased___redArg(x_7, x_3, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_8, x_3, x_4, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_ToIR_lowerCode(x_2, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_10, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_4);
x_21 = lean_nat_dec_lt(x_7, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_5);
x_22 = l_Lean_IR_ToIR_lowerCode(x_1, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_array_fget(x_4, x_7);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_8, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_29);
x_31 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_24);
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
x_44 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_24, x_43);
lean_dec(x_43);
lean_dec(x_24);
if (lean_obj_tag(x_44) == 0)
{
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
x_15 = x_28;
goto block_19;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = lean_array_get(x_47, x_3, x_7);
switch (lean_obj_tag(x_48)) {
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_6, x_49);
x_51 = lean_nat_add(x_7, x_49);
lean_dec(x_7);
lean_inc(x_5);
x_52 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_50, x_51, x_8, x_9, x_10, x_28);
lean_dec(x_50);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_nat_add(x_55, x_6);
x_57 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_46);
lean_ctor_set(x_57, 3, x_54);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_ctor_get(x_2, 2);
x_61 = lean_nat_add(x_60, x_6);
x_62 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_46);
lean_ctor_set(x_62, 3, x_58);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
else
{
lean_dec(x_46);
lean_dec(x_5);
return x_52;
}
}
case 3:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_48, 2);
lean_inc(x_65);
lean_dec(x_48);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_7, x_66);
lean_dec(x_7);
lean_inc(x_5);
x_68 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_67, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
x_73 = lean_nat_add(x_71, x_72);
x_74 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_64);
lean_ctor_set(x_74, 3, x_46);
lean_ctor_set(x_74, 4, x_65);
lean_ctor_set(x_74, 5, x_70);
lean_ctor_set(x_68, 0, x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_68);
x_77 = lean_ctor_get(x_2, 2);
x_78 = lean_ctor_get(x_2, 3);
x_79 = lean_nat_add(x_77, x_78);
x_80 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_64);
lean_ctor_set(x_80, 3, x_46);
lean_ctor_set(x_80, 4, x_65);
lean_ctor_set(x_80, 5, x_75);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
else
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_46);
lean_dec(x_5);
return x_68;
}
}
default: 
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_48);
lean_dec(x_46);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_7, x_82);
lean_dec(x_7);
x_7 = x_83;
x_11 = x_28;
goto _start;
}
}
}
else
{
lean_dec(x_45);
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
x_15 = x_28;
goto block_19;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_23);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_7, x_85);
lean_dec(x_7);
x_7 = x_86;
goto _start;
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
x_8 = x_12;
x_9 = x_13;
x_10 = x_14;
x_11 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_9 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_3, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_4);
x_22 = lean_array_get_size(x_20);
lean_dec(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_21, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_22);
x_26 = l_Array_extract___redArg(x_4, x_25, x_22);
x_27 = l_Array_extract___redArg(x_4, x_22, x_21);
lean_dec(x_4);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_28, x_27, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_10, 0, x_31);
lean_ctor_set(x_29, 0, x_10);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_10, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_10);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_22);
lean_dec(x_21);
x_39 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_4);
x_40 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_39, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_10, 0, x_42);
lean_ctor_set(x_40, 0, x_10);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_10, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_free_object(x_10);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_22);
lean_dec(x_21);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_4);
x_51 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_50, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_ctor_set(x_10, 0, x_53);
lean_ctor_set(x_51, 0, x_10);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set(x_10, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_10);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
lean_dec(x_10);
x_62 = lean_ctor_get(x_9, 1);
lean_inc(x_62);
lean_dec(x_9);
x_63 = lean_ctor_get(x_61, 3);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_array_get_size(x_4);
x_65 = lean_array_get_size(x_63);
lean_dec(x_63);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = lean_nat_dec_eq(x_64, x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_unsigned_to_nat(0u);
lean_inc(x_65);
x_69 = l_Array_extract___redArg(x_4, x_68, x_65);
x_70 = l_Array_extract___redArg(x_4, x_65, x_64);
lean_dec(x_4);
x_71 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_71, x_70, x_5, x_6, x_7, x_62);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_65);
lean_dec(x_64);
x_82 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_4);
x_83 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_82, x_5, x_6, x_7, x_62);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_65);
lean_dec(x_64);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_4);
x_94 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_93, x_5, x_6, x_7, x_62);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_95);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_10 = x_1;
} else {
 lean_dec_ref(x_1);
 x_10 = lean_box(0);
}
x_11 = l_Lean_IR_ToIR_bindVar___redArg(x_8, x_4, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_28; 
lean_dec(x_9);
x_28 = lean_box(7);
x_14 = x_28;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_13;
goto block_27;
}
case 3:
{
lean_object* x_29; 
lean_dec(x_9);
x_29 = lean_box(7);
x_14 = x_29;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_13;
goto block_27;
}
case 7:
{
lean_object* x_30; 
lean_dec(x_9);
x_30 = lean_box(7);
x_14 = x_30;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_13;
goto block_27;
}
default: 
{
lean_object* x_31; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_IR_ToIR_lowerType(x_9, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_14 = x_32;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_33;
goto block_27;
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
block_27:
{
lean_object* x_19; 
x_19 = l_Lean_IR_ToIR_lowerCode(x_2, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_is_scalar(x_10)) {
 x_22 = lean_alloc_ctor(0, 4, 0);
} else {
 x_22 = x_10;
}
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
if (lean_is_scalar(x_10)) {
 x_25 = lean_alloc_ctor(0, 4, 0);
} else {
 x_25 = x_10;
}
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_3);
lean_ctor_set(x_25, 3, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ToIR_lowerLet___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_ToIR_lowerLet___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerResultType.resultTypeForArity", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid arity", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(412u);
x_4 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
x_5 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerType___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = l_Lean_IR_ToIR_lowerType___closed__8;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
goto block_5;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
return x_13;
}
}
else
{
goto block_5;
}
}
else
{
goto block_5;
}
}
case 7:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_16;
goto _start;
}
default: 
{
lean_dec(x_2);
goto block_5;
}
}
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
x_4 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
x_8 = l_Lean_IR_ToIR_lowerType(x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_size(x_8);
x_11 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_12 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_10, x_11, x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_8);
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_IR_ToIR_lowerResultType(x_7, x_15, x_2, x_3, x_4, x_14);
lean_dec(x_7);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = l_Lean_IR_ToIR_lowerCode(x_20, x_2, x_3, x_4, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_9);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
lean_dec(x_9);
x_36 = l_Lean_IR_ToIR_lowerCode(x_35, x_2, x_3, x_4, x_18);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_13);
lean_ctor_set(x_41, 2, x_17);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_46 = x_36;
} else {
 lean_dec_ref(x_36);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = l_List_isEmpty___redArg(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_13);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_9, 0, x_55);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_16);
lean_free_object(x_9);
lean_dec(x_50);
x_56 = lean_ir_mk_dummy_extern_decl(x_6, x_13, x_51);
x_57 = l_Lean_IR_ToIR_addDecl___redArg(x_56, x_4, x_52);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = l_List_isEmpty___redArg(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_6);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set(x_9, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_9);
lean_dec(x_64);
x_71 = lean_ir_mk_dummy_extern_decl(x_6, x_13, x_65);
x_72 = l_Lean_IR_ToIR_addDecl___redArg(x_71, x_4, x_66);
lean_dec(x_4);
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
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_9, 0);
lean_inc(x_77);
lean_dec(x_9);
x_78 = lean_ctor_get(x_16, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_16, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_80 = x_16;
} else {
 lean_dec_ref(x_16);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
x_82 = l_List_isEmpty___redArg(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
x_83 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_83, 0, x_6);
lean_ctor_set(x_83, 1, x_13);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_77);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_80);
lean_dec(x_77);
x_86 = lean_ir_mk_dummy_extern_decl(x_6, x_13, x_78);
x_87 = l_Lean_IR_ToIR_addDecl___redArg(x_86, x_4, x_79);
lean_dec(x_4);
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
else
{
uint8_t x_92; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_16);
if (x_92 == 0)
{
return x_16;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_16, 0);
x_94 = lean_ctor_get(x_16, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_16);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
return x_12;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_12, 0);
x_98 = lean_ctor_get(x_12, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_12);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl), 5, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_ToIR_M_run___redArg(x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
x_15 = x_4;
goto block_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_array_push(x_4, x_20);
x_15 = x_21;
goto block_19;
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_15;
x_7 = x_14;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_toIR___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = l_Lean_IR_toIR___closed__0;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_6, x_7, x_5, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_toIR(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CtorLayout(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CtorLayout(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ToIR_M_run___redArg___closed__0 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__0);
l_Lean_IR_ToIR_M_run___redArg___closed__1 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__1);
l_Lean_IR_ToIR_M_run___redArg___closed__2 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__2);
l_Lean_IR_ToIR_M_run___redArg___closed__3 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__3);
l_Lean_IR_ToIR_M_run___redArg___closed__4 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__4);
l_Lean_IR_ToIR_M_run___redArg___closed__5 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__5);
l_Lean_IR_ToIR_addDecl___redArg___closed__0 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__0);
l_Lean_IR_ToIR_addDecl___redArg___closed__1 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__1);
l_Lean_IR_ToIR_addDecl___redArg___closed__2 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__2);
l_Lean_IR_ToIR_addDecl___redArg___closed__3 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__3);
l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__0);
l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__1);
l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__2 = _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__2);
l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3 = _init_l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_List_foldl___at___List_foldl___at___Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0_spec__0_spec__0___redArg___closed__3);
l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___lam__0___closed__0);
l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__0);
l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__1);
l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413__spec__0___redArg___closed__2);
if (builtin) {res = l_Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_413_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_ToIR_scalarTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_ToIR_scalarTypeExt);
lean_dec_ref(res);
}l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0 = _init_l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__0);
l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1 = _init_l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__1);
l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2 = _init_l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__0___closed__2);
l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__0);
l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__1);
l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__2);
l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__3);
l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__4 = _init_l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_fillCache_spec__1___redArg___closed__4);
l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__0 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__0);
l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__1 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__1);
l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__2 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__2);
l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__3 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType_fillCache___closed__3);
l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__0);
l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__1);
l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__2);
l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___redArg___closed__3);
l_Lean_IR_ToIR_lowerEnumToScalarType___closed__0 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType___closed__0);
l_Lean_IR_ToIR_lowerType___closed__0 = _init_l_Lean_IR_ToIR_lowerType___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__0);
l_Lean_IR_ToIR_lowerType___closed__1 = _init_l_Lean_IR_ToIR_lowerType___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__1);
l_Lean_IR_ToIR_lowerType___closed__2 = _init_l_Lean_IR_ToIR_lowerType___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__2);
l_Lean_IR_ToIR_lowerType___closed__3 = _init_l_Lean_IR_ToIR_lowerType___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__3);
l_Lean_IR_ToIR_lowerType___closed__4 = _init_l_Lean_IR_ToIR_lowerType___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__4);
l_Lean_IR_ToIR_lowerType___closed__5 = _init_l_Lean_IR_ToIR_lowerType___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__5);
l_Lean_IR_ToIR_lowerType___closed__6 = _init_l_Lean_IR_ToIR_lowerType___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__6);
l_Lean_IR_ToIR_lowerType___closed__7 = _init_l_Lean_IR_ToIR_lowerType___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__7);
l_Lean_IR_ToIR_lowerType___closed__8 = _init_l_Lean_IR_ToIR_lowerType___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__8);
l_Lean_IR_ToIR_lowerType___closed__9 = _init_l_Lean_IR_ToIR_lowerType___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__9);
l_Lean_IR_ToIR_lowerType___closed__10 = _init_l_Lean_IR_ToIR_lowerType___closed__10();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__10);
l_Lean_IR_ToIR_lowerType___closed__11 = _init_l_Lean_IR_ToIR_lowerType___closed__11();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__11);
l_Lean_IR_ToIR_initFn___closed__0____x40_Lean_Compiler_IR_ToIR___hyg_1189_ = _init_l_Lean_IR_ToIR_initFn___closed__0____x40_Lean_Compiler_IR_ToIR___hyg_1189_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__0____x40_Lean_Compiler_IR_ToIR___hyg_1189_);
l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_ = _init_l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__1____x40_Lean_Compiler_IR_ToIR___hyg_1189_);
if (builtin) {res = l_Lean_IR_ToIR_initFn____x40_Lean_Compiler_IR_ToIR___hyg_1189_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_ToIR_ctorInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_ToIR_ctorInfoExt);
lean_dec_ref(res);
}l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__0 = _init_l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__0);
l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__1 = _init_l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__1);
l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__2 = _init_l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_getCtorInfo_fillCache___closed__2);
l_Lean_IR_ToIR_getCtorInfo___closed__0 = _init_l_Lean_IR_ToIR_getCtorInfo___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_getCtorInfo___closed__0);
l_Lean_IR_ToIR_lowerArg___closed__0 = _init_l_Lean_IR_ToIR_lowerArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__0);
l_Lean_IR_ToIR_lowerArg___closed__1 = _init_l_Lean_IR_ToIR_lowerArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__1);
l_Lean_IR_ToIR_lowerArg___closed__2 = _init_l_Lean_IR_ToIR_lowerArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__2);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3);
l_Lean_IR_ToIR_instInhabitedTranslatedProj = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj);
l_Lean_IR_ToIR_lowerProj___closed__0 = _init_l_Lean_IR_ToIR_lowerProj___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerProj___closed__0);
l_Lean_IR_ToIR_lowerAlt_loop___closed__0 = _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerAlt_loop___closed__0);
l_Lean_IR_ToIR_lowerAlt_loop___closed__1 = _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerAlt_loop___closed__1);
l_Lean_IR_ToIR_lowerAlt_loop___closed__2 = _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerAlt_loop___closed__2);
l_Lean_IR_ToIR_lowerCode___closed__0 = _init_l_Lean_IR_ToIR_lowerCode___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__0);
l_Lean_IR_ToIR_lowerCode___closed__1 = _init_l_Lean_IR_ToIR_lowerCode___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__1);
l_Lean_IR_ToIR_lowerCode___closed__2 = _init_l_Lean_IR_ToIR_lowerCode___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__2);
l_Lean_IR_ToIR_lowerCode___closed__3 = _init_l_Lean_IR_ToIR_lowerCode___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__3);
l_Lean_IR_ToIR_lowerCode___closed__4 = _init_l_Lean_IR_ToIR_lowerCode___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__4);
l_Lean_IR_ToIR_lowerCode___closed__5 = _init_l_Lean_IR_ToIR_lowerCode___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__5);
l_Lean_IR_ToIR_lowerLet___closed__0 = _init_l_Lean_IR_ToIR_lowerLet___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__0);
l_Lean_IR_ToIR_lowerLet___closed__1 = _init_l_Lean_IR_ToIR_lowerLet___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__1);
l_Lean_IR_ToIR_lowerLet___closed__2 = _init_l_Lean_IR_ToIR_lowerLet___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__2);
l_Lean_IR_ToIR_lowerLet___closed__3 = _init_l_Lean_IR_ToIR_lowerLet___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__3);
l_Lean_IR_ToIR_lowerLet___closed__4 = _init_l_Lean_IR_ToIR_lowerLet___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__4);
l_Lean_IR_ToIR_lowerLet___closed__5 = _init_l_Lean_IR_ToIR_lowerLet___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__5);
l_Lean_IR_ToIR_lowerLet___closed__6 = _init_l_Lean_IR_ToIR_lowerLet___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__6);
l_Lean_IR_ToIR_lowerLet___closed__7 = _init_l_Lean_IR_ToIR_lowerLet___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__7);
l_Lean_IR_ToIR_lowerLet___closed__8 = _init_l_Lean_IR_ToIR_lowerLet___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__8);
l_Lean_IR_ToIR_lowerLet___closed__9 = _init_l_Lean_IR_ToIR_lowerLet___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__9);
l_Lean_IR_ToIR_lowerLet___closed__10 = _init_l_Lean_IR_ToIR_lowerLet___closed__10();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__10);
l_Lean_IR_ToIR_lowerLet___closed__11 = _init_l_Lean_IR_ToIR_lowerLet___closed__11();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__11);
l_Lean_IR_ToIR_lowerLet___closed__12 = _init_l_Lean_IR_ToIR_lowerLet___closed__12();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__12);
l_Lean_IR_ToIR_lowerLet___closed__13 = _init_l_Lean_IR_ToIR_lowerLet___closed__13();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__13);
l_Lean_IR_ToIR_lowerLet___closed__14 = _init_l_Lean_IR_ToIR_lowerLet___closed__14();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__14);
l_Lean_IR_ToIR_lowerLet___closed__15 = _init_l_Lean_IR_ToIR_lowerLet___closed__15();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__15);
l_Lean_IR_ToIR_lowerLet___closed__16 = _init_l_Lean_IR_ToIR_lowerLet___closed__16();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__16);
l_Lean_IR_ToIR_lowerLet___closed__17 = _init_l_Lean_IR_ToIR_lowerLet___closed__17();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__17);
l_Lean_IR_ToIR_lowerLet___closed__18 = _init_l_Lean_IR_ToIR_lowerLet___closed__18();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__18);
l_Lean_IR_ToIR_lowerLet___closed__19 = _init_l_Lean_IR_ToIR_lowerLet___closed__19();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__19);
l_Lean_IR_ToIR_lowerLet___closed__20 = _init_l_Lean_IR_ToIR_lowerLet___closed__20();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__20);
l_Lean_IR_ToIR_lowerLet___closed__21 = _init_l_Lean_IR_ToIR_lowerLet___closed__21();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__21);
l_Lean_IR_ToIR_lowerLet___closed__22 = _init_l_Lean_IR_ToIR_lowerLet___closed__22();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__22);
l_Lean_IR_ToIR_lowerLet___closed__23 = _init_l_Lean_IR_ToIR_lowerLet___closed__23();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__23);
l_Lean_IR_ToIR_lowerLet___closed__24 = _init_l_Lean_IR_ToIR_lowerLet___closed__24();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__24);
l_Lean_IR_ToIR_lowerLet___closed__25 = _init_l_Lean_IR_ToIR_lowerLet___closed__25();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__25);
l_Lean_IR_ToIR_lowerLet___closed__26 = _init_l_Lean_IR_ToIR_lowerLet___closed__26();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__26);
l_Lean_IR_ToIR_lowerLet___closed__27 = _init_l_Lean_IR_ToIR_lowerLet___closed__27();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__27);
l_Lean_IR_ToIR_lowerLet___closed__28 = _init_l_Lean_IR_ToIR_lowerLet___closed__28();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__28);
l_Lean_IR_ToIR_lowerLet___closed__29 = _init_l_Lean_IR_ToIR_lowerLet___closed__29();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__29);
l_Lean_IR_ToIR_lowerLet___closed__30 = _init_l_Lean_IR_ToIR_lowerLet___closed__30();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__30);
l_Lean_IR_ToIR_lowerLet___closed__31 = _init_l_Lean_IR_ToIR_lowerLet___closed__31();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__31);
l_Lean_IR_ToIR_lowerLet___closed__32 = _init_l_Lean_IR_ToIR_lowerLet___closed__32();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__32);
l_Lean_IR_ToIR_lowerLet___closed__33 = _init_l_Lean_IR_ToIR_lowerLet___closed__33();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__33);
l_Lean_IR_ToIR_lowerLet___closed__34 = _init_l_Lean_IR_ToIR_lowerLet___closed__34();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__34);
l_Lean_IR_ToIR_lowerLet___closed__35 = _init_l_Lean_IR_ToIR_lowerLet___closed__35();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__35);
l_Lean_IR_ToIR_lowerLet___closed__36 = _init_l_Lean_IR_ToIR_lowerLet___closed__36();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__36);
l_Lean_IR_ToIR_lowerLet___closed__37 = _init_l_Lean_IR_ToIR_lowerLet___closed__37();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__37);
l_Lean_IR_ToIR_lowerLet___closed__38 = _init_l_Lean_IR_ToIR_lowerLet___closed__38();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__38);
l_Lean_IR_ToIR_lowerLet___closed__39 = _init_l_Lean_IR_ToIR_lowerLet___closed__39();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__39);
l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0 = _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0);
l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1 = _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1);
l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2 = _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2);
l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3 = _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3);
l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4 = _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4);
l_Lean_IR_toIR___closed__0 = _init_l_Lean_IR_toIR___closed__0();
lean_mark_persistent(l_Lean_IR_toIR___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
