// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM Lean.Compiler.IR.ToIRType Lean.CoreM Lean.Environment
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
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__5;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__0;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__0;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Environment_addExtraName(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__3;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__15;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__19;
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__13;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__2;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__3;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__14;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__6;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__18;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__7;
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__2;
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__3;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__0;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__8;
static lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getCtorLayout(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__17;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__9;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIR___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__20;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
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
x_8 = l_Lean_IR_findEnvDecl(x_7, x_1);
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
x_12 = l_Lean_IR_findEnvDecl(x_11, x_1);
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
static lean_object* _init_l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__0;
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
x_17 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1;
x_18 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2;
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
x_34 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1;
x_35 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2;
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
x_54 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1;
x_55 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2;
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
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerArg", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected value", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(81u);
x_4 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
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
x_29 = l_Lean_IR_ToIR_lowerArg___closed__3;
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
x_35 = l_Lean_IR_ToIR_lowerArg___closed__3;
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
x_55 = l_Lean_IR_ToIR_lowerArg___closed__3;
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
x_62 = l_Lean_IR_ToIR_lowerArg___closed__3;
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
x_12 = l_Lean_IR_toIRType(x_7, x_3, x_4, x_11);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerParam(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__0;
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
x_17 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1;
x_18 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2;
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
x_26 = l_Lean_IR_instInhabitedFnBody;
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
x_34 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1;
x_35 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2;
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
x_44 = l_Lean_IR_instInhabitedFnBody;
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
x_54 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1;
x_55 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2;
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
x_65 = l_Lean_IR_instInhabitedFnBody;
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
x_3 = lean_unsigned_to_nat(268u);
x_4 = l_Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
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
x_1 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(123u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(115u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
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
x_3 = lean_unsigned_to_nat(131u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(128u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
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
x_133 = lean_ctor_get(x_125, 2);
x_134 = lean_ctor_get(x_125, 3);
x_135 = lean_ctor_get(x_125, 1);
lean_dec(x_135);
x_136 = lean_array_get_size(x_130);
x_137 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_133);
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
x_150 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_133, x_149);
lean_dec(x_149);
lean_dec(x_133);
if (lean_obj_tag(x_150) == 0)
{
lean_free_object(x_125);
lean_dec(x_134);
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
lean_inc(x_132);
x_153 = l_Lean_IR_nameToIRType(x_132, x_3, x_4, x_129);
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
x_157 = lean_array_size(x_134);
x_158 = 0;
x_159 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_156, x_157, x_158, x_134, x_2, x_3, x_4, x_155);
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
lean_dec(x_134);
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
lean_dec(x_134);
lean_dec(x_132);
x_173 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_174 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_173, x_2, x_3, x_4, x_129);
return x_174;
}
default: 
{
lean_free_object(x_125);
lean_dec(x_134);
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
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; size_t x_186; size_t x_187; size_t x_188; size_t x_189; size_t x_190; lean_object* x_191; lean_object* x_192; 
x_175 = lean_ctor_get(x_125, 0);
x_176 = lean_ctor_get(x_125, 2);
x_177 = lean_ctor_get(x_125, 3);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_125);
x_178 = lean_array_get_size(x_130);
x_179 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_176);
x_180 = 32;
x_181 = lean_uint64_shift_right(x_179, x_180);
x_182 = lean_uint64_xor(x_179, x_181);
x_183 = 16;
x_184 = lean_uint64_shift_right(x_182, x_183);
x_185 = lean_uint64_xor(x_182, x_184);
x_186 = lean_uint64_to_usize(x_185);
x_187 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_188 = 1;
x_189 = lean_usize_sub(x_187, x_188);
x_190 = lean_usize_land(x_186, x_189);
x_191 = lean_array_uget(x_130, x_190);
lean_dec(x_130);
x_192 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_176, x_191);
lean_dec(x_191);
lean_dec(x_176);
if (lean_obj_tag(x_192) == 0)
{
lean_dec(x_177);
lean_dec(x_175);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_129;
goto block_12;
}
else
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
switch (lean_obj_tag(x_193)) {
case 0:
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_175);
x_195 = l_Lean_IR_nameToIRType(x_175, x_3, x_4, x_129);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; size_t x_199; size_t x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
lean_inc(x_194);
x_198 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerAlt), 6, 1);
lean_closure_set(x_198, 0, x_194);
x_199 = lean_array_size(x_177);
x_200 = 0;
x_201 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_198, x_199, x_200, x_177, x_2, x_3, x_4, x_197);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
x_205 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_205, 0, x_175);
lean_ctor_set(x_205, 1, x_194);
lean_ctor_set(x_205, 2, x_196);
lean_ctor_set(x_205, 3, x_202);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_196);
lean_dec(x_194);
lean_dec(x_175);
x_207 = lean_ctor_get(x_201, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_209 = x_201;
} else {
 lean_dec_ref(x_201);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_194);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_211 = lean_ctor_get(x_195, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_195, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_213 = x_195;
} else {
 lean_dec_ref(x_195);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
case 1:
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_193);
lean_dec(x_177);
lean_dec(x_175);
x_215 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_216 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_215, x_2, x_3, x_4, x_129);
return x_216;
}
default: 
{
lean_dec(x_177);
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
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; size_t x_237; size_t x_238; size_t x_239; size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_4);
lean_dec(x_3);
x_217 = lean_ctor_get(x_1, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_218 = x_1;
} else {
 lean_dec_ref(x_1);
 x_218 = lean_box(0);
}
x_219 = lean_st_ref_get(x_2, x_5);
lean_dec(x_2);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_227 = lean_ctor_get(x_220, 0);
lean_inc(x_227);
lean_dec(x_220);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_array_get_size(x_228);
x_230 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_217);
x_231 = 32;
x_232 = lean_uint64_shift_right(x_230, x_231);
x_233 = lean_uint64_xor(x_230, x_232);
x_234 = 16;
x_235 = lean_uint64_shift_right(x_233, x_234);
x_236 = lean_uint64_xor(x_233, x_235);
x_237 = lean_uint64_to_usize(x_236);
x_238 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_239 = 1;
x_240 = lean_usize_sub(x_238, x_239);
x_241 = lean_usize_land(x_237, x_240);
x_242 = lean_array_uget(x_228, x_241);
lean_dec(x_228);
x_243 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_217, x_242);
lean_dec(x_242);
lean_dec(x_217);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_245 = l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(x_244);
x_223 = x_245;
goto block_226;
}
else
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
lean_dec(x_243);
switch (lean_obj_tag(x_246)) {
case 0:
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
x_223 = x_246;
goto block_226;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_223 = x_249;
goto block_226;
}
}
case 1:
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_246);
x_250 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_251 = l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(x_250);
x_223 = x_251;
goto block_226;
}
default: 
{
lean_object* x_252; 
x_252 = lean_box(1);
x_223 = x_252;
goto block_226;
}
}
}
block_226:
{
lean_object* x_224; lean_object* x_225; 
if (lean_is_scalar(x_218)) {
 x_224 = lean_alloc_ctor(11, 1, 0);
} else {
 x_224 = x_218;
 lean_ctor_set_tag(x_224, 11);
}
lean_ctor_set(x_224, 0, x_223);
if (lean_is_scalar(x_222)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_222;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_221);
return x_225;
}
}
default: 
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_box(13);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_5);
return x_254;
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
x_10 = l_Lean_IR_getCtorLayout(x_7, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_15; 
x_15 = lean_array_fget(x_1, x_5);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_16 = l_Lean_IR_instInhabitedArg;
x_17 = lean_array_get(x_16, x_2, x_5);
x_18 = lean_array_push(x_4, x_17);
x_7 = x_18;
x_8 = x_6;
goto block_14;
}
else
{
lean_dec(x_15);
x_7 = x_4;
x_8 = x_6;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_11 = lean_nat_dec_lt(x_10, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
x_4 = x_7;
x_5 = x_10;
x_6 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1, x_2, x_7, x_9, x_10, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_MessageData_tagWithErrorName(x_2, x_1);
x_8 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_7, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
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
x_1 = lean_mk_string_unchecked("projection of non-structure type", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(141u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(154u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
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
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(204u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: type == .object\n      ", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(170u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
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
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dependsOnNoncomputable", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(211u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_IR_ToIR_lowerLitValue(x_16);
lean_ctor_set_tag(x_14, 11);
lean_ctor_set(x_14, 0, x_17);
x_18 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_14, x_3, x_4, x_5, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_IR_ToIR_lowerLitValue(x_19);
x_21 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_21, x_3, x_4, x_5, x_6);
return x_22;
}
}
case 1:
{
lean_object* x_23; 
x_23 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_23;
}
case 2:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 3);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 2);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_st_ref_get(x_3, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_get_size(x_36);
x_38 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_31);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_36, x_49);
lean_dec(x_36);
x_51 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_31, x_50);
lean_dec(x_50);
lean_dec(x_31);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_2);
x_52 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_53 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_52, x_3, x_4, x_5, x_35);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
switch (lean_obj_tag(x_54)) {
case 0:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_get(x_5, x_35);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = 0;
x_61 = l_Lean_Environment_find_x3f(x_59, x_29, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_55);
lean_dec(x_30);
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_58;
goto block_13;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 5)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 4);
lean_inc(x_64);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_dec(x_55);
lean_dec(x_30);
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_58;
goto block_13;
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_5);
lean_inc(x_4);
x_67 = l_Lean_IR_getCtorLayout(x_66, x_4, x_5, x_58);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_box(0);
x_73 = lean_array_get(x_72, x_71, x_30);
lean_dec(x_30);
lean_dec(x_71);
x_74 = l_Lean_IR_ToIR_lowerProj(x_55, x_70, x_73);
lean_dec(x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_IR_ToIR_bindVar___redArg(x_25, x_3, x_69);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_80);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_77);
lean_ctor_set(x_1, 1, x_76);
lean_ctor_set(x_1, 0, x_79);
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_81, 0);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_81);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set(x_1, 2, x_77);
lean_ctor_set(x_1, 1, x_76);
lean_ctor_set(x_1, 0, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_free_object(x_1);
return x_81;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_74);
lean_free_object(x_1);
x_87 = l_Lean_IR_ToIR_bindErased___redArg(x_25, x_3, x_69);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_88);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_55);
lean_dec(x_30);
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_67);
if (x_90 == 0)
{
return x_67;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_67, 0);
x_92 = lean_ctor_get(x_67, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_67);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_30);
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_58;
goto block_13;
}
}
}
else
{
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_30);
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_58;
goto block_13;
}
}
}
case 1:
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_54);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_2);
x_94 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_95 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_94, x_3, x_4, x_5, x_35);
return x_95;
}
default: 
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_1);
x_96 = l_Lean_IR_ToIR_bindErased___redArg(x_25, x_3, x_35);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
lean_dec(x_1);
x_100 = lean_ctor_get(x_14, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_14, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_14, 2);
lean_inc(x_102);
lean_dec(x_14);
x_103 = lean_st_ref_get(x_3, x_6);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_array_get_size(x_107);
x_109 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_102);
x_110 = 32;
x_111 = lean_uint64_shift_right(x_109, x_110);
x_112 = lean_uint64_xor(x_109, x_111);
x_113 = 16;
x_114 = lean_uint64_shift_right(x_112, x_113);
x_115 = lean_uint64_xor(x_112, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_118 = 1;
x_119 = lean_usize_sub(x_117, x_118);
x_120 = lean_usize_land(x_116, x_119);
x_121 = lean_array_uget(x_107, x_120);
lean_dec(x_107);
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_2);
x_123 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_124 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_123, x_3, x_4, x_5, x_106);
return x_124;
}
else
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
switch (lean_obj_tag(x_125)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_5, x_106);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = 0;
x_132 = l_Lean_Environment_find_x3f(x_130, x_100, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_dec(x_126);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_129;
goto block_13;
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 5)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_ctor_get(x_134, 4);
lean_inc(x_135);
lean_dec(x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_dec(x_126);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_129;
goto block_13;
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_5);
lean_inc(x_4);
x_138 = l_Lean_IR_getCtorLayout(x_137, x_4, x_5, x_129);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_box(0);
x_144 = lean_array_get(x_143, x_142, x_101);
lean_dec(x_101);
lean_dec(x_142);
x_145 = l_Lean_IR_ToIR_lowerProj(x_126, x_141, x_144);
lean_dec(x_141);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_IR_ToIR_bindVar___redArg(x_99, x_3, x_140);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_156, 0, x_150);
lean_ctor_set(x_156, 1, x_147);
lean_ctor_set(x_156, 2, x_148);
lean_ctor_set(x_156, 3, x_153);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
else
{
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_147);
return x_152;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_145);
x_158 = l_Lean_IR_ToIR_bindErased___redArg(x_99, x_3, x_140);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_159);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_126);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_ctor_get(x_138, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_138, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_163 = x_138;
} else {
 lean_dec_ref(x_138);
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
else
{
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_126);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_129;
goto block_13;
}
}
}
else
{
lean_dec(x_133);
lean_dec(x_126);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_129;
goto block_13;
}
}
}
case 1:
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_125);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_2);
x_165 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_166 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_165, x_3, x_4, x_5, x_106);
return x_166;
}
default: 
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_101);
lean_dec(x_100);
x_167 = l_Lean_IR_ToIR_bindErased___redArg(x_99, x_3, x_106);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_168);
return x_169;
}
}
}
}
}
case 3:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; 
x_170 = lean_ctor_get(x_1, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_14, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_14, 2);
lean_inc(x_172);
lean_dec(x_14);
x_173 = lean_array_size(x_172);
x_174 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_175 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_173, x_174, x_172, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_176);
lean_inc(x_171);
lean_inc(x_2);
lean_inc(x_1);
x_178 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_171, x_176, x_3, x_4, x_5, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_st_ref_get(x_5, x_180);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_181, 0);
x_184 = lean_ctor_get(x_181, 1);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
lean_dec(x_183);
x_186 = 0;
lean_inc(x_171);
lean_inc(x_185);
x_187 = l_Lean_Environment_find_x3f(x_185, x_171, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_185);
lean_free_object(x_181);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
lean_dec(x_1);
x_188 = l_Lean_IR_ToIR_lowerLet___closed__5;
x_189 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_188, x_3, x_4, x_5, x_184);
return x_189;
}
else
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
switch (lean_obj_tag(x_191)) {
case 1:
{
lean_object* x_192; 
lean_free_object(x_187);
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_170);
lean_ctor_set_tag(x_181, 6);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 0, x_171);
x_192 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_184);
return x_192;
}
case 3:
{
lean_object* x_193; 
lean_free_object(x_187);
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_170);
lean_ctor_set_tag(x_181, 6);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 0, x_171);
x_193 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_184);
return x_193;
}
case 6:
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_191);
if (x_194 == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_191, 0);
lean_inc(x_171);
x_196 = l_Lean_isExtern(x_185, x_171);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_free_object(x_181);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_197 = x_1;
} else {
 lean_dec_ref(x_1);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 3);
lean_inc(x_200);
lean_dec(x_195);
lean_inc(x_5);
lean_inc(x_4);
x_201 = l_Lean_IR_nameToIRType(x_198, x_4, x_5, x_184);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_Lean_IR_IRType_isScalar(x_202);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
lean_dec(x_199);
lean_free_object(x_191);
lean_free_object(x_187);
x_205 = lean_box(7);
x_206 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_202, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_197);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
x_207 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_208 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_207, x_3, x_4, x_5, x_203);
return x_208;
}
else
{
lean_object* x_209; 
lean_inc(x_5);
lean_inc(x_4);
x_209 = l_Lean_IR_getCtorLayout(x_171, x_4, x_5, x_203);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_242; uint8_t x_243; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_array_get_size(x_213);
x_215 = lean_unsigned_to_nat(0u);
x_216 = lean_array_get_size(x_176);
x_217 = l_Array_extract___redArg(x_176, x_200, x_216);
lean_dec(x_176);
x_242 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_243 = lean_nat_dec_lt(x_215, x_214);
if (x_243 == 0)
{
lean_dec(x_214);
x_218 = x_242;
x_219 = x_211;
goto block_241;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_213, x_217, x_214, x_242, x_215, x_211);
lean_dec(x_214);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_218 = x_245;
x_219 = x_246;
goto block_241;
}
block_241:
{
lean_object* x_220; uint8_t x_221; 
x_220 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_219);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
x_224 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_212, x_213, x_217, x_222, x_3, x_4, x_5, x_223);
lean_dec(x_217);
lean_dec(x_213);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_224, 0);
lean_ctor_set(x_220, 1, x_218);
lean_ctor_set(x_220, 0, x_212);
if (lean_is_scalar(x_197)) {
 x_227 = lean_alloc_ctor(0, 4, 0);
} else {
 x_227 = x_197;
}
lean_ctor_set(x_227, 0, x_222);
lean_ctor_set(x_227, 1, x_202);
lean_ctor_set(x_227, 2, x_220);
lean_ctor_set(x_227, 3, x_226);
lean_ctor_set(x_224, 0, x_227);
return x_224;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_224, 0);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_224);
lean_ctor_set(x_220, 1, x_218);
lean_ctor_set(x_220, 0, x_212);
if (lean_is_scalar(x_197)) {
 x_230 = lean_alloc_ctor(0, 4, 0);
} else {
 x_230 = x_197;
}
lean_ctor_set(x_230, 0, x_222);
lean_ctor_set(x_230, 1, x_202);
lean_ctor_set(x_230, 2, x_220);
lean_ctor_set(x_230, 3, x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_free_object(x_220);
lean_dec(x_222);
lean_dec(x_218);
lean_dec(x_212);
lean_dec(x_202);
lean_dec(x_197);
return x_224;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_220, 0);
x_233 = lean_ctor_get(x_220, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_220);
lean_inc(x_232);
x_234 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_212, x_213, x_217, x_232, x_3, x_4, x_5, x_233);
lean_dec(x_217);
lean_dec(x_213);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_212);
lean_ctor_set(x_238, 1, x_218);
if (lean_is_scalar(x_197)) {
 x_239 = lean_alloc_ctor(0, 4, 0);
} else {
 x_239 = x_197;
}
lean_ctor_set(x_239, 0, x_232);
lean_ctor_set(x_239, 1, x_202);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_235);
if (lean_is_scalar(x_237)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_237;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_236);
return x_240;
}
else
{
lean_dec(x_232);
lean_dec(x_218);
lean_dec(x_212);
lean_dec(x_202);
lean_dec(x_197);
return x_234;
}
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_197);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_247 = !lean_is_exclusive(x_209);
if (x_247 == 0)
{
return x_209;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_209, 0);
x_249 = lean_ctor_get(x_209, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_209);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_200);
lean_dec(x_176);
lean_dec(x_171);
x_251 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_203);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_253);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_254, 0);
lean_ctor_set_tag(x_191, 0);
lean_ctor_set(x_191, 0, x_199);
lean_ctor_set_tag(x_187, 11);
if (lean_is_scalar(x_197)) {
 x_257 = lean_alloc_ctor(0, 4, 0);
} else {
 x_257 = x_197;
}
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_202);
lean_ctor_set(x_257, 2, x_187);
lean_ctor_set(x_257, 3, x_256);
lean_ctor_set(x_254, 0, x_257);
return x_254;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_254, 0);
x_259 = lean_ctor_get(x_254, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_254);
lean_ctor_set_tag(x_191, 0);
lean_ctor_set(x_191, 0, x_199);
lean_ctor_set_tag(x_187, 11);
if (lean_is_scalar(x_197)) {
 x_260 = lean_alloc_ctor(0, 4, 0);
} else {
 x_260 = x_197;
}
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_202);
lean_ctor_set(x_260, 2, x_187);
lean_ctor_set(x_260, 3, x_258);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_dec(x_252);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_free_object(x_191);
lean_free_object(x_187);
return x_254;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_197);
lean_free_object(x_191);
lean_free_object(x_187);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_262 = !lean_is_exclusive(x_201);
if (x_262 == 0)
{
return x_201;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_201, 0);
x_264 = lean_ctor_get(x_201, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_201);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
lean_object* x_266; 
lean_free_object(x_191);
lean_dec(x_195);
lean_free_object(x_187);
lean_dec(x_170);
lean_ctor_set_tag(x_181, 6);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 0, x_171);
x_266 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_184);
return x_266;
}
}
else
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_191, 0);
lean_inc(x_267);
lean_dec(x_191);
lean_inc(x_171);
x_268 = l_Lean_isExtern(x_185, x_171);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_free_object(x_181);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_269 = x_1;
} else {
 lean_dec_ref(x_1);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_267, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_267, 3);
lean_inc(x_272);
lean_dec(x_267);
lean_inc(x_5);
lean_inc(x_4);
x_273 = l_Lean_IR_nameToIRType(x_270, x_4, x_5, x_184);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_IR_IRType_isScalar(x_274);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
lean_dec(x_271);
lean_free_object(x_187);
x_277 = lean_box(7);
x_278 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_274, x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_274);
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
x_279 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_280 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_279, x_3, x_4, x_5, x_275);
return x_280;
}
else
{
lean_object* x_281; 
lean_inc(x_5);
lean_inc(x_4);
x_281 = l_Lean_IR_getCtorLayout(x_171, x_4, x_5, x_275);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_304; uint8_t x_305; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_286 = lean_array_get_size(x_285);
x_287 = lean_unsigned_to_nat(0u);
x_288 = lean_array_get_size(x_176);
x_289 = l_Array_extract___redArg(x_176, x_272, x_288);
lean_dec(x_176);
x_304 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_305 = lean_nat_dec_lt(x_287, x_286);
if (x_305 == 0)
{
lean_dec(x_286);
x_290 = x_304;
x_291 = x_283;
goto block_303;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_285, x_289, x_286, x_304, x_287, x_283);
lean_dec(x_286);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_290 = x_307;
x_291 = x_308;
goto block_303;
}
block_303:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_291);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
lean_inc(x_293);
x_296 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_284, x_285, x_289, x_293, x_3, x_4, x_5, x_294);
lean_dec(x_289);
lean_dec(x_285);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_299 = x_296;
} else {
 lean_dec_ref(x_296);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_295;
}
lean_ctor_set(x_300, 0, x_284);
lean_ctor_set(x_300, 1, x_290);
if (lean_is_scalar(x_269)) {
 x_301 = lean_alloc_ctor(0, 4, 0);
} else {
 x_301 = x_269;
}
lean_ctor_set(x_301, 0, x_293);
lean_ctor_set(x_301, 1, x_274);
lean_ctor_set(x_301, 2, x_300);
lean_ctor_set(x_301, 3, x_297);
if (lean_is_scalar(x_299)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_299;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_298);
return x_302;
}
else
{
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_290);
lean_dec(x_284);
lean_dec(x_274);
lean_dec(x_269);
return x_296;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_274);
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_309 = lean_ctor_get(x_281, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_281, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_311 = x_281;
} else {
 lean_dec_ref(x_281);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_272);
lean_dec(x_176);
lean_dec(x_171);
x_313 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_275);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_315);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_319 = x_316;
} else {
 lean_dec_ref(x_316);
 x_319 = lean_box(0);
}
x_320 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_320, 0, x_271);
lean_ctor_set_tag(x_187, 11);
lean_ctor_set(x_187, 0, x_320);
if (lean_is_scalar(x_269)) {
 x_321 = lean_alloc_ctor(0, 4, 0);
} else {
 x_321 = x_269;
}
lean_ctor_set(x_321, 0, x_314);
lean_ctor_set(x_321, 1, x_274);
lean_ctor_set(x_321, 2, x_187);
lean_ctor_set(x_321, 3, x_317);
if (lean_is_scalar(x_319)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_319;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_318);
return x_322;
}
else
{
lean_dec(x_314);
lean_dec(x_274);
lean_dec(x_271);
lean_dec(x_269);
lean_free_object(x_187);
return x_316;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_free_object(x_187);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_323 = lean_ctor_get(x_273, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_273, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_325 = x_273;
} else {
 lean_dec_ref(x_273);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; 
lean_dec(x_267);
lean_free_object(x_187);
lean_dec(x_170);
lean_ctor_set_tag(x_181, 6);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 0, x_171);
x_327 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_184);
return x_327;
}
}
}
case 7:
{
uint8_t x_328; 
lean_free_object(x_187);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_328 = !lean_is_exclusive(x_191);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_329 = lean_ctor_get(x_191, 0);
lean_dec(x_329);
x_330 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_331 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_332 = 1;
x_333 = l_Lean_Name_toString(x_171, x_332, x_330);
lean_ctor_set_tag(x_191, 3);
lean_ctor_set(x_191, 0, x_333);
lean_ctor_set_tag(x_181, 5);
lean_ctor_set(x_181, 1, x_191);
lean_ctor_set(x_181, 0, x_331);
x_334 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_335 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_335, 0, x_181);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_MessageData_ofFormat(x_335);
x_337 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_336, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_191);
x_338 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_339 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_340 = 1;
x_341 = l_Lean_Name_toString(x_171, x_340, x_338);
x_342 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set_tag(x_181, 5);
lean_ctor_set(x_181, 1, x_342);
lean_ctor_set(x_181, 0, x_339);
x_343 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_344 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_344, 0, x_181);
lean_ctor_set(x_344, 1, x_343);
x_345 = l_Lean_MessageData_ofFormat(x_344);
x_346 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_345, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
return x_346;
}
}
default: 
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_347 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_348 = l_Lean_IR_ToIR_lowerLet___closed__15;
x_349 = l_Lean_IR_ToIR_lowerLet___closed__17;
x_350 = 1;
x_351 = l_Lean_Name_toString(x_171, x_350, x_347);
lean_ctor_set_tag(x_187, 3);
lean_ctor_set(x_187, 0, x_351);
lean_ctor_set_tag(x_181, 5);
lean_ctor_set(x_181, 1, x_187);
lean_ctor_set(x_181, 0, x_349);
x_352 = l_Lean_IR_ToIR_lowerLet___closed__19;
x_353 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_353, 0, x_181);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_MessageData_ofFormat(x_353);
x_355 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_348, x_354, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
return x_355;
}
}
}
else
{
lean_object* x_356; 
x_356 = lean_ctor_get(x_187, 0);
lean_inc(x_356);
lean_dec(x_187);
switch (lean_obj_tag(x_356)) {
case 1:
{
lean_object* x_357; 
lean_dec(x_356);
lean_dec(x_185);
lean_dec(x_170);
lean_ctor_set_tag(x_181, 6);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 0, x_171);
x_357 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_184);
return x_357;
}
case 3:
{
lean_object* x_358; 
lean_dec(x_356);
lean_dec(x_185);
lean_dec(x_170);
lean_ctor_set_tag(x_181, 6);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 0, x_171);
x_358 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_184);
return x_358;
}
case 6:
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; 
x_359 = lean_ctor_get(x_356, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 x_360 = x_356;
} else {
 lean_dec_ref(x_356);
 x_360 = lean_box(0);
}
lean_inc(x_171);
x_361 = l_Lean_isExtern(x_185, x_171);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_free_object(x_181);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_362 = x_1;
} else {
 lean_dec_ref(x_1);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_359, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_359, 3);
lean_inc(x_365);
lean_dec(x_359);
lean_inc(x_5);
lean_inc(x_4);
x_366 = l_Lean_IR_nameToIRType(x_363, x_4, x_5, x_184);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = l_Lean_IR_IRType_isScalar(x_367);
if (x_369 == 0)
{
lean_object* x_370; uint8_t x_371; 
lean_dec(x_364);
lean_dec(x_360);
x_370 = lean_box(7);
x_371 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_367, x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_367);
lean_dec(x_365);
lean_dec(x_362);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
x_372 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_373 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_372, x_3, x_4, x_5, x_368);
return x_373;
}
else
{
lean_object* x_374; 
lean_inc(x_5);
lean_inc(x_4);
x_374 = l_Lean_IR_getCtorLayout(x_171, x_4, x_5, x_368);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_397; uint8_t x_398; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_377 = lean_ctor_get(x_375, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
lean_dec(x_375);
x_379 = lean_array_get_size(x_378);
x_380 = lean_unsigned_to_nat(0u);
x_381 = lean_array_get_size(x_176);
x_382 = l_Array_extract___redArg(x_176, x_365, x_381);
lean_dec(x_176);
x_397 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_398 = lean_nat_dec_lt(x_380, x_379);
if (x_398 == 0)
{
lean_dec(x_379);
x_383 = x_397;
x_384 = x_376;
goto block_396;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_378, x_382, x_379, x_397, x_380, x_376);
lean_dec(x_379);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_383 = x_400;
x_384 = x_401;
goto block_396;
}
block_396:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_385 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_384);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_388 = x_385;
} else {
 lean_dec_ref(x_385);
 x_388 = lean_box(0);
}
lean_inc(x_386);
x_389 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_377, x_378, x_382, x_386, x_3, x_4, x_5, x_387);
lean_dec(x_382);
lean_dec(x_378);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_388;
}
lean_ctor_set(x_393, 0, x_377);
lean_ctor_set(x_393, 1, x_383);
if (lean_is_scalar(x_362)) {
 x_394 = lean_alloc_ctor(0, 4, 0);
} else {
 x_394 = x_362;
}
lean_ctor_set(x_394, 0, x_386);
lean_ctor_set(x_394, 1, x_367);
lean_ctor_set(x_394, 2, x_393);
lean_ctor_set(x_394, 3, x_390);
if (lean_is_scalar(x_392)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_392;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_391);
return x_395;
}
else
{
lean_dec(x_388);
lean_dec(x_386);
lean_dec(x_383);
lean_dec(x_377);
lean_dec(x_367);
lean_dec(x_362);
return x_389;
}
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_367);
lean_dec(x_365);
lean_dec(x_362);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_402 = lean_ctor_get(x_374, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_374, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_404 = x_374;
} else {
 lean_dec_ref(x_374);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_403);
return x_405;
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_365);
lean_dec(x_176);
lean_dec(x_171);
x_406 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_368);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_408);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_413 = lean_alloc_ctor(0, 1, 0);
} else {
 x_413 = x_360;
 lean_ctor_set_tag(x_413, 0);
}
lean_ctor_set(x_413, 0, x_364);
x_414 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_414, 0, x_413);
if (lean_is_scalar(x_362)) {
 x_415 = lean_alloc_ctor(0, 4, 0);
} else {
 x_415 = x_362;
}
lean_ctor_set(x_415, 0, x_407);
lean_ctor_set(x_415, 1, x_367);
lean_ctor_set(x_415, 2, x_414);
lean_ctor_set(x_415, 3, x_410);
if (lean_is_scalar(x_412)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_412;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_411);
return x_416;
}
else
{
lean_dec(x_407);
lean_dec(x_367);
lean_dec(x_364);
lean_dec(x_362);
lean_dec(x_360);
return x_409;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_365);
lean_dec(x_364);
lean_dec(x_362);
lean_dec(x_360);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_417 = lean_ctor_get(x_366, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_366, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_419 = x_366;
} else {
 lean_dec_ref(x_366);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
else
{
lean_object* x_421; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_170);
lean_ctor_set_tag(x_181, 6);
lean_ctor_set(x_181, 1, x_176);
lean_ctor_set(x_181, 0, x_171);
x_421 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_184);
return x_421;
}
}
case 7:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 x_422 = x_356;
} else {
 lean_dec_ref(x_356);
 x_422 = lean_box(0);
}
x_423 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_424 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_425 = 1;
x_426 = l_Lean_Name_toString(x_171, x_425, x_423);
if (lean_is_scalar(x_422)) {
 x_427 = lean_alloc_ctor(3, 1, 0);
} else {
 x_427 = x_422;
 lean_ctor_set_tag(x_427, 3);
}
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set_tag(x_181, 5);
lean_ctor_set(x_181, 1, x_427);
lean_ctor_set(x_181, 0, x_424);
x_428 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_429 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_429, 0, x_181);
lean_ctor_set(x_429, 1, x_428);
x_430 = l_Lean_MessageData_ofFormat(x_429);
x_431 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_430, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
return x_431;
}
default: 
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_356);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_432 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_433 = l_Lean_IR_ToIR_lowerLet___closed__15;
x_434 = l_Lean_IR_ToIR_lowerLet___closed__17;
x_435 = 1;
x_436 = l_Lean_Name_toString(x_171, x_435, x_432);
x_437 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set_tag(x_181, 5);
lean_ctor_set(x_181, 1, x_437);
lean_ctor_set(x_181, 0, x_434);
x_438 = l_Lean_IR_ToIR_lowerLet___closed__19;
x_439 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_439, 0, x_181);
lean_ctor_set(x_439, 1, x_438);
x_440 = l_Lean_MessageData_ofFormat(x_439);
x_441 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_433, x_440, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
return x_441;
}
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; 
x_442 = lean_ctor_get(x_181, 0);
x_443 = lean_ctor_get(x_181, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_181);
x_444 = lean_ctor_get(x_442, 0);
lean_inc(x_444);
lean_dec(x_442);
x_445 = 0;
lean_inc(x_171);
lean_inc(x_444);
x_446 = l_Lean_Environment_find_x3f(x_444, x_171, x_445);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_444);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
lean_dec(x_1);
x_447 = l_Lean_IR_ToIR_lowerLet___closed__5;
x_448 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_447, x_3, x_4, x_5, x_443);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_446, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_450 = x_446;
} else {
 lean_dec_ref(x_446);
 x_450 = lean_box(0);
}
switch (lean_obj_tag(x_449)) {
case 1:
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_170);
x_451 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_451, 0, x_171);
lean_ctor_set(x_451, 1, x_176);
x_452 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_451, x_3, x_4, x_5, x_443);
return x_452;
}
case 3:
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_170);
x_453 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_453, 0, x_171);
lean_ctor_set(x_453, 1, x_176);
x_454 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_453, x_3, x_4, x_5, x_443);
return x_454;
}
case 6:
{
lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_455 = lean_ctor_get(x_449, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 x_456 = x_449;
} else {
 lean_dec_ref(x_449);
 x_456 = lean_box(0);
}
lean_inc(x_171);
x_457 = l_Lean_isExtern(x_444, x_171);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_458 = x_1;
} else {
 lean_dec_ref(x_1);
 x_458 = lean_box(0);
}
x_459 = lean_ctor_get(x_455, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_455, 2);
lean_inc(x_460);
x_461 = lean_ctor_get(x_455, 3);
lean_inc(x_461);
lean_dec(x_455);
lean_inc(x_5);
lean_inc(x_4);
x_462 = l_Lean_IR_nameToIRType(x_459, x_4, x_5, x_443);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; uint8_t x_465; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = l_Lean_IR_IRType_isScalar(x_463);
if (x_465 == 0)
{
lean_object* x_466; uint8_t x_467; 
lean_dec(x_460);
lean_dec(x_456);
lean_dec(x_450);
x_466 = lean_box(7);
x_467 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_463, x_466);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_458);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
x_468 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_469 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_468, x_3, x_4, x_5, x_464);
return x_469;
}
else
{
lean_object* x_470; 
lean_inc(x_5);
lean_inc(x_4);
x_470 = l_Lean_IR_getCtorLayout(x_171, x_4, x_5, x_464);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_493; uint8_t x_494; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_ctor_get(x_471, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
lean_dec(x_471);
x_475 = lean_array_get_size(x_474);
x_476 = lean_unsigned_to_nat(0u);
x_477 = lean_array_get_size(x_176);
x_478 = l_Array_extract___redArg(x_176, x_461, x_477);
lean_dec(x_176);
x_493 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_494 = lean_nat_dec_lt(x_476, x_475);
if (x_494 == 0)
{
lean_dec(x_475);
x_479 = x_493;
x_480 = x_472;
goto block_492;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_474, x_478, x_475, x_493, x_476, x_472);
lean_dec(x_475);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_479 = x_496;
x_480 = x_497;
goto block_492;
}
block_492:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_481 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_480);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_484 = x_481;
} else {
 lean_dec_ref(x_481);
 x_484 = lean_box(0);
}
lean_inc(x_482);
x_485 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_473, x_474, x_478, x_482, x_3, x_4, x_5, x_483);
lean_dec(x_478);
lean_dec(x_474);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_488 = x_485;
} else {
 lean_dec_ref(x_485);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_484)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_484;
}
lean_ctor_set(x_489, 0, x_473);
lean_ctor_set(x_489, 1, x_479);
if (lean_is_scalar(x_458)) {
 x_490 = lean_alloc_ctor(0, 4, 0);
} else {
 x_490 = x_458;
}
lean_ctor_set(x_490, 0, x_482);
lean_ctor_set(x_490, 1, x_463);
lean_ctor_set(x_490, 2, x_489);
lean_ctor_set(x_490, 3, x_486);
if (lean_is_scalar(x_488)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_488;
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_487);
return x_491;
}
else
{
lean_dec(x_484);
lean_dec(x_482);
lean_dec(x_479);
lean_dec(x_473);
lean_dec(x_463);
lean_dec(x_458);
return x_485;
}
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_458);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_498 = lean_ctor_get(x_470, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_470, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_500 = x_470;
} else {
 lean_dec_ref(x_470);
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
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_461);
lean_dec(x_176);
lean_dec(x_171);
x_502 = l_Lean_IR_ToIR_bindVar___redArg(x_170, x_3, x_464);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
x_505 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_508 = x_505;
} else {
 lean_dec_ref(x_505);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_509 = lean_alloc_ctor(0, 1, 0);
} else {
 x_509 = x_456;
 lean_ctor_set_tag(x_509, 0);
}
lean_ctor_set(x_509, 0, x_460);
if (lean_is_scalar(x_450)) {
 x_510 = lean_alloc_ctor(11, 1, 0);
} else {
 x_510 = x_450;
 lean_ctor_set_tag(x_510, 11);
}
lean_ctor_set(x_510, 0, x_509);
if (lean_is_scalar(x_458)) {
 x_511 = lean_alloc_ctor(0, 4, 0);
} else {
 x_511 = x_458;
}
lean_ctor_set(x_511, 0, x_503);
lean_ctor_set(x_511, 1, x_463);
lean_ctor_set(x_511, 2, x_510);
lean_ctor_set(x_511, 3, x_506);
if (lean_is_scalar(x_508)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_508;
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_507);
return x_512;
}
else
{
lean_dec(x_503);
lean_dec(x_463);
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_456);
lean_dec(x_450);
return x_505;
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_458);
lean_dec(x_456);
lean_dec(x_450);
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_513 = lean_ctor_get(x_462, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_462, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_515 = x_462;
} else {
 lean_dec_ref(x_462);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
else
{
lean_object* x_517; lean_object* x_518; 
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_450);
lean_dec(x_170);
x_517 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_517, 0, x_171);
lean_ctor_set(x_517, 1, x_176);
x_518 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_517, x_3, x_4, x_5, x_443);
return x_518;
}
}
case 7:
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_450);
lean_dec(x_444);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 x_519 = x_449;
} else {
 lean_dec_ref(x_449);
 x_519 = lean_box(0);
}
x_520 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_521 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_522 = 1;
x_523 = l_Lean_Name_toString(x_171, x_522, x_520);
if (lean_is_scalar(x_519)) {
 x_524 = lean_alloc_ctor(3, 1, 0);
} else {
 x_524 = x_519;
 lean_ctor_set_tag(x_524, 3);
}
lean_ctor_set(x_524, 0, x_523);
x_525 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_525, 0, x_521);
lean_ctor_set(x_525, 1, x_524);
x_526 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_527 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
x_528 = l_Lean_MessageData_ofFormat(x_527);
x_529 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_528, x_4, x_5, x_443);
lean_dec(x_5);
lean_dec(x_4);
return x_529;
}
default: 
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_530 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 1, 0);
x_531 = l_Lean_IR_ToIR_lowerLet___closed__15;
x_532 = l_Lean_IR_ToIR_lowerLet___closed__17;
x_533 = 1;
x_534 = l_Lean_Name_toString(x_171, x_533, x_530);
if (lean_is_scalar(x_450)) {
 x_535 = lean_alloc_ctor(3, 1, 0);
} else {
 x_535 = x_450;
 lean_ctor_set_tag(x_535, 3);
}
lean_ctor_set(x_535, 0, x_534);
x_536 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_536, 0, x_532);
lean_ctor_set(x_536, 1, x_535);
x_537 = l_Lean_IR_ToIR_lowerLet___closed__19;
x_538 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
x_539 = l_Lean_MessageData_ofFormat(x_538);
x_540 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_531, x_539, x_4, x_5, x_443);
lean_dec(x_5);
lean_dec(x_4);
return x_540;
}
}
}
}
}
else
{
uint8_t x_541; 
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_541 = !lean_is_exclusive(x_178);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; 
x_542 = lean_ctor_get(x_178, 0);
lean_dec(x_542);
x_543 = lean_ctor_get(x_179, 0);
lean_inc(x_543);
lean_dec(x_179);
lean_ctor_set(x_178, 0, x_543);
return x_178;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = lean_ctor_get(x_178, 1);
lean_inc(x_544);
lean_dec(x_178);
x_545 = lean_ctor_get(x_179, 0);
lean_inc(x_545);
lean_dec(x_179);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_544);
return x_546;
}
}
}
else
{
uint8_t x_547; 
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_547 = !lean_is_exclusive(x_178);
if (x_547 == 0)
{
return x_178;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_178, 0);
x_549 = lean_ctor_get(x_178, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_178);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
return x_550;
}
}
}
else
{
uint8_t x_551; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_551 = !lean_is_exclusive(x_175);
if (x_551 == 0)
{
return x_175;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_175, 0);
x_553 = lean_ctor_get(x_175, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_175);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
default: 
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_555 = lean_ctor_get(x_14, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_14, 1);
lean_inc(x_556);
lean_dec(x_14);
x_557 = lean_st_ref_get(x_3, x_6);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
lean_dec(x_558);
x_560 = lean_ctor_get(x_557, 1);
lean_inc(x_560);
lean_dec(x_557);
x_561 = !lean_is_exclusive(x_559);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; uint64_t x_565; uint64_t x_566; uint64_t x_567; uint64_t x_568; uint64_t x_569; uint64_t x_570; uint64_t x_571; size_t x_572; size_t x_573; size_t x_574; size_t x_575; size_t x_576; lean_object* x_577; lean_object* x_578; 
x_562 = lean_ctor_get(x_559, 1);
x_563 = lean_ctor_get(x_559, 0);
lean_dec(x_563);
x_564 = lean_array_get_size(x_562);
x_565 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_555);
x_566 = 32;
x_567 = lean_uint64_shift_right(x_565, x_566);
x_568 = lean_uint64_xor(x_565, x_567);
x_569 = 16;
x_570 = lean_uint64_shift_right(x_568, x_569);
x_571 = lean_uint64_xor(x_568, x_570);
x_572 = lean_uint64_to_usize(x_571);
x_573 = lean_usize_of_nat(x_564);
lean_dec(x_564);
x_574 = 1;
x_575 = lean_usize_sub(x_573, x_574);
x_576 = lean_usize_land(x_572, x_575);
x_577 = lean_array_uget(x_562, x_576);
lean_dec(x_562);
x_578 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_555, x_577);
lean_dec(x_577);
lean_dec(x_555);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; 
lean_free_object(x_559);
lean_dec(x_556);
lean_dec(x_2);
lean_dec(x_1);
x_579 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_580 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_579, x_3, x_4, x_5, x_560);
return x_580;
}
else
{
lean_object* x_581; 
x_581 = lean_ctor_get(x_578, 0);
lean_inc(x_581);
lean_dec(x_578);
switch (lean_obj_tag(x_581)) {
case 0:
{
lean_object* x_582; size_t x_583; size_t x_584; lean_object* x_585; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
lean_dec(x_581);
x_583 = lean_array_size(x_556);
x_584 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_585 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_583, x_584, x_556, x_3, x_4, x_5, x_560);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
lean_ctor_set_tag(x_559, 8);
lean_ctor_set(x_559, 1, x_586);
lean_ctor_set(x_559, 0, x_582);
x_588 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_559, x_3, x_4, x_5, x_587);
return x_588;
}
else
{
uint8_t x_589; 
lean_dec(x_582);
lean_free_object(x_559);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_589 = !lean_is_exclusive(x_585);
if (x_589 == 0)
{
return x_585;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_585, 0);
x_591 = lean_ctor_get(x_585, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_585);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
case 1:
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_581);
lean_free_object(x_559);
lean_dec(x_556);
lean_dec(x_2);
lean_dec(x_1);
x_593 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_594 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_593, x_3, x_4, x_5, x_560);
return x_594;
}
default: 
{
lean_object* x_595; 
lean_free_object(x_559);
lean_dec(x_556);
x_595 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_560);
return x_595;
}
}
}
}
else
{
lean_object* x_596; lean_object* x_597; uint64_t x_598; uint64_t x_599; uint64_t x_600; uint64_t x_601; uint64_t x_602; uint64_t x_603; uint64_t x_604; size_t x_605; size_t x_606; size_t x_607; size_t x_608; size_t x_609; lean_object* x_610; lean_object* x_611; 
x_596 = lean_ctor_get(x_559, 1);
lean_inc(x_596);
lean_dec(x_559);
x_597 = lean_array_get_size(x_596);
x_598 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_555);
x_599 = 32;
x_600 = lean_uint64_shift_right(x_598, x_599);
x_601 = lean_uint64_xor(x_598, x_600);
x_602 = 16;
x_603 = lean_uint64_shift_right(x_601, x_602);
x_604 = lean_uint64_xor(x_601, x_603);
x_605 = lean_uint64_to_usize(x_604);
x_606 = lean_usize_of_nat(x_597);
lean_dec(x_597);
x_607 = 1;
x_608 = lean_usize_sub(x_606, x_607);
x_609 = lean_usize_land(x_605, x_608);
x_610 = lean_array_uget(x_596, x_609);
lean_dec(x_596);
x_611 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_555, x_610);
lean_dec(x_610);
lean_dec(x_555);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; 
lean_dec(x_556);
lean_dec(x_2);
lean_dec(x_1);
x_612 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_613 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_612, x_3, x_4, x_5, x_560);
return x_613;
}
else
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_611, 0);
lean_inc(x_614);
lean_dec(x_611);
switch (lean_obj_tag(x_614)) {
case 0:
{
lean_object* x_615; size_t x_616; size_t x_617; lean_object* x_618; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
lean_dec(x_614);
x_616 = lean_array_size(x_556);
x_617 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_618 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_616, x_617, x_556, x_3, x_4, x_5, x_560);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
lean_dec(x_618);
x_621 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_621, 0, x_615);
lean_ctor_set(x_621, 1, x_619);
x_622 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_621, x_3, x_4, x_5, x_620);
return x_622;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_615);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_623 = lean_ctor_get(x_618, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_618, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_625 = x_618;
} else {
 lean_dec_ref(x_618);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_623);
lean_ctor_set(x_626, 1, x_624);
return x_626;
}
}
case 1:
{
lean_object* x_627; lean_object* x_628; 
lean_dec(x_614);
lean_dec(x_556);
lean_dec(x_2);
lean_dec(x_1);
x_627 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_628 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_627, x_3, x_4, x_5, x_560);
return x_628;
}
default: 
{
lean_object* x_629; 
lean_dec(x_556);
x_629 = l_Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5, x_560);
return x_629;
}
}
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_IR_ToIR_lowerLet___closed__2;
x_12 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_11, x_7, x_8, x_9, x_10);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_10, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_13 = l_Lean_IR_ToIR_lowerCode(x_1, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fget(x_4, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_array_get(x_16, x_3, x_6);
switch (lean_obj_tag(x_17)) {
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
lean_inc(x_5);
x_21 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
return x_21;
}
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 2);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_6, x_31);
lean_dec(x_6);
lean_inc(x_5);
x_33 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_32, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_nat_add(x_36, x_37);
x_39 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set(x_39, 3, x_15);
lean_ctor_set(x_39, 4, x_30);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
x_44 = lean_nat_add(x_42, x_43);
x_45 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_29);
lean_ctor_set(x_45, 3, x_15);
lean_ctor_set(x_45, 4, x_30);
lean_ctor_set(x_45, 5, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_5);
return x_33;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_17);
lean_dec(x_15);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_6, x_47);
lean_dec(x_6);
x_6 = x_48;
goto _start;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_6, x_50);
lean_dec(x_6);
x_6 = x_51;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_IR_ToIR_newVar___redArg(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_box(7);
lean_inc(x_19);
lean_ctor_set_tag(x_17, 8);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_17);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_15);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_3);
lean_ctor_set(x_25, 3, x_1);
lean_ctor_set(x_21, 0, x_25);
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
x_28 = lean_box(7);
lean_inc(x_19);
lean_ctor_set_tag(x_17, 8);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 2, x_17);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_15);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_box(7);
lean_inc(x_31);
x_38 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_1, 3, x_34);
lean_ctor_set(x_1, 2, x_38);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_15);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_3);
lean_ctor_set(x_39, 3, x_1);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
else
{
lean_dec(x_31);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lean_IR_ToIR_bindVar___redArg(x_41, x_5, x_8);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_IR_ToIR_newVar___redArg(x_5, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_box(7);
lean_inc(x_46);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(8, 2, 0);
} else {
 x_54 = x_48;
 lean_ctor_set_tag(x_54, 8);
}
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_4);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_50);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_3);
lean_ctor_set(x_56, 3, x_55);
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
else
{
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
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
case 8:
{
lean_object* x_31; 
lean_dec(x_9);
x_31 = lean_box(7);
x_14 = x_31;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_13;
goto block_27;
}
default: 
{
lean_object* x_32; 
lean_inc(x_6);
lean_inc(x_5);
x_32 = l_Lean_IR_toIRType(x_9, x_5, x_6, x_13);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_14 = x_33;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_34;
goto block_27;
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_IR_ToIR_lowerLet_spec__0(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___Lean_IR_ToIR_lowerLet_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
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
x_3 = lean_unsigned_to_nat(285u);
x_4 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
x_5 = l_Lean_IR_ToIR_lowerArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
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
x_11 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
goto block_5;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
x_7 = l_Lean_IR_toIRType(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
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
x_16 = l_Lean_IR_ToIR_lowerResultType___redArg(x_7, x_15, x_3, x_4, x_14);
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
x_56 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_51);
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
x_71 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_65);
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
x_86 = l_Lean_IR_mkDummyExternDecl(x_6, x_13, x_78);
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
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Compiler_IR_ToIRType(builtin, lean_io_mk_world());
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
l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__0 = _init_l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__0);
l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1 = _init_l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__1);
l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2 = _init_l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_IR_ToIR_lowerArg_spec__0___closed__2);
l_Lean_IR_ToIR_lowerArg___closed__0 = _init_l_Lean_IR_ToIR_lowerArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__0);
l_Lean_IR_ToIR_lowerArg___closed__1 = _init_l_Lean_IR_ToIR_lowerArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__1);
l_Lean_IR_ToIR_lowerArg___closed__2 = _init_l_Lean_IR_ToIR_lowerArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__2);
l_Lean_IR_ToIR_lowerArg___closed__3 = _init_l_Lean_IR_ToIR_lowerArg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__3);
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
l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5 = _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5);
l_Lean_IR_toIR___closed__0 = _init_l_Lean_IR_toIR___closed__0();
lean_mark_persistent(l_Lean_IR_toIR___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
