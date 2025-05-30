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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3;
static lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4;
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__21;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_IR_ToIR_bindVar___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkPartialApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__31;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___closed__1;
static lean_object* l_panic___at_Lean_IR_ToIR_lowerType___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__3;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__33;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_IR_toIR___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedCtorFieldInfo;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_IR_ToIR_lowerArg___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__30;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
lean_object* l___private_Init_GetElem_0__List_get_x21Internal___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lambda__1___boxed(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__38;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__1;
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lambda__1(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
lean_object* l_Lean_Environment_addExtraName(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__3;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__15;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__7;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__19;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_getCtorInfo___closed__3;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__13;
static lean_object* l_Lean_IR_ToIR_lowerType___closed__12;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__29;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__23;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_getCtorInfo___closed__2;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedCtorInfo;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_IR_Decl_name(lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
static lean_object* l_Lean_IR_ToIR_lowerType___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__2;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_IR_toIR___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__9;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__14;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__11;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__6;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__18;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedIRType;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__22;
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__7;
static lean_object* l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__35;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedArg;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__6;
static lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__26;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__8;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ToIR_bindVar___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__7;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__24;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__37;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_get_ctor_layout(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2;
static lean_object* l_Lean_IR_ToIR_addDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__27;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__17;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__6;
static lean_object* l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__2;
static lean_object* l_Lean_IR_ToIR_M_run___rarg___closed__2;
static lean_object* l_Lean_IR_ToIR_M_run___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__3;
static lean_object* l_Lean_IR_ToIR_addDecl___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerAlt_loop___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__28;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__9;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__36;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__34;
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__20;
static lean_object* l_Lean_IR_ToIR_M_run___rarg___closed__1;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_ir_mk_dummy_extern_decl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__2;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__25;
static lean_object* l_Lean_IR_ToIR_lowerType___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerType___closed__10;
static lean_object* l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__1;
static lean_object* l_Lean_IR_ToIR_addDecl___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj;
static lean_object* l_Lean_IR_ToIR_getCtorInfo___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ToIR_M_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ToIR_M_run___rarg___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_IR_ToIR_M_run___rarg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_M_run___rarg___closed__3;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_IR_ToIR_M_run___rarg___closed__4;
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
uint8_t x_17; 
lean_dec(x_7);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_M_run___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ToIR_bindVar___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_4);
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
x_26 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_IR_ToIR_bindVar___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ToIR_bindVar___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_IR_ToIR_bindVar___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_10, x_13);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = lean_nat_add(x_16, x_13);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 2, x_31);
x_35 = lean_array_uset(x_17, x_30, x_34);
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
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_35);
lean_ctor_set(x_11, 1, x_42);
lean_ctor_set(x_11, 0, x_33);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_11);
x_43 = lean_st_ref_set(x_2, x_6, x_9);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_10);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_ctor_set(x_11, 1, x_35);
lean_ctor_set(x_11, 0, x_33);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_11);
x_48 = lean_st_ref_set(x_2, x_6, x_9);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_10);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_11);
x_53 = lean_st_ref_set(x_2, x_6, x_9);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_10);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_58 = lean_ctor_get(x_11, 0);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_11);
x_60 = lean_array_get_size(x_59);
x_61 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = lean_nat_add(x_58, x_13);
lean_dec(x_58);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_12);
lean_ctor_set(x_76, 2, x_73);
x_77 = lean_array_uset(x_59, x_72, x_76);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_nat_mul(x_75, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = lean_array_get_size(x_77);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_85);
x_86 = lean_st_ref_set(x_2, x_6, x_9);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_77);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_90);
x_91 = lean_st_ref_set(x_2, x_6, x_9);
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
lean_ctor_set(x_94, 0, x_10);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_58);
lean_ctor_set(x_95, 1, x_59);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_95);
x_96 = lean_st_ref_set(x_2, x_6, x_9);
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
lean_ctor_set(x_99, 0, x_10);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; uint8_t x_124; 
x_100 = lean_ctor_get(x_6, 0);
x_101 = lean_ctor_get(x_6, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_6);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
lean_dec(x_100);
lean_inc(x_102);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_102, x_105);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_array_get_size(x_108);
x_111 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_123 = lean_array_uget(x_108, x_122);
x_124 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_125 = lean_nat_add(x_107, x_105);
lean_dec(x_107);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_104);
lean_ctor_set(x_126, 2, x_123);
x_127 = lean_array_uset(x_108, x_122, x_126);
x_128 = lean_unsigned_to_nat(4u);
x_129 = lean_nat_mul(x_125, x_128);
x_130 = lean_unsigned_to_nat(3u);
x_131 = lean_nat_div(x_129, x_130);
lean_dec(x_129);
x_132 = lean_array_get_size(x_127);
x_133 = lean_nat_dec_le(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_127);
if (lean_is_scalar(x_109)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_109;
}
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_106);
x_137 = lean_st_ref_set(x_2, x_136, x_101);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_102);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
if (lean_is_scalar(x_109)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_109;
}
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_127);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_106);
x_143 = lean_st_ref_set(x_2, x_142, x_101);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_102);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_123);
lean_dec(x_104);
lean_dec(x_1);
if (lean_is_scalar(x_109)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_109;
}
lean_ctor_set(x_147, 0, x_107);
lean_ctor_set(x_147, 1, x_108);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_106);
x_149 = lean_st_ref_set(x_2, x_148, x_101);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_102);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_array_get_size(x_15);
x_17 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_14, x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_12);
lean_ctor_set(x_33, 2, x_29);
x_34 = lean_array_uset(x_15, x_28, x_33);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_nat_mul(x_32, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_34);
lean_ctor_set(x_11, 1, x_41);
lean_ctor_set(x_11, 0, x_32);
x_42 = lean_st_ref_set(x_3, x_8, x_9);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_ctor_set(x_11, 1, x_34);
lean_ctor_set(x_11, 0, x_32);
x_49 = lean_st_ref_set(x_3, x_8, x_9);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_1);
x_56 = lean_st_ref_set(x_3, x_8, x_9);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; uint8_t x_79; 
x_63 = lean_ctor_get(x_11, 0);
x_64 = lean_ctor_get(x_11, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_11);
x_65 = lean_array_get_size(x_64);
x_66 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_79 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_63, x_80);
lean_dec(x_63);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_12);
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
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_8, 0, x_91);
x_92 = lean_st_ref_set(x_3, x_8, x_9);
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
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_81);
lean_ctor_set(x_97, 1, x_83);
lean_ctor_set(x_8, 0, x_97);
x_98 = lean_st_ref_set(x_3, x_8, x_9);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_78);
lean_dec(x_12);
lean_dec(x_1);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_63);
lean_ctor_set(x_103, 1, x_64);
lean_ctor_set(x_8, 0, x_103);
x_104 = lean_st_ref_set(x_3, x_8, x_9);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; uint64_t x_122; size_t x_123; size_t x_124; size_t x_125; size_t x_126; size_t x_127; lean_object* x_128; uint8_t x_129; 
x_109 = lean_ctor_get(x_8, 0);
x_110 = lean_ctor_get(x_8, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_8);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_2);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
x_115 = lean_array_get_size(x_113);
x_116 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
x_117 = 32;
x_118 = lean_uint64_shift_right(x_116, x_117);
x_119 = lean_uint64_xor(x_116, x_118);
x_120 = 16;
x_121 = lean_uint64_shift_right(x_119, x_120);
x_122 = lean_uint64_xor(x_119, x_121);
x_123 = lean_uint64_to_usize(x_122);
x_124 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_125 = 1;
x_126 = lean_usize_sub(x_124, x_125);
x_127 = lean_usize_land(x_123, x_126);
x_128 = lean_array_uget(x_113, x_127);
x_129 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_112, x_130);
lean_dec(x_112);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_111);
lean_ctor_set(x_132, 2, x_128);
x_133 = lean_array_uset(x_113, x_127, x_132);
x_134 = lean_unsigned_to_nat(4u);
x_135 = lean_nat_mul(x_131, x_134);
x_136 = lean_unsigned_to_nat(3u);
x_137 = lean_nat_div(x_135, x_136);
lean_dec(x_135);
x_138 = lean_array_get_size(x_133);
x_139 = lean_nat_dec_le(x_137, x_138);
lean_dec(x_138);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_133);
if (lean_is_scalar(x_114)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_114;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_110);
x_143 = lean_st_ref_set(x_3, x_142, x_9);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
if (lean_is_scalar(x_114)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_114;
}
lean_ctor_set(x_148, 0, x_131);
lean_ctor_set(x_148, 1, x_133);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_110);
x_150 = lean_st_ref_set(x_3, x_149, x_9);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_box(0);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_128);
lean_dec(x_111);
lean_dec(x_1);
if (lean_is_scalar(x_114)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_114;
}
lean_ctor_set(x_155, 0, x_112);
lean_ctor_set(x_155, 1, x_113);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_110);
x_157 = lean_st_ref_set(x_3, x_156, x_9);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
}
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_ctor_set(x_6, 1, x_11);
x_12 = lean_st_ref_set(x_1, x_6, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_st_ref_set(x_1, x_21, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_10, x_13);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = lean_nat_add(x_16, x_13);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 2, x_31);
x_35 = lean_array_uset(x_17, x_30, x_34);
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
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_35);
lean_ctor_set(x_11, 1, x_42);
lean_ctor_set(x_11, 0, x_33);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_11);
x_43 = lean_st_ref_set(x_2, x_6, x_9);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_10);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_ctor_set(x_11, 1, x_35);
lean_ctor_set(x_11, 0, x_33);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_11);
x_48 = lean_st_ref_set(x_2, x_6, x_9);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_10);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_11);
x_53 = lean_st_ref_set(x_2, x_6, x_9);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_10);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_58 = lean_ctor_get(x_11, 0);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_11);
x_60 = lean_array_get_size(x_59);
x_61 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = lean_nat_add(x_58, x_13);
lean_dec(x_58);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_12);
lean_ctor_set(x_76, 2, x_73);
x_77 = lean_array_uset(x_59, x_72, x_76);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_nat_mul(x_75, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = lean_array_get_size(x_77);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_85);
x_86 = lean_st_ref_set(x_2, x_6, x_9);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_77);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_90);
x_91 = lean_st_ref_set(x_2, x_6, x_9);
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
lean_ctor_set(x_94, 0, x_10);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_58);
lean_ctor_set(x_95, 1, x_59);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_95);
x_96 = lean_st_ref_set(x_2, x_6, x_9);
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
lean_ctor_set(x_99, 0, x_10);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; uint8_t x_124; 
x_100 = lean_ctor_get(x_6, 0);
x_101 = lean_ctor_get(x_6, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_6);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
lean_dec(x_100);
lean_inc(x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_102, x_105);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_array_get_size(x_108);
x_111 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_123 = lean_array_uget(x_108, x_122);
x_124 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_125 = lean_nat_add(x_107, x_105);
lean_dec(x_107);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_104);
lean_ctor_set(x_126, 2, x_123);
x_127 = lean_array_uset(x_108, x_122, x_126);
x_128 = lean_unsigned_to_nat(4u);
x_129 = lean_nat_mul(x_125, x_128);
x_130 = lean_unsigned_to_nat(3u);
x_131 = lean_nat_div(x_129, x_130);
lean_dec(x_129);
x_132 = lean_array_get_size(x_127);
x_133 = lean_nat_dec_le(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_127);
if (lean_is_scalar(x_109)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_109;
}
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_106);
x_137 = lean_st_ref_set(x_2, x_136, x_101);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_102);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
if (lean_is_scalar(x_109)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_109;
}
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_127);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_106);
x_143 = lean_st_ref_set(x_2, x_142, x_101);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_102);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_123);
lean_dec(x_104);
lean_dec(x_1);
if (lean_is_scalar(x_109)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_109;
}
lean_ctor_set(x_147, 0, x_107);
lean_ctor_set(x_147, 1, x_108);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_106);
x_149 = lean_st_ref_set(x_2, x_148, x_101);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_102);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_array_get_size(x_14);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_14, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_13, x_30);
lean_dec(x_13);
x_32 = lean_box(2);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
x_34 = lean_array_uset(x_14, x_27, x_33);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_nat_mul(x_31, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_34);
lean_ctor_set(x_8, 1, x_41);
lean_ctor_set(x_8, 0, x_31);
x_42 = lean_st_ref_set(x_2, x_7, x_9);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_ctor_set(x_8, 1, x_34);
lean_ctor_set(x_8, 0, x_31);
x_49 = lean_st_ref_set(x_2, x_7, x_9);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_28);
lean_dec(x_1);
x_56 = lean_st_ref_set(x_2, x_7, x_9);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; uint8_t x_79; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_65 = lean_array_get_size(x_64);
x_66 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
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
x_79 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_63, x_80);
lean_dec(x_63);
x_82 = lean_box(2);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_78);
x_84 = lean_array_uset(x_64, x_77, x_83);
x_85 = lean_unsigned_to_nat(4u);
x_86 = lean_nat_mul(x_81, x_85);
x_87 = lean_unsigned_to_nat(3u);
x_88 = lean_nat_div(x_86, x_87);
lean_dec(x_86);
x_89 = lean_array_get_size(x_84);
x_90 = lean_nat_dec_le(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_84);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_7, 0, x_92);
x_93 = lean_st_ref_set(x_2, x_7, x_9);
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
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_84);
lean_ctor_set(x_7, 0, x_98);
x_99 = lean_st_ref_set(x_2, x_7, x_9);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_78);
lean_dec(x_1);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_63);
lean_ctor_set(x_104, 1, x_64);
lean_ctor_set(x_7, 0, x_104);
x_105 = lean_st_ref_set(x_2, x_7, x_9);
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
x_108 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; size_t x_122; size_t x_123; size_t x_124; size_t x_125; size_t x_126; lean_object* x_127; uint8_t x_128; 
x_110 = lean_ctor_get(x_7, 1);
lean_inc(x_110);
lean_dec(x_7);
x_111 = lean_ctor_get(x_8, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_8, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_113 = x_8;
} else {
 lean_dec_ref(x_8);
 x_113 = lean_box(0);
}
x_114 = lean_array_get_size(x_112);
x_115 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_1);
x_116 = 32;
x_117 = lean_uint64_shift_right(x_115, x_116);
x_118 = lean_uint64_xor(x_115, x_117);
x_119 = 16;
x_120 = lean_uint64_shift_right(x_118, x_119);
x_121 = lean_uint64_xor(x_118, x_120);
x_122 = lean_uint64_to_usize(x_121);
x_123 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_124 = 1;
x_125 = lean_usize_sub(x_123, x_124);
x_126 = lean_usize_land(x_122, x_125);
x_127 = lean_array_uget(x_112, x_126);
x_128 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ToIR_bindVar___spec__1(x_1, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_add(x_111, x_129);
lean_dec(x_111);
x_131 = lean_box(2);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_127);
x_133 = lean_array_uset(x_112, x_126, x_132);
x_134 = lean_unsigned_to_nat(4u);
x_135 = lean_nat_mul(x_130, x_134);
x_136 = lean_unsigned_to_nat(3u);
x_137 = lean_nat_div(x_135, x_136);
lean_dec(x_135);
x_138 = lean_array_get_size(x_133);
x_139 = lean_nat_dec_le(x_137, x_138);
lean_dec(x_138);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ToIR_bindVar___spec__2(x_133);
if (lean_is_scalar(x_113)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_113;
}
lean_ctor_set(x_141, 0, x_130);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_110);
x_143 = lean_st_ref_set(x_2, x_142, x_9);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
if (lean_is_scalar(x_113)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_113;
}
lean_ctor_set(x_148, 0, x_130);
lean_ctor_set(x_148, 1, x_133);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_110);
x_150 = lean_st_ref_set(x_2, x_149, x_9);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_box(0);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_127);
lean_dec(x_1);
if (lean_is_scalar(x_113)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_113;
}
lean_ctor_set(x_155, 0, x_111);
lean_ctor_set(x_155, 1, x_112);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_110);
x_157 = lean_st_ref_set(x_2, x_156, x_9);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
}
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ir_find_env_decl(x_9, x_1);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ir_find_env_decl(x_13, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
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
static lean_object* _init_l_Lean_IR_ToIR_addDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declMapExt;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 5);
lean_dec(x_11);
x_12 = l_Lean_IR_Decl_name(x_1);
x_13 = l_Lean_Environment_addExtraName(x_10, x_12);
x_14 = l_Lean_IR_ToIR_addDecl___closed__1;
x_15 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_14, x_13, x_1);
x_16 = l_Lean_IR_ToIR_addDecl___closed__4;
lean_ctor_set(x_7, 5, x_16);
lean_ctor_set(x_7, 0, x_15);
x_17 = lean_st_ref_set(x_4, x_7, x_8);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
x_27 = lean_ctor_get(x_7, 3);
x_28 = lean_ctor_get(x_7, 4);
x_29 = lean_ctor_get(x_7, 6);
x_30 = lean_ctor_get(x_7, 7);
x_31 = lean_ctor_get(x_7, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_32 = l_Lean_IR_Decl_name(x_1);
x_33 = l_Lean_Environment_addExtraName(x_24, x_32);
x_34 = l_Lean_IR_ToIR_addDecl___closed__1;
x_35 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_34, x_33, x_1);
x_36 = l_Lean_IR_ToIR_addDecl___closed__4;
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set(x_37, 6, x_29);
lean_ctor_set(x_37, 7, x_30);
lean_ctor_set(x_37, 8, x_31);
x_38 = lean_st_ref_set(x_4, x_37, x_8);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
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
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
case 2:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_9 = lean_uint8_to_nat(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 3:
{
uint16_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get_uint16(x_1, 0);
lean_dec(x_1);
x_12 = lean_uint16_to_nat(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
case 4:
{
uint32_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get_uint32(x_1, 0);
lean_dec(x_1);
x_15 = lean_uint32_to_nat(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
default: 
{
uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_18 = lean_uint64_to_nat(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__2;
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_4(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerEnumToScalarType", 34, 34);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected valid constructor name", 31, 31);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(82u);
x_4 = lean_unsigned_to_nat(57u);
x_5 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__5;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_24; lean_object* x_25; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_16 = x_6;
} else {
 lean_dec_ref(x_6);
 x_16 = lean_box(0);
}
x_24 = 0;
lean_inc(x_1);
x_25 = l_Lean_Environment_find_x3f(x_1, x_14, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1(x_26, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_4);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_4);
x_17 = x_29;
x_18 = x_28;
goto block_23;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
switch (lean_obj_tag(x_34)) {
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_38 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1(x_37, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_4);
lean_ctor_set(x_34, 0, x_4);
x_17 = x_34;
x_18 = x_39;
goto block_23;
}
else
{
uint8_t x_40; 
lean_free_object(x_34);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
x_44 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1(x_44, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_4);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_4);
x_17 = x_47;
x_18 = x_46;
goto block_23;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
case 6:
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 2);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Expr_isForall(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_inc(x_4);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_4);
x_17 = x_34;
x_18 = x_12;
goto block_23;
}
else
{
lean_object* x_57; 
lean_free_object(x_34);
x_57 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__7;
x_17 = x_57;
x_18 = x_12;
goto block_23;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_34, 0);
lean_inc(x_58);
lean_dec(x_34);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 2);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Expr_isForall(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_inc(x_4);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_4);
x_17 = x_62;
x_18 = x_12;
goto block_23;
}
else
{
lean_object* x_63; 
x_63 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__7;
x_17 = x_63;
x_18 = x_12;
goto block_23;
}
}
}
default: 
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_34);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_34, 0);
lean_dec(x_65);
x_66 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_67 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1(x_66, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_4);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_4);
x_17 = x_34;
x_18 = x_68;
goto block_23;
}
else
{
uint8_t x_69; 
lean_free_object(x_34);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_67);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_34);
x_73 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_74 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1(x_73, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_4);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_4);
x_17 = x_76;
x_18 = x_75;
goto block_23;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
}
block_23:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
 lean_ctor_set_tag(x_20, 0);
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_6 = x_15;
x_7 = x_21;
x_8 = lean_box(0);
x_12 = x_18;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(3);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(256u);
x_11 = lean_nat_dec_lt(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(65536u);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_cstr_to_nat("4294967296");
x_15 = lean_nat_dec_lt(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__2;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__3;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerEnumToScalarType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
lean_inc(x_10);
x_12 = l_Lean_Environment_find_x3f(x_10, x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_List_lengthTRAux___rarg(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = l_Lean_IR_ToIR_lowerEnumToScalarType___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
x_22 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2(x_10, x_16, x_19, x_21, x_16, x_16, x_21, lean_box(0), x_2, x_3, x_4, x_9);
lean_dec(x_16);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1(x_18, x_20, x_26, x_2, x_3, x_4, x_25);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_18);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
lean_ctor_set(x_6, 0, x_38);
return x_6;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_6, 0);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_6);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 0;
lean_inc(x_41);
x_43 = l_Lean_Environment_find_x3f(x_41, x_1, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
if (lean_obj_tag(x_46) == 5)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_47, 4);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_List_lengthTRAux___rarg(x_48, x_49);
x_51 = lean_box(0);
x_52 = lean_box(0);
x_53 = l_Lean_IR_ToIR_lowerEnumToScalarType___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_48);
x_54 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2(x_41, x_48, x_51, x_53, x_48, x_48, x_53, lean_box(0), x_2, x_3, x_4, x_40);
lean_dec(x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_box(0);
x_59 = l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1(x_50, x_52, x_58, x_2, x_3, x_4, x_57);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_50);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_50);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_50);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_ctor_get(x_54, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_66 = x_54;
} else {
 lean_dec_ref(x_54);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_40);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_panic___at_Lean_IR_ToIR_lowerType___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1;
x_2 = l_Lean_IR_instInhabitedIRType;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_panic___at_Lean_IR_ToIR_lowerType___spec__1___closed__1;
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_4(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerType", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid type", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerType___closed__1;
x_3 = lean_unsigned_to_nat(121u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_IR_ToIR_lowerType___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt8", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt16", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt64", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("USize", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Float", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Float32", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerType___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Lean_IR_ToIR_lowerType___closed__4;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_IR_ToIR_lowerType___closed__5;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_IR_ToIR_lowerType___closed__6;
x_14 = lean_string_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_IR_ToIR_lowerType___closed__7;
x_16 = lean_string_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_IR_ToIR_lowerType___closed__8;
x_18 = lean_string_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_IR_ToIR_lowerType___closed__9;
x_20 = lean_string_dec_eq(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_IR_ToIR_lowerType___closed__10;
x_22 = lean_string_dec_eq(x_8, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_IR_ToIR_lowerType___closed__11;
x_24 = lean_string_dec_eq(x_8, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_IR_ToIR_lowerType___closed__12;
x_26 = lean_string_dec_eq(x_8, x_25);
lean_dec(x_8);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_6, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(7);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_37);
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_box(6);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_box(9);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_5);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_box(5);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_box(4);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_5);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_box(2);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_5);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec(x_7);
x_63 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_6, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
x_67 = lean_box(7);
lean_ctor_set(x_63, 0, x_67);
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_box(7);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_63, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
lean_dec(x_64);
lean_ctor_set(x_63, 0, x_73);
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
lean_dec(x_63);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_63);
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
lean_object* x_81; 
x_81 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_6, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
x_85 = lean_box(7);
lean_ctor_set(x_81, 0, x_85);
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_87 = lean_box(7);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_81, 0);
lean_dec(x_90);
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
lean_dec(x_82);
lean_ctor_set(x_81, 0, x_91);
return x_81;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
lean_dec(x_81);
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
lean_dec(x_82);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_81);
if (x_95 == 0)
{
return x_81;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_81, 0);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_81);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
case 5:
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
lean_dec(x_1);
x_100 = l_Lean_Expr_headBeta(x_99);
if (lean_obj_tag(x_100) == 4)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_101, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = lean_box(7);
lean_ctor_set(x_102, 0, x_106);
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_dec(x_102);
x_108 = lean_box(7);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_102);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_102, 0);
lean_dec(x_111);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
lean_dec(x_103);
lean_ctor_set(x_102, 0, x_112);
return x_102;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_102, 1);
lean_inc(x_113);
lean_dec(x_102);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
lean_dec(x_103);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_102);
if (x_116 == 0)
{
return x_102;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_102, 0);
x_118 = lean_ctor_get(x_102, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_102);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_100);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_box(7);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_5);
return x_121;
}
}
case 7:
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_box(7);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_5);
return x_123;
}
default: 
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_124 = l_Lean_IR_ToIR_lowerType___closed__3;
x_125 = l_panic___at_Lean_IR_ToIR_lowerType___spec__1(x_124, x_2, x_3, x_4, x_5);
return x_125;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_instInhabitedCtorInfo;
x_2 = l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1;
x_2 = l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__2;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__3;
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_4(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_ToIR_getCtorInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.getCtorInfo", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_getCtorInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unrecognized constructor", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_getCtorInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_getCtorInfo___closed__1;
x_3 = lean_unsigned_to_nat(134u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_IR_ToIR_getCtorInfo___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_IR_ToIR_getCtorInfo___closed__3;
x_13 = l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1(x_12, x_2, x_3, x_4, x_9);
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
x_32 = l_Lean_IR_ToIR_getCtorInfo___closed__3;
x_33 = l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1(x_32, x_2, x_3, x_4, x_29);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_panic___at_Lean_IR_ToIR_lowerArg___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1;
x_2 = l_Lean_IR_instInhabitedArg;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_panic___at_Lean_IR_ToIR_lowerArg___spec__2___closed__1;
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_4(x_7, x_2, x_3, x_4, x_5);
return x_8;
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
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerArg___closed__1;
x_3 = lean_unsigned_to_nat(142u);
x_4 = lean_unsigned_to_nat(37u);
x_5 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_6);
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
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_6, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_7);
x_29 = l_Lean_IR_ToIR_lowerArg___closed__3;
x_30 = l_panic___at_Lean_IR_ToIR_lowerArg___spec__2(x_29, x_2, x_3, x_4, x_11);
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
x_36 = l_panic___at_Lean_IR_ToIR_lowerArg___spec__2(x_35, x_2, x_3, x_4, x_11);
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
x_41 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_6);
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
x_54 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_6, x_53);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_IR_ToIR_lowerArg___closed__3;
x_56 = l_panic___at_Lean_IR_ToIR_lowerArg___spec__2(x_55, x_2, x_3, x_4, x_38);
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
x_63 = l_panic___at_Lean_IR_ToIR_lowerArg___spec__2(x_62, x_2, x_3, x_4, x_38);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1;
x_2 = l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
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
static lean_object* _init_l_Lean_IR_ToIR_lowerProj___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_box(6);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
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
x_4 = l_Lean_IR_ToIR_lowerProj___closed__1;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_IR_ToIR_bindVar(x_6, x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = l_Lean_IR_ToIR_lowerType(x_10, x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1;
x_2 = l_Lean_IR_instInhabitedFnBody;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1___closed__1;
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_4(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerAlt.loop", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mismatched fields and params", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerAlt_loop___closed__1;
x_3 = lean_unsigned_to_nat(372u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_IR_ToIR_lowerAlt_loop___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_array_get_size(x_4);
x_46 = lean_nat_dec_lt(x_6, x_45);
lean_dec(x_45);
x_47 = lean_array_get_size(x_5);
x_48 = lean_nat_dec_lt(x_6, x_47);
lean_dec(x_47);
if (x_46 == 0)
{
lean_dec(x_6);
lean_dec(x_1);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lean_IR_ToIR_lowerCode(x_2, x_7, x_8, x_9, x_10);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_50 = l_Lean_IR_ToIR_lowerAlt_loop___closed__3;
x_51 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_50, x_7, x_8, x_9, x_10);
return x_51;
}
}
else
{
lean_object* x_52; 
x_52 = lean_array_fget(x_4, x_6);
if (x_48 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_11 = x_53;
x_12 = x_52;
goto block_44;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_array_fget(x_5, x_6);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_11 = x_55;
x_12 = x_52;
goto block_44;
}
}
block_44:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_IR_ToIR_lowerAlt_loop___closed__3;
x_14 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_13, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_1);
x_16 = l_Lean_IR_ToIR_lowerProj(x_1, x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_IR_ToIR_bindVar(x_20, x_7, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_26 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_25, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_19);
lean_ctor_set(x_32, 3, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_16);
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
lean_dec(x_12);
x_39 = l_Lean_IR_ToIR_bindErased(x_38, x_7, x_8, x_9, x_10);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_6, x_41);
lean_dec(x_6);
x_6 = x_42;
x_10 = x_40;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_IR_ToIR_lowerParam(x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_12, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_IR_ToIR_lowerArg(x_10, x_4, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_12, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_4, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_4, x_3, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_IR_ToIR_lowerAlt(x_1, x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_13, x_3, x_15);
x_3 = x_18;
x_4 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedArg;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all local functions should be λ-lifted", 39, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_3 = lean_unsigned_to_nat(192u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_IR_ToIR_lowerCode___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_3 = lean_unsigned_to_nat(176u);
x_4 = lean_unsigned_to_nat(46u);
x_5 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_3 = lean_unsigned_to_nat(184u);
x_4 = lean_unsigned_to_nat(52u);
x_5 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_3 = lean_unsigned_to_nat(189u);
x_4 = lean_unsigned_to_nat(37u);
x_5 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_IR_ToIR_lowerLet(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_IR_ToIR_lowerCode___closed__3;
x_10 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = l_Lean_IR_ToIR_bindJoinPoint(x_13, x_2, x_3, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_11, 2);
lean_inc(x_17);
x_18 = lean_array_size(x_17);
x_19 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__1(x_18, x_19, x_17, x_2, x_3, x_4, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_11, 4);
lean_inc(x_23);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_IR_ToIR_lowerCode(x_23, x_2, x_3, x_4, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_IR_ToIR_lowerCode(x_12, x_2, x_3, x_4, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_15);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 3:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_st_ref_get(x_2, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; size_t x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_array_get_size(x_54);
x_57 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_47);
x_58 = 32;
x_59 = lean_uint64_shift_right(x_57, x_58);
x_60 = lean_uint64_xor(x_57, x_59);
x_61 = 16;
x_62 = lean_uint64_shift_right(x_60, x_61);
x_63 = lean_uint64_xor(x_60, x_62);
x_64 = lean_uint64_to_usize(x_63);
x_65 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_66 = 1;
x_67 = lean_usize_sub(x_65, x_66);
x_68 = lean_usize_land(x_64, x_67);
x_69 = lean_array_uget(x_54, x_68);
lean_dec(x_54);
x_70 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_47, x_69);
lean_dec(x_69);
lean_dec(x_47);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_free_object(x_51);
lean_dec(x_48);
x_71 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_72 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_71, x_2, x_3, x_4, x_52);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_array_size(x_48);
x_76 = 0;
x_77 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_75, x_76, x_48, x_2, x_3, x_4, x_52);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_ctor_set_tag(x_51, 12);
lean_ctor_set(x_51, 1, x_79);
lean_ctor_set(x_51, 0, x_74);
lean_ctor_set(x_77, 0, x_51);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_77);
lean_ctor_set_tag(x_51, 12);
lean_ctor_set(x_51, 1, x_80);
lean_ctor_set(x_51, 0, x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_51);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_74);
lean_free_object(x_51);
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_77);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_73);
lean_free_object(x_51);
lean_dec(x_48);
x_87 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_88 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_87, x_2, x_3, x_4, x_52);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; lean_object* x_104; 
x_89 = lean_ctor_get(x_51, 1);
lean_inc(x_89);
lean_dec(x_51);
x_90 = lean_array_get_size(x_89);
x_91 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_47);
x_92 = 32;
x_93 = lean_uint64_shift_right(x_91, x_92);
x_94 = lean_uint64_xor(x_91, x_93);
x_95 = 16;
x_96 = lean_uint64_shift_right(x_94, x_95);
x_97 = lean_uint64_xor(x_94, x_96);
x_98 = lean_uint64_to_usize(x_97);
x_99 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_100 = 1;
x_101 = lean_usize_sub(x_99, x_100);
x_102 = lean_usize_land(x_98, x_101);
x_103 = lean_array_uget(x_89, x_102);
lean_dec(x_89);
x_104 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_47, x_103);
lean_dec(x_103);
lean_dec(x_47);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_48);
x_105 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_106 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_105, x_2, x_3, x_4, x_52);
return x_106;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
lean_dec(x_104);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_108; size_t x_109; size_t x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_array_size(x_48);
x_110 = 0;
x_111 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_109, x_110, x_48, x_2, x_3, x_4, x_52);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_112);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_108);
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_119 = x_111;
} else {
 lean_dec_ref(x_111);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_107);
lean_dec(x_48);
x_121 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_122 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_121, x_2, x_3, x_4, x_52);
return x_122;
}
}
}
}
case 4:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_1, 0);
lean_inc(x_123);
lean_dec(x_1);
x_124 = lean_st_ref_get(x_2, x_5);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; size_t x_142; size_t x_143; size_t x_144; size_t x_145; size_t x_146; lean_object* x_147; lean_object* x_148; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
x_131 = lean_ctor_get(x_123, 2);
x_132 = lean_ctor_get(x_123, 3);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_dec(x_126);
x_134 = lean_array_get_size(x_133);
x_135 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_131);
x_136 = 32;
x_137 = lean_uint64_shift_right(x_135, x_136);
x_138 = lean_uint64_xor(x_135, x_137);
x_139 = 16;
x_140 = lean_uint64_shift_right(x_138, x_139);
x_141 = lean_uint64_xor(x_138, x_140);
x_142 = lean_uint64_to_usize(x_141);
x_143 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_144 = 1;
x_145 = lean_usize_sub(x_143, x_144);
x_146 = lean_usize_land(x_142, x_145);
x_147 = lean_array_uget(x_133, x_146);
lean_dec(x_133);
x_148 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_131, x_147);
lean_dec(x_147);
lean_dec(x_131);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_free_object(x_123);
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_129);
x_149 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_150 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_149, x_2, x_3, x_4, x_127);
return x_150;
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_153 = l_Lean_IR_ToIR_lowerType(x_130, x_2, x_3, x_4, x_127);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_array_size(x_132);
x_157 = 0;
lean_inc(x_152);
x_158 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__3(x_152, x_156, x_157, x_132, x_2, x_3, x_4, x_155);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_158, 0);
lean_ctor_set_tag(x_123, 10);
lean_ctor_set(x_123, 3, x_160);
lean_ctor_set(x_123, 2, x_154);
lean_ctor_set(x_123, 1, x_152);
lean_ctor_set(x_158, 0, x_123);
return x_158;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_158, 0);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_158);
lean_ctor_set_tag(x_123, 10);
lean_ctor_set(x_123, 3, x_161);
lean_ctor_set(x_123, 2, x_154);
lean_ctor_set(x_123, 1, x_152);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_123);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
else
{
uint8_t x_164; 
lean_dec(x_154);
lean_dec(x_152);
lean_free_object(x_123);
lean_dec(x_129);
x_164 = !lean_is_exclusive(x_158);
if (x_164 == 0)
{
return x_158;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_158, 0);
x_166 = lean_ctor_get(x_158, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_158);
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
lean_dec(x_152);
lean_free_object(x_123);
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_153);
if (x_168 == 0)
{
return x_153;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_153, 0);
x_170 = lean_ctor_get(x_153, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_153);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_151);
lean_free_object(x_123);
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_129);
x_172 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_173 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_172, x_2, x_3, x_4, x_127);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; size_t x_187; size_t x_188; size_t x_189; size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
x_174 = lean_ctor_get(x_123, 0);
x_175 = lean_ctor_get(x_123, 1);
x_176 = lean_ctor_get(x_123, 2);
x_177 = lean_ctor_get(x_123, 3);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_123);
x_178 = lean_ctor_get(x_126, 1);
lean_inc(x_178);
lean_dec(x_126);
x_179 = lean_array_get_size(x_178);
x_180 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_176);
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
x_192 = lean_array_uget(x_178, x_191);
lean_dec(x_178);
x_193 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_176, x_192);
lean_dec(x_192);
lean_dec(x_176);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
x_194 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_195 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_194, x_2, x_3, x_4, x_127);
return x_195;
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
lean_dec(x_193);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec(x_196);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_198 = l_Lean_IR_ToIR_lowerType(x_175, x_2, x_3, x_4, x_127);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; size_t x_201; size_t x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_array_size(x_177);
x_202 = 0;
lean_inc(x_197);
x_203 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__3(x_197, x_201, x_202, x_177, x_2, x_3, x_4, x_200);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_207, 0, x_174);
lean_ctor_set(x_207, 1, x_197);
lean_ctor_set(x_207, 2, x_199);
lean_ctor_set(x_207, 3, x_204);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_174);
x_209 = lean_ctor_get(x_203, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_203, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_211 = x_203;
} else {
 lean_dec_ref(x_203);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_197);
lean_dec(x_177);
lean_dec(x_174);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_213 = lean_ctor_get(x_198, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_198, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_215 = x_198;
} else {
 lean_dec_ref(x_198);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_196);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
x_217 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_218 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_217, x_2, x_3, x_4, x_127);
return x_218;
}
}
}
}
case 5:
{
uint8_t x_219; 
lean_dec(x_4);
lean_dec(x_3);
x_219 = !lean_is_exclusive(x_1);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_1, 0);
x_221 = lean_st_ref_get(x_2, x_5);
lean_dec(x_2);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = !lean_is_exclusive(x_221);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint64_t x_228; uint64_t x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; size_t x_235; size_t x_236; size_t x_237; size_t x_238; size_t x_239; lean_object* x_240; lean_object* x_241; 
x_225 = lean_ctor_get(x_221, 0);
lean_dec(x_225);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = lean_array_get_size(x_226);
x_228 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_220);
x_229 = 32;
x_230 = lean_uint64_shift_right(x_228, x_229);
x_231 = lean_uint64_xor(x_228, x_230);
x_232 = 16;
x_233 = lean_uint64_shift_right(x_231, x_232);
x_234 = lean_uint64_xor(x_231, x_233);
x_235 = lean_uint64_to_usize(x_234);
x_236 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_237 = 1;
x_238 = lean_usize_sub(x_236, x_237);
x_239 = lean_usize_land(x_235, x_238);
x_240 = lean_array_uget(x_226, x_239);
lean_dec(x_226);
x_241 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_220, x_240);
lean_dec(x_240);
lean_dec(x_220);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_243 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_242);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 0, x_243);
lean_ctor_set(x_221, 0, x_1);
return x_221;
}
else
{
uint8_t x_244; 
lean_free_object(x_1);
x_244 = !lean_is_exclusive(x_241);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_241, 0);
switch (lean_obj_tag(x_245)) {
case 0:
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_ctor_set_tag(x_241, 11);
lean_ctor_set(x_221, 0, x_241);
return x_221;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set_tag(x_241, 11);
lean_ctor_set(x_241, 0, x_248);
lean_ctor_set(x_221, 0, x_241);
return x_221;
}
}
case 1:
{
uint8_t x_249; 
lean_free_object(x_241);
x_249 = !lean_is_exclusive(x_245);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_245, 0);
lean_dec(x_250);
x_251 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_252 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_251);
lean_ctor_set_tag(x_245, 11);
lean_ctor_set(x_245, 0, x_252);
lean_ctor_set(x_221, 0, x_245);
return x_221;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_245);
x_253 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_254 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_253);
x_255 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_221, 0, x_255);
return x_221;
}
}
default: 
{
lean_object* x_256; 
lean_free_object(x_241);
x_256 = l_Lean_IR_ToIR_lowerCode___closed__7;
lean_ctor_set(x_221, 0, x_256);
return x_221;
}
}
}
else
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_241, 0);
lean_inc(x_257);
lean_dec(x_241);
switch (lean_obj_tag(x_257)) {
case 0:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
x_261 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_221, 0, x_261);
return x_221;
}
case 1:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_262 = x_257;
} else {
 lean_dec_ref(x_257);
 x_262 = lean_box(0);
}
x_263 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_264 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_263);
if (lean_is_scalar(x_262)) {
 x_265 = lean_alloc_ctor(11, 1, 0);
} else {
 x_265 = x_262;
 lean_ctor_set_tag(x_265, 11);
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_221, 0, x_265);
return x_221;
}
default: 
{
lean_object* x_266; 
x_266 = l_Lean_IR_ToIR_lowerCode___closed__7;
lean_ctor_set(x_221, 0, x_266);
return x_221;
}
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint64_t x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; uint64_t x_274; uint64_t x_275; uint64_t x_276; size_t x_277; size_t x_278; size_t x_279; size_t x_280; size_t x_281; lean_object* x_282; lean_object* x_283; 
x_267 = lean_ctor_get(x_221, 1);
lean_inc(x_267);
lean_dec(x_221);
x_268 = lean_ctor_get(x_223, 1);
lean_inc(x_268);
lean_dec(x_223);
x_269 = lean_array_get_size(x_268);
x_270 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_220);
x_271 = 32;
x_272 = lean_uint64_shift_right(x_270, x_271);
x_273 = lean_uint64_xor(x_270, x_272);
x_274 = 16;
x_275 = lean_uint64_shift_right(x_273, x_274);
x_276 = lean_uint64_xor(x_273, x_275);
x_277 = lean_uint64_to_usize(x_276);
x_278 = lean_usize_of_nat(x_269);
lean_dec(x_269);
x_279 = 1;
x_280 = lean_usize_sub(x_278, x_279);
x_281 = lean_usize_land(x_277, x_280);
x_282 = lean_array_uget(x_268, x_281);
lean_dec(x_268);
x_283 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_220, x_282);
lean_dec(x_282);
lean_dec(x_220);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_285 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_284);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 0, x_285);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_1);
lean_ctor_set(x_286, 1, x_267);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_free_object(x_1);
x_287 = lean_ctor_get(x_283, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_288 = x_283;
} else {
 lean_dec_ref(x_283);
 x_288 = lean_box(0);
}
switch (lean_obj_tag(x_287)) {
case 0:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
if (lean_is_scalar(x_288)) {
 x_292 = lean_alloc_ctor(11, 1, 0);
} else {
 x_292 = x_288;
 lean_ctor_set_tag(x_292, 11);
}
lean_ctor_set(x_292, 0, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_267);
return x_293;
}
case 1:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_288);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_294 = x_287;
} else {
 lean_dec_ref(x_287);
 x_294 = lean_box(0);
}
x_295 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_296 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_295);
if (lean_is_scalar(x_294)) {
 x_297 = lean_alloc_ctor(11, 1, 0);
} else {
 x_297 = x_294;
 lean_ctor_set_tag(x_297, 11);
}
lean_ctor_set(x_297, 0, x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_267);
return x_298;
}
default: 
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_288);
x_299 = l_Lean_IR_ToIR_lowerCode___closed__7;
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_267);
return x_300;
}
}
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint64_t x_309; uint64_t x_310; uint64_t x_311; uint64_t x_312; uint64_t x_313; uint64_t x_314; uint64_t x_315; size_t x_316; size_t x_317; size_t x_318; size_t x_319; size_t x_320; lean_object* x_321; lean_object* x_322; 
x_301 = lean_ctor_get(x_1, 0);
lean_inc(x_301);
lean_dec(x_1);
x_302 = lean_st_ref_get(x_2, x_5);
lean_dec(x_2);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_306 = x_302;
} else {
 lean_dec_ref(x_302);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_304, 1);
lean_inc(x_307);
lean_dec(x_304);
x_308 = lean_array_get_size(x_307);
x_309 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_301);
x_310 = 32;
x_311 = lean_uint64_shift_right(x_309, x_310);
x_312 = lean_uint64_xor(x_309, x_311);
x_313 = 16;
x_314 = lean_uint64_shift_right(x_312, x_313);
x_315 = lean_uint64_xor(x_312, x_314);
x_316 = lean_uint64_to_usize(x_315);
x_317 = lean_usize_of_nat(x_308);
lean_dec(x_308);
x_318 = 1;
x_319 = lean_usize_sub(x_317, x_318);
x_320 = lean_usize_land(x_316, x_319);
x_321 = lean_array_uget(x_307, x_320);
lean_dec(x_307);
x_322 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_301, x_321);
lean_dec(x_321);
lean_dec(x_301);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_323 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_324 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_323);
x_325 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_325, 0, x_324);
if (lean_is_scalar(x_306)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_306;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_305);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_322, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_328 = x_322;
} else {
 lean_dec_ref(x_322);
 x_328 = lean_box(0);
}
switch (lean_obj_tag(x_327)) {
case 0:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 1, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
if (lean_is_scalar(x_328)) {
 x_332 = lean_alloc_ctor(11, 1, 0);
} else {
 x_332 = x_328;
 lean_ctor_set_tag(x_332, 11);
}
lean_ctor_set(x_332, 0, x_331);
if (lean_is_scalar(x_306)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_306;
}
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_305);
return x_333;
}
case 1:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_328);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 x_334 = x_327;
} else {
 lean_dec_ref(x_327);
 x_334 = lean_box(0);
}
x_335 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_336 = l_panic___at_Lean_IR_ToIR_lowerCode___spec__4(x_335);
if (lean_is_scalar(x_334)) {
 x_337 = lean_alloc_ctor(11, 1, 0);
} else {
 x_337 = x_334;
 lean_ctor_set_tag(x_337, 11);
}
lean_ctor_set(x_337, 0, x_336);
if (lean_is_scalar(x_306)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_306;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_305);
return x_338;
}
default: 
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_328);
x_339 = l_Lean_IR_ToIR_lowerCode___closed__7;
if (lean_is_scalar(x_306)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_306;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_305);
return x_340;
}
}
}
}
}
default: 
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = lean_box(13);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_5);
return x_342;
}
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_3, x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_lt(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_24 = lean_array_get(x_23, x_2, x_6);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_26 = lean_array_get(x_25, x_1, x_6);
switch (lean_obj_tag(x_26)) {
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(1);
x_30 = lean_array_push(x_5, x_29);
lean_ctor_set(x_26, 0, x_30);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_box(1);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_5);
x_16 = x_26;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_36;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_16 = x_37;
x_17 = x_12;
goto block_22;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_st_ref_get(x_9, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_39);
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
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_39, x_58);
lean_dec(x_58);
lean_dec(x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_43;
goto block_22;
}
else
{
uint8_t x_60; 
lean_free_object(x_24);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
lean_free_object(x_59);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_1, x_6);
switch (lean_obj_tag(x_65)) {
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_63);
x_68 = lean_array_push(x_5, x_65);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_68);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_63);
x_70 = lean_array_push(x_5, x_69);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_70);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
case 2:
{
uint8_t x_71; 
lean_free_object(x_61);
lean_dec(x_63);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_65, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_5);
x_16 = x_65;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_16 = x_73;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_dec(x_65);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_76 = lean_array_get(x_75, x_1, x_6);
switch (lean_obj_tag(x_76)) {
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_array_push(x_5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_16 = x_80;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_5);
x_16 = x_82;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_43;
goto block_22;
}
}
}
}
case 1:
{
uint8_t x_84; 
lean_free_object(x_59);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_61, 0);
lean_dec(x_85);
lean_ctor_set(x_61, 0, x_5);
x_16 = x_61;
x_17 = x_43;
goto block_22;
}
else
{
lean_object* x_86; 
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_5);
x_16 = x_86;
x_17 = x_43;
goto block_22;
}
}
default: 
{
lean_ctor_set(x_59, 0, x_5);
x_16 = x_59;
x_17 = x_43;
goto block_22;
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
switch (lean_obj_tag(x_87)) {
case 0:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_91 = lean_array_get(x_90, x_1, x_6);
switch (lean_obj_tag(x_91)) {
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_92 = x_91;
} else {
 lean_dec_ref(x_91);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_array_push(x_5, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_43;
goto block_22;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_5);
x_16 = x_97;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_98; 
lean_dec(x_91);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_89;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_5);
x_16 = x_98;
x_17 = x_43;
goto block_22;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
x_16 = x_100;
x_17 = x_43;
goto block_22;
}
default: 
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_16 = x_101;
x_17 = x_43;
goto block_22;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
lean_dec(x_24);
x_103 = lean_st_ref_get(x_9, x_12);
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
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_102);
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
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_102, x_121);
lean_dec(x_121);
lean_dec(x_102);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_5);
x_16 = x_123;
x_17 = x_106;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
switch (lean_obj_tag(x_124)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_129 = lean_array_get(x_128, x_1, x_6);
switch (lean_obj_tag(x_129)) {
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_130 = x_129;
} else {
 lean_dec_ref(x_129);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_126);
x_132 = lean_array_push(x_5, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_127;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_106;
goto block_22;
}
case 2:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_126);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_5);
x_16 = x_135;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_5);
x_16 = x_136;
x_17 = x_106;
goto block_22;
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_5);
x_16 = x_138;
x_17 = x_106;
goto block_22;
}
default: 
{
lean_object* x_139; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_5);
x_16 = x_139;
x_17 = x_106;
goto block_22;
}
}
}
}
}
default: 
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_24);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_24, 0);
lean_dec(x_141);
x_142 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_143 = lean_array_get(x_142, x_1, x_6);
switch (lean_obj_tag(x_143)) {
case 1:
{
uint8_t x_144; 
lean_free_object(x_24);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(1);
x_147 = lean_array_push(x_5, x_146);
lean_ctor_set(x_143, 0, x_147);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_143);
x_148 = lean_box(1);
x_149 = lean_array_push(x_5, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_12;
goto block_22;
}
}
case 2:
{
uint8_t x_151; 
lean_free_object(x_24);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
lean_ctor_set_tag(x_143, 1);
lean_ctor_set(x_143, 0, x_5);
x_16 = x_143;
x_17 = x_12;
goto block_22;
}
else
{
lean_object* x_153; 
lean_dec(x_143);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_5);
x_16 = x_153;
x_17 = x_12;
goto block_22;
}
}
default: 
{
lean_dec(x_143);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_5);
x_16 = x_24;
x_17 = x_12;
goto block_22;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_24);
x_154 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_155 = lean_array_get(x_154, x_1, x_6);
switch (lean_obj_tag(x_155)) {
case 1:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_156 = x_155;
} else {
 lean_dec_ref(x_155);
 x_156 = lean_box(0);
}
x_157 = lean_box(1);
x_158 = lean_array_push(x_5, x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_16 = x_159;
x_17 = x_12;
goto block_22;
}
case 2:
{
lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_5);
x_16 = x_161;
x_17 = x_12;
goto block_22;
}
default: 
{
lean_object* x_162; 
lean_dec(x_155);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_5);
x_16 = x_162;
x_17 = x_12;
goto block_22;
}
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_20;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_IR_ToIR_bindVar(x_11, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
x_17 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_2, x_3, x_4, x_5, x_14, x_16, x_16, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 0, x_3);
x_20 = lean_box(7);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_12);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 0, x_3);
x_24 = lean_box(7);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_31);
x_34 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_2, x_3, x_4, x_5, x_31, x_33, x_33, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
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
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_6);
x_39 = lean_box(7);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_35);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_3);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_3 = lean_unsigned_to_nat(252u);
x_4 = lean_unsigned_to_nat(37u);
x_5 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("projection of non-inductive type", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_3 = lean_unsigned_to_nat(238u);
x_4 = lean_unsigned_to_nat(10u);
x_5 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_3 = lean_unsigned_to_nat(343u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_IR_ToIR_lowerLet___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Quot", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcInv", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("axiom '", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("thm unsupported by code generator", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_3 = lean_unsigned_to_nat(342u);
x_4 = lean_unsigned_to_nat(30u);
x_5 = l_Lean_IR_ToIR_lowerLet___closed__17;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__19;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quot ", 5, 5);
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
x_1 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("induct unsupported by code generator", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_3 = lean_unsigned_to_nat(341u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l_Lean_IR_ToIR_lowerLet___closed__25;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
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
x_1 = l_Lean_IR_ToIR_lowerLet___closed__32;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__34;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__36;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_3 = lean_unsigned_to_nat(350u);
x_4 = lean_unsigned_to_nat(37u);
x_5 = l_Lean_IR_ToIR_lowerArg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_IR_ToIR_lowerLitValue(x_9);
lean_ctor_set_tag(x_7, 11);
lean_ctor_set(x_7, 0, x_10);
x_11 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_7, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_IR_ToIR_lowerLitValue(x_12);
x_14 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_14, x_3, x_4, x_5, x_6);
return x_15;
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_16, x_3, x_4, x_5, x_6);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 2);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_st_ref_get(x_3, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_20);
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
x_40 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_20, x_39);
lean_dec(x_39);
lean_dec(x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_41 = l_Lean_IR_ToIR_lowerLet___closed__2;
x_42 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_41, x_3, x_4, x_5, x_24);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
switch (lean_obj_tag(x_43)) {
case 0:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_get(x_5, x_24);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 0;
x_50 = l_Lean_Environment_find_x3f(x_48, x_18, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_52 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_51, x_3, x_4, x_5, x_47);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
if (lean_obj_tag(x_53) == 5)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 4);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_instInhabitedName;
x_57 = lean_unsigned_to_nat(0u);
x_58 = l___private_Init_GetElem_0__List_get_x21Internal___rarg(x_56, x_55, x_57);
lean_dec(x_55);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l_Lean_IR_ToIR_getCtorInfo(x_58, x_3, x_4, x_5, x_47);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_65 = lean_array_get(x_64, x_63, x_19);
lean_dec(x_19);
lean_dec(x_63);
x_66 = l_Lean_IR_ToIR_lowerProj(x_44, x_62, x_65);
lean_dec(x_62);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lean_IR_ToIR_bindVar(x_70, x_3, x_4, x_5, x_61);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_69);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_68);
lean_ctor_set(x_80, 2, x_69);
lean_ctor_set(x_80, 3, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
x_82 = !lean_is_exclusive(x_74);
if (x_82 == 0)
{
return x_74;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
lean_dec(x_1);
x_87 = l_Lean_IR_ToIR_bindErased(x_86, x_3, x_4, x_5, x_61);
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
lean_dec(x_44);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_59);
if (x_90 == 0)
{
return x_59;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_59, 0);
x_92 = lean_ctor_get(x_59, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_59);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_53);
lean_dec(x_44);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_94 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_95 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_94, x_3, x_4, x_5, x_47);
return x_95;
}
}
}
case 1:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_43);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_96 = l_Lean_IR_ToIR_lowerLet___closed__2;
x_97 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_96, x_3, x_4, x_5, x_24);
return x_97;
}
default: 
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_19);
lean_dec(x_18);
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
lean_dec(x_1);
x_99 = l_Lean_IR_ToIR_bindErased(x_98, x_3, x_4, x_5, x_24);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_100);
return x_101;
}
}
}
}
case 3:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_7, 0);
lean_inc(x_102);
switch (lean_obj_tag(x_102)) {
case 0:
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_7);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_7, 2);
x_105 = lean_ctor_get(x_7, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_7, 0);
lean_dec(x_106);
x_107 = lean_array_size(x_104);
x_108 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_104);
x_109 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_107, x_108, x_104, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_110);
lean_inc(x_2);
lean_inc(x_1);
x_112 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_110, x_3, x_4, x_5, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_st_ref_get(x_5, x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = 0;
lean_inc(x_119);
x_121 = l_Lean_Environment_find_x3f(x_119, x_102, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_119);
lean_free_object(x_115);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
x_122 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_123 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_122, x_3, x_4, x_5, x_118);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
lean_dec(x_121);
switch (lean_obj_tag(x_124)) {
case 0:
{
uint8_t x_125; 
lean_dec(x_119);
lean_free_object(x_7);
lean_dec(x_104);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_124, 0);
lean_dec(x_126);
x_127 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_128 = lean_name_eq(x_102, x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_130 = lean_name_eq(x_102, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_free_object(x_115);
x_131 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_118);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_131, 1);
x_135 = lean_ctor_get(x_131, 0);
lean_dec(x_135);
x_136 = 1;
x_137 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_138 = l_Lean_Name_toString(x_102, x_136, x_137);
lean_ctor_set_tag(x_124, 3);
lean_ctor_set(x_124, 0, x_138);
x_139 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_131, 5);
lean_ctor_set(x_131, 1, x_124);
lean_ctor_set(x_131, 0, x_139);
x_140 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_141 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_MessageData_ofFormat(x_141);
x_143 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_142, x_3, x_4, x_5, x_134);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_143;
}
else
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_131, 1);
lean_inc(x_144);
lean_dec(x_131);
x_145 = 1;
x_146 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_147 = l_Lean_Name_toString(x_102, x_145, x_146);
lean_ctor_set_tag(x_124, 3);
lean_ctor_set(x_124, 0, x_147);
x_148 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_149 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_124);
x_150 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_MessageData_ofFormat(x_151);
x_153 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_152, x_3, x_4, x_5, x_144);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_free_object(x_124);
x_154 = !lean_is_exclusive(x_131);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_155 = lean_ctor_get(x_131, 1);
x_156 = lean_ctor_get(x_131, 0);
lean_dec(x_156);
x_157 = lean_ctor_get(x_132, 0);
lean_inc(x_157);
lean_dec(x_132);
x_158 = lean_array_get_size(x_110);
x_159 = l_Lean_IR_Decl_params(x_157);
lean_dec(x_157);
x_160 = lean_array_get_size(x_159);
lean_dec(x_159);
x_161 = lean_nat_dec_lt(x_158, x_160);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = lean_nat_dec_eq(x_158, x_160);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_unsigned_to_nat(0u);
x_164 = l_Array_extract___rarg(x_110, x_163, x_160);
x_165 = l_Array_extract___rarg(x_110, x_160, x_158);
lean_dec(x_158);
lean_dec(x_110);
lean_ctor_set_tag(x_131, 6);
lean_ctor_set(x_131, 1, x_164);
lean_ctor_set(x_131, 0, x_102);
x_166 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_131, x_165, x_3, x_4, x_5, x_155);
return x_166;
}
else
{
lean_object* x_167; 
lean_dec(x_160);
lean_dec(x_158);
lean_ctor_set_tag(x_131, 6);
lean_ctor_set(x_131, 1, x_110);
lean_ctor_set(x_131, 0, x_102);
x_167 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_131, x_3, x_4, x_5, x_155);
return x_167;
}
}
else
{
lean_object* x_168; 
lean_dec(x_160);
lean_dec(x_158);
lean_ctor_set_tag(x_131, 7);
lean_ctor_set(x_131, 1, x_110);
lean_ctor_set(x_131, 0, x_102);
x_168 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_131, x_3, x_4, x_5, x_155);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_169 = lean_ctor_get(x_131, 1);
lean_inc(x_169);
lean_dec(x_131);
x_170 = lean_ctor_get(x_132, 0);
lean_inc(x_170);
lean_dec(x_132);
x_171 = lean_array_get_size(x_110);
x_172 = l_Lean_IR_Decl_params(x_170);
lean_dec(x_170);
x_173 = lean_array_get_size(x_172);
lean_dec(x_172);
x_174 = lean_nat_dec_lt(x_171, x_173);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = lean_nat_dec_eq(x_171, x_173);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_unsigned_to_nat(0u);
x_177 = l_Array_extract___rarg(x_110, x_176, x_173);
x_178 = l_Array_extract___rarg(x_110, x_173, x_171);
lean_dec(x_171);
lean_dec(x_110);
x_179 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_179, 0, x_102);
lean_ctor_set(x_179, 1, x_177);
x_180 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_179, x_178, x_3, x_4, x_5, x_169);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
lean_dec(x_171);
x_181 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_181, 0, x_102);
lean_ctor_set(x_181, 1, x_110);
x_182 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_181, x_3, x_4, x_5, x_169);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_173);
lean_dec(x_171);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_102);
lean_ctor_set(x_183, 1, x_110);
x_184 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_183, x_3, x_4, x_5, x_169);
return x_184;
}
}
}
}
else
{
lean_object* x_185; 
lean_free_object(x_124);
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_box(13);
lean_ctor_set(x_115, 0, x_185);
return x_115;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_free_object(x_124);
lean_free_object(x_115);
x_186 = l_Lean_IR_instInhabitedArg;
x_187 = lean_unsigned_to_nat(2u);
x_188 = lean_array_get(x_186, x_110, x_187);
lean_dec(x_110);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec(x_188);
x_190 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_189, x_3, x_4, x_5, x_118);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_box(0);
x_192 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_191, x_3, x_4, x_5, x_118);
return x_192;
}
}
}
else
{
lean_object* x_193; uint8_t x_194; 
lean_dec(x_124);
x_193 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_194 = lean_name_eq(x_102, x_193);
if (x_194 == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_196 = lean_name_eq(x_102, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_free_object(x_115);
x_197 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_118);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
x_201 = 1;
x_202 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_203 = l_Lean_Name_toString(x_102, x_201, x_202);
x_204 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_200)) {
 x_206 = lean_alloc_ctor(5, 2, 0);
} else {
 x_206 = x_200;
 lean_ctor_set_tag(x_206, 5);
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_208 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_MessageData_ofFormat(x_208);
x_210 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_209, x_3, x_4, x_5, x_199);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_211 = lean_ctor_get(x_197, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_212 = x_197;
} else {
 lean_dec_ref(x_197);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_198, 0);
lean_inc(x_213);
lean_dec(x_198);
x_214 = lean_array_get_size(x_110);
x_215 = l_Lean_IR_Decl_params(x_213);
lean_dec(x_213);
x_216 = lean_array_get_size(x_215);
lean_dec(x_215);
x_217 = lean_nat_dec_lt(x_214, x_216);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = lean_nat_dec_eq(x_214, x_216);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_unsigned_to_nat(0u);
x_220 = l_Array_extract___rarg(x_110, x_219, x_216);
x_221 = l_Array_extract___rarg(x_110, x_216, x_214);
lean_dec(x_214);
lean_dec(x_110);
if (lean_is_scalar(x_212)) {
 x_222 = lean_alloc_ctor(6, 2, 0);
} else {
 x_222 = x_212;
 lean_ctor_set_tag(x_222, 6);
}
lean_ctor_set(x_222, 0, x_102);
lean_ctor_set(x_222, 1, x_220);
x_223 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_222, x_221, x_3, x_4, x_5, x_211);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_216);
lean_dec(x_214);
if (lean_is_scalar(x_212)) {
 x_224 = lean_alloc_ctor(6, 2, 0);
} else {
 x_224 = x_212;
 lean_ctor_set_tag(x_224, 6);
}
lean_ctor_set(x_224, 0, x_102);
lean_ctor_set(x_224, 1, x_110);
x_225 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_224, x_3, x_4, x_5, x_211);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_216);
lean_dec(x_214);
if (lean_is_scalar(x_212)) {
 x_226 = lean_alloc_ctor(7, 2, 0);
} else {
 x_226 = x_212;
 lean_ctor_set_tag(x_226, 7);
}
lean_ctor_set(x_226, 0, x_102);
lean_ctor_set(x_226, 1, x_110);
x_227 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_226, x_3, x_4, x_5, x_211);
return x_227;
}
}
}
else
{
lean_object* x_228; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = lean_box(13);
lean_ctor_set(x_115, 0, x_228);
return x_115;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_free_object(x_115);
x_229 = l_Lean_IR_instInhabitedArg;
x_230 = lean_unsigned_to_nat(2u);
x_231 = lean_array_get(x_229, x_110, x_230);
lean_dec(x_110);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec(x_231);
x_233 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_232, x_3, x_4, x_5, x_118);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_box(0);
x_235 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_234, x_3, x_4, x_5, x_118);
return x_235;
}
}
}
}
case 2:
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_124);
lean_dec(x_119);
lean_free_object(x_115);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
x_236 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_237 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_236, x_3, x_4, x_5, x_118);
return x_237;
}
case 4:
{
uint8_t x_238; 
lean_dec(x_119);
lean_free_object(x_115);
lean_free_object(x_7);
lean_dec(x_104);
x_238 = !lean_is_exclusive(x_124);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_124, 0);
lean_dec(x_239);
x_240 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_241 = lean_name_eq(x_102, x_240);
if (x_241 == 0)
{
uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_1);
x_242 = 1;
x_243 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_244 = l_Lean_Name_toString(x_102, x_242, x_243);
lean_ctor_set_tag(x_124, 3);
lean_ctor_set(x_124, 0, x_244);
x_245 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_246 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_124);
x_247 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_248 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_MessageData_ofFormat(x_248);
x_250 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_249, x_3, x_4, x_5, x_118);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_free_object(x_124);
x_251 = l_Lean_IR_instInhabitedArg;
x_252 = lean_unsigned_to_nat(2u);
x_253 = lean_array_get(x_251, x_110, x_252);
lean_dec(x_110);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec(x_253);
x_255 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_254, x_3, x_4, x_5, x_118);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_box(0);
x_257 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_256, x_3, x_4, x_5, x_118);
return x_257;
}
}
}
else
{
lean_object* x_258; uint8_t x_259; 
lean_dec(x_124);
x_258 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_259 = lean_name_eq(x_102, x_258);
if (x_259 == 0)
{
uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_1);
x_260 = 1;
x_261 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_262 = l_Lean_Name_toString(x_102, x_260, x_261);
x_263 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_264 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_265 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
x_266 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_267 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Lean_MessageData_ofFormat(x_267);
x_269 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_268, x_3, x_4, x_5, x_118);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = l_Lean_IR_instInhabitedArg;
x_271 = lean_unsigned_to_nat(2u);
x_272 = lean_array_get(x_270, x_110, x_271);
lean_dec(x_110);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec(x_272);
x_274 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_273, x_3, x_4, x_5, x_118);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_box(0);
x_276 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_275, x_3, x_4, x_5, x_118);
return x_276;
}
}
}
}
case 5:
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_124);
lean_dec(x_119);
lean_free_object(x_115);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
x_277 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_278 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_277, x_3, x_4, x_5, x_118);
return x_278;
}
case 6:
{
lean_object* x_279; uint8_t x_280; 
lean_free_object(x_115);
x_279 = lean_ctor_get(x_124, 0);
lean_inc(x_279);
lean_dec(x_124);
x_280 = l_Lean_isExtern(x_119, x_102);
if (x_280 == 0)
{
lean_object* x_281; 
lean_dec(x_110);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_281 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_118);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
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
x_286 = lean_ctor_get(x_279, 3);
lean_inc(x_286);
lean_dec(x_279);
x_287 = lean_array_get_size(x_104);
x_288 = l_Array_extract___rarg(x_104, x_286, x_287);
lean_dec(x_287);
lean_dec(x_104);
x_289 = lean_array_get_size(x_285);
x_290 = lean_unsigned_to_nat(0u);
x_291 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_291);
lean_ctor_set(x_7, 1, x_289);
lean_ctor_set(x_7, 0, x_290);
x_292 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_293 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2(x_285, x_288, x_7, x_7, x_292, x_290, lean_box(0), lean_box(0), x_3, x_4, x_5, x_283);
lean_dec(x_7);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_284, x_285, x_288, x_294, x_3, x_4, x_5, x_295);
lean_dec(x_288);
lean_dec(x_285);
return x_296;
}
else
{
uint8_t x_297; 
lean_dec(x_279);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_281);
if (x_297 == 0)
{
return x_281;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_281, 0);
x_299 = lean_ctor_get(x_281, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_281);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
else
{
lean_object* x_301; 
lean_dec(x_279);
lean_free_object(x_7);
lean_dec(x_104);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_110);
lean_inc(x_2);
lean_inc(x_1);
x_301 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_110, x_3, x_4, x_5, x_118);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_304, 0, x_102);
lean_ctor_set(x_304, 1, x_110);
x_305 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_304, x_3, x_4, x_5, x_303);
return x_305;
}
else
{
uint8_t x_306; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_301);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_301, 0);
lean_dec(x_307);
x_308 = lean_ctor_get(x_302, 0);
lean_inc(x_308);
lean_dec(x_302);
lean_ctor_set(x_301, 0, x_308);
return x_301;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_301, 1);
lean_inc(x_309);
lean_dec(x_301);
x_310 = lean_ctor_get(x_302, 0);
lean_inc(x_310);
lean_dec(x_302);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_301);
if (x_312 == 0)
{
return x_301;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_301, 0);
x_314 = lean_ctor_get(x_301, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_301);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
}
case 7:
{
uint8_t x_316; 
lean_dec(x_119);
lean_free_object(x_115);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
x_316 = !lean_is_exclusive(x_124);
if (x_316 == 0)
{
lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_317 = lean_ctor_get(x_124, 0);
lean_dec(x_317);
x_318 = 1;
x_319 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_320 = l_Lean_Name_toString(x_102, x_318, x_319);
lean_ctor_set_tag(x_124, 3);
lean_ctor_set(x_124, 0, x_320);
x_321 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_322 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_124);
x_323 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_324 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = l_Lean_MessageData_ofFormat(x_324);
x_326 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_325, x_3, x_4, x_5, x_118);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_326;
}
else
{
uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_124);
x_327 = 1;
x_328 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_329 = l_Lean_Name_toString(x_102, x_327, x_328);
x_330 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_330, 0, x_329);
x_331 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_332 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_330);
x_333 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_334 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_MessageData_ofFormat(x_334);
x_336 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_335, x_3, x_4, x_5, x_118);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_336;
}
}
default: 
{
lean_object* x_337; 
lean_dec(x_124);
lean_dec(x_119);
lean_free_object(x_115);
lean_free_object(x_7);
lean_dec(x_104);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_110);
lean_inc(x_2);
lean_inc(x_1);
x_337 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_110, x_3, x_4, x_5, x_118);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_340, 0, x_102);
lean_ctor_set(x_340, 1, x_110);
x_341 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_340, x_3, x_4, x_5, x_339);
return x_341;
}
else
{
uint8_t x_342; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_342 = !lean_is_exclusive(x_337);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_337, 0);
lean_dec(x_343);
x_344 = lean_ctor_get(x_338, 0);
lean_inc(x_344);
lean_dec(x_338);
lean_ctor_set(x_337, 0, x_344);
return x_337;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_337, 1);
lean_inc(x_345);
lean_dec(x_337);
x_346 = lean_ctor_get(x_338, 0);
lean_inc(x_346);
lean_dec(x_338);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_337);
if (x_348 == 0)
{
return x_337;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_337, 0);
x_350 = lean_ctor_get(x_337, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_337);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_115, 0);
x_353 = lean_ctor_get(x_115, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_115);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
lean_dec(x_352);
x_355 = 0;
lean_inc(x_354);
x_356 = l_Lean_Environment_find_x3f(x_354, x_102, x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_354);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
x_357 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_358 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_357, x_3, x_4, x_5, x_353);
return x_358;
}
else
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_356, 0);
lean_inc(x_359);
lean_dec(x_356);
switch (lean_obj_tag(x_359)) {
case 0:
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; 
lean_dec(x_354);
lean_free_object(x_7);
lean_dec(x_104);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 x_360 = x_359;
} else {
 lean_dec_ref(x_359);
 x_360 = lean_box(0);
}
x_361 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_362 = lean_name_eq(x_102, x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; 
x_363 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_364 = lean_name_eq(x_102, x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_353);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_368 = x_365;
} else {
 lean_dec_ref(x_365);
 x_368 = lean_box(0);
}
x_369 = 1;
x_370 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_371 = l_Lean_Name_toString(x_102, x_369, x_370);
if (lean_is_scalar(x_360)) {
 x_372 = lean_alloc_ctor(3, 1, 0);
} else {
 x_372 = x_360;
 lean_ctor_set_tag(x_372, 3);
}
lean_ctor_set(x_372, 0, x_371);
x_373 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_368)) {
 x_374 = lean_alloc_ctor(5, 2, 0);
} else {
 x_374 = x_368;
 lean_ctor_set_tag(x_374, 5);
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
x_375 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_376 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
x_377 = l_Lean_MessageData_ofFormat(x_376);
x_378 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_377, x_3, x_4, x_5, x_367);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
lean_dec(x_360);
x_379 = lean_ctor_get(x_365, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_380 = x_365;
} else {
 lean_dec_ref(x_365);
 x_380 = lean_box(0);
}
x_381 = lean_ctor_get(x_366, 0);
lean_inc(x_381);
lean_dec(x_366);
x_382 = lean_array_get_size(x_110);
x_383 = l_Lean_IR_Decl_params(x_381);
lean_dec(x_381);
x_384 = lean_array_get_size(x_383);
lean_dec(x_383);
x_385 = lean_nat_dec_lt(x_382, x_384);
if (x_385 == 0)
{
uint8_t x_386; 
x_386 = lean_nat_dec_eq(x_382, x_384);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_unsigned_to_nat(0u);
x_388 = l_Array_extract___rarg(x_110, x_387, x_384);
x_389 = l_Array_extract___rarg(x_110, x_384, x_382);
lean_dec(x_382);
lean_dec(x_110);
if (lean_is_scalar(x_380)) {
 x_390 = lean_alloc_ctor(6, 2, 0);
} else {
 x_390 = x_380;
 lean_ctor_set_tag(x_390, 6);
}
lean_ctor_set(x_390, 0, x_102);
lean_ctor_set(x_390, 1, x_388);
x_391 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_390, x_389, x_3, x_4, x_5, x_379);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_384);
lean_dec(x_382);
if (lean_is_scalar(x_380)) {
 x_392 = lean_alloc_ctor(6, 2, 0);
} else {
 x_392 = x_380;
 lean_ctor_set_tag(x_392, 6);
}
lean_ctor_set(x_392, 0, x_102);
lean_ctor_set(x_392, 1, x_110);
x_393 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_392, x_3, x_4, x_5, x_379);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_384);
lean_dec(x_382);
if (lean_is_scalar(x_380)) {
 x_394 = lean_alloc_ctor(7, 2, 0);
} else {
 x_394 = x_380;
 lean_ctor_set_tag(x_394, 7);
}
lean_ctor_set(x_394, 0, x_102);
lean_ctor_set(x_394, 1, x_110);
x_395 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_394, x_3, x_4, x_5, x_379);
return x_395;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_360);
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_396 = lean_box(13);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_353);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_360);
x_398 = l_Lean_IR_instInhabitedArg;
x_399 = lean_unsigned_to_nat(2u);
x_400 = lean_array_get(x_398, x_110, x_399);
lean_dec(x_110);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec(x_400);
x_402 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_401, x_3, x_4, x_5, x_353);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_box(0);
x_404 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_403, x_3, x_4, x_5, x_353);
return x_404;
}
}
}
case 2:
{
lean_object* x_405; lean_object* x_406; 
lean_dec(x_359);
lean_dec(x_354);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
x_405 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_406 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_405, x_3, x_4, x_5, x_353);
return x_406;
}
case 4:
{
lean_object* x_407; lean_object* x_408; uint8_t x_409; 
lean_dec(x_354);
lean_free_object(x_7);
lean_dec(x_104);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 x_407 = x_359;
} else {
 lean_dec_ref(x_359);
 x_407 = lean_box(0);
}
x_408 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_409 = lean_name_eq(x_102, x_408);
if (x_409 == 0)
{
uint8_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_1);
x_410 = 1;
x_411 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_412 = l_Lean_Name_toString(x_102, x_410, x_411);
if (lean_is_scalar(x_407)) {
 x_413 = lean_alloc_ctor(3, 1, 0);
} else {
 x_413 = x_407;
 lean_ctor_set_tag(x_413, 3);
}
lean_ctor_set(x_413, 0, x_412);
x_414 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_415 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
x_416 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_417 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
x_418 = l_Lean_MessageData_ofFormat(x_417);
x_419 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_418, x_3, x_4, x_5, x_353);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_407);
x_420 = l_Lean_IR_instInhabitedArg;
x_421 = lean_unsigned_to_nat(2u);
x_422 = lean_array_get(x_420, x_110, x_421);
lean_dec(x_110);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec(x_422);
x_424 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_423, x_3, x_4, x_5, x_353);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_box(0);
x_426 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_425, x_3, x_4, x_5, x_353);
return x_426;
}
}
}
case 5:
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_359);
lean_dec(x_354);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
x_427 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_428 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_427, x_3, x_4, x_5, x_353);
return x_428;
}
case 6:
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_ctor_get(x_359, 0);
lean_inc(x_429);
lean_dec(x_359);
x_430 = l_Lean_isExtern(x_354, x_102);
if (x_430 == 0)
{
lean_object* x_431; 
lean_dec(x_110);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_431 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_353);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
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
x_436 = lean_ctor_get(x_429, 3);
lean_inc(x_436);
lean_dec(x_429);
x_437 = lean_array_get_size(x_104);
x_438 = l_Array_extract___rarg(x_104, x_436, x_437);
lean_dec(x_437);
lean_dec(x_104);
x_439 = lean_array_get_size(x_435);
x_440 = lean_unsigned_to_nat(0u);
x_441 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_441);
lean_ctor_set(x_7, 1, x_439);
lean_ctor_set(x_7, 0, x_440);
x_442 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_443 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2(x_435, x_438, x_7, x_7, x_442, x_440, lean_box(0), lean_box(0), x_3, x_4, x_5, x_433);
lean_dec(x_7);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_434, x_435, x_438, x_444, x_3, x_4, x_5, x_445);
lean_dec(x_438);
lean_dec(x_435);
return x_446;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_429);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_447 = lean_ctor_get(x_431, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_431, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_449 = x_431;
} else {
 lean_dec_ref(x_431);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
}
else
{
lean_object* x_451; 
lean_dec(x_429);
lean_free_object(x_7);
lean_dec(x_104);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_110);
lean_inc(x_2);
lean_inc(x_1);
x_451 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_110, x_3, x_4, x_5, x_353);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_454, 0, x_102);
lean_ctor_set(x_454, 1, x_110);
x_455 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_454, x_3, x_4, x_5, x_453);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_457 = x_451;
} else {
 lean_dec_ref(x_451);
 x_457 = lean_box(0);
}
x_458 = lean_ctor_get(x_452, 0);
lean_inc(x_458);
lean_dec(x_452);
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_456);
return x_459;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_460 = lean_ctor_get(x_451, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_451, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_462 = x_451;
} else {
 lean_dec_ref(x_451);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
}
}
case 7:
{
lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_354);
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 x_464 = x_359;
} else {
 lean_dec_ref(x_359);
 x_464 = lean_box(0);
}
x_465 = 1;
x_466 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_467 = l_Lean_Name_toString(x_102, x_465, x_466);
if (lean_is_scalar(x_464)) {
 x_468 = lean_alloc_ctor(3, 1, 0);
} else {
 x_468 = x_464;
 lean_ctor_set_tag(x_468, 3);
}
lean_ctor_set(x_468, 0, x_467);
x_469 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_470 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_468);
x_471 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_472 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
x_473 = l_Lean_MessageData_ofFormat(x_472);
x_474 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_473, x_3, x_4, x_5, x_353);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_474;
}
default: 
{
lean_object* x_475; 
lean_dec(x_359);
lean_dec(x_354);
lean_free_object(x_7);
lean_dec(x_104);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_110);
lean_inc(x_2);
lean_inc(x_1);
x_475 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_110, x_3, x_4, x_5, x_353);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_478, 0, x_102);
lean_ctor_set(x_478, 1, x_110);
x_479 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_478, x_3, x_4, x_5, x_477);
return x_479;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_480 = lean_ctor_get(x_475, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_481 = x_475;
} else {
 lean_dec_ref(x_475);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_476, 0);
lean_inc(x_482);
lean_dec(x_476);
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_480);
return x_483;
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_484 = lean_ctor_get(x_475, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_475, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_486 = x_475;
} else {
 lean_dec_ref(x_475);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 2, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_485);
return x_487;
}
}
}
}
}
}
else
{
uint8_t x_488; 
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_488 = !lean_is_exclusive(x_112);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_112, 0);
lean_dec(x_489);
x_490 = lean_ctor_get(x_113, 0);
lean_inc(x_490);
lean_dec(x_113);
lean_ctor_set(x_112, 0, x_490);
return x_112;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_112, 1);
lean_inc(x_491);
lean_dec(x_112);
x_492 = lean_ctor_get(x_113, 0);
lean_inc(x_492);
lean_dec(x_113);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
return x_493;
}
}
}
else
{
uint8_t x_494; 
lean_dec(x_110);
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_494 = !lean_is_exclusive(x_112);
if (x_494 == 0)
{
return x_112;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_112, 0);
x_496 = lean_ctor_get(x_112, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_112);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
}
}
else
{
uint8_t x_498; 
lean_free_object(x_7);
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_498 = !lean_is_exclusive(x_109);
if (x_498 == 0)
{
return x_109;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_109, 0);
x_500 = lean_ctor_get(x_109, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_109);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
else
{
lean_object* x_502; size_t x_503; size_t x_504; lean_object* x_505; 
x_502 = lean_ctor_get(x_7, 2);
lean_inc(x_502);
lean_dec(x_7);
x_503 = lean_array_size(x_502);
x_504 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_502);
x_505 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_503, x_504, x_502, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_506);
lean_inc(x_2);
lean_inc(x_1);
x_508 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_506, x_3, x_4, x_5, x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; lean_object* x_517; 
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_st_ref_get(x_5, x_510);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_514 = x_511;
} else {
 lean_dec_ref(x_511);
 x_514 = lean_box(0);
}
x_515 = lean_ctor_get(x_512, 0);
lean_inc(x_515);
lean_dec(x_512);
x_516 = 0;
lean_inc(x_515);
x_517 = l_Lean_Environment_find_x3f(x_515, x_102, x_516);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; 
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_506);
lean_dec(x_502);
lean_dec(x_2);
lean_dec(x_1);
x_518 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_519 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_518, x_3, x_4, x_5, x_513);
return x_519;
}
else
{
lean_object* x_520; 
x_520 = lean_ctor_get(x_517, 0);
lean_inc(x_520);
lean_dec(x_517);
switch (lean_obj_tag(x_520)) {
case 0:
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; 
lean_dec(x_515);
lean_dec(x_502);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 x_521 = x_520;
} else {
 lean_dec_ref(x_520);
 x_521 = lean_box(0);
}
x_522 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_523 = lean_name_eq(x_102, x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; 
x_524 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_525 = lean_name_eq(x_102, x_524);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; 
lean_dec(x_514);
x_526 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_513);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_506);
lean_dec(x_2);
lean_dec(x_1);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_529 = x_526;
} else {
 lean_dec_ref(x_526);
 x_529 = lean_box(0);
}
x_530 = 1;
x_531 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_532 = l_Lean_Name_toString(x_102, x_530, x_531);
if (lean_is_scalar(x_521)) {
 x_533 = lean_alloc_ctor(3, 1, 0);
} else {
 x_533 = x_521;
 lean_ctor_set_tag(x_533, 3);
}
lean_ctor_set(x_533, 0, x_532);
x_534 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_529)) {
 x_535 = lean_alloc_ctor(5, 2, 0);
} else {
 x_535 = x_529;
 lean_ctor_set_tag(x_535, 5);
}
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_533);
x_536 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_537 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
x_538 = l_Lean_MessageData_ofFormat(x_537);
x_539 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_538, x_3, x_4, x_5, x_528);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
lean_dec(x_521);
x_540 = lean_ctor_get(x_526, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_541 = x_526;
} else {
 lean_dec_ref(x_526);
 x_541 = lean_box(0);
}
x_542 = lean_ctor_get(x_527, 0);
lean_inc(x_542);
lean_dec(x_527);
x_543 = lean_array_get_size(x_506);
x_544 = l_Lean_IR_Decl_params(x_542);
lean_dec(x_542);
x_545 = lean_array_get_size(x_544);
lean_dec(x_544);
x_546 = lean_nat_dec_lt(x_543, x_545);
if (x_546 == 0)
{
uint8_t x_547; 
x_547 = lean_nat_dec_eq(x_543, x_545);
if (x_547 == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_548 = lean_unsigned_to_nat(0u);
x_549 = l_Array_extract___rarg(x_506, x_548, x_545);
x_550 = l_Array_extract___rarg(x_506, x_545, x_543);
lean_dec(x_543);
lean_dec(x_506);
if (lean_is_scalar(x_541)) {
 x_551 = lean_alloc_ctor(6, 2, 0);
} else {
 x_551 = x_541;
 lean_ctor_set_tag(x_551, 6);
}
lean_ctor_set(x_551, 0, x_102);
lean_ctor_set(x_551, 1, x_549);
x_552 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_551, x_550, x_3, x_4, x_5, x_540);
return x_552;
}
else
{
lean_object* x_553; lean_object* x_554; 
lean_dec(x_545);
lean_dec(x_543);
if (lean_is_scalar(x_541)) {
 x_553 = lean_alloc_ctor(6, 2, 0);
} else {
 x_553 = x_541;
 lean_ctor_set_tag(x_553, 6);
}
lean_ctor_set(x_553, 0, x_102);
lean_ctor_set(x_553, 1, x_506);
x_554 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_553, x_3, x_4, x_5, x_540);
return x_554;
}
}
else
{
lean_object* x_555; lean_object* x_556; 
lean_dec(x_545);
lean_dec(x_543);
if (lean_is_scalar(x_541)) {
 x_555 = lean_alloc_ctor(7, 2, 0);
} else {
 x_555 = x_541;
 lean_ctor_set_tag(x_555, 7);
}
lean_ctor_set(x_555, 0, x_102);
lean_ctor_set(x_555, 1, x_506);
x_556 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_555, x_3, x_4, x_5, x_540);
return x_556;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; 
lean_dec(x_521);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_557 = lean_box(13);
if (lean_is_scalar(x_514)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_514;
}
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_513);
return x_558;
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_521);
lean_dec(x_514);
x_559 = l_Lean_IR_instInhabitedArg;
x_560 = lean_unsigned_to_nat(2u);
x_561 = lean_array_get(x_559, x_506, x_560);
lean_dec(x_506);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
lean_dec(x_561);
x_563 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_562, x_3, x_4, x_5, x_513);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; 
x_564 = lean_box(0);
x_565 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_564, x_3, x_4, x_5, x_513);
return x_565;
}
}
}
case 2:
{
lean_object* x_566; lean_object* x_567; 
lean_dec(x_520);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_506);
lean_dec(x_502);
lean_dec(x_2);
lean_dec(x_1);
x_566 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_567 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_566, x_3, x_4, x_5, x_513);
return x_567;
}
case 4:
{
lean_object* x_568; lean_object* x_569; uint8_t x_570; 
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_502);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 x_568 = x_520;
} else {
 lean_dec_ref(x_520);
 x_568 = lean_box(0);
}
x_569 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_570 = lean_name_eq(x_102, x_569);
if (x_570 == 0)
{
uint8_t x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_506);
lean_dec(x_2);
lean_dec(x_1);
x_571 = 1;
x_572 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_573 = l_Lean_Name_toString(x_102, x_571, x_572);
if (lean_is_scalar(x_568)) {
 x_574 = lean_alloc_ctor(3, 1, 0);
} else {
 x_574 = x_568;
 lean_ctor_set_tag(x_574, 3);
}
lean_ctor_set(x_574, 0, x_573);
x_575 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_576 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_574);
x_577 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_578 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
x_579 = l_Lean_MessageData_ofFormat(x_578);
x_580 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_579, x_3, x_4, x_5, x_513);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_580;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_568);
x_581 = l_Lean_IR_instInhabitedArg;
x_582 = lean_unsigned_to_nat(2u);
x_583 = lean_array_get(x_581, x_506, x_582);
lean_dec(x_506);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
lean_dec(x_583);
x_585 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_584, x_3, x_4, x_5, x_513);
return x_585;
}
else
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_box(0);
x_587 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_586, x_3, x_4, x_5, x_513);
return x_587;
}
}
}
case 5:
{
lean_object* x_588; lean_object* x_589; 
lean_dec(x_520);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_506);
lean_dec(x_502);
lean_dec(x_2);
lean_dec(x_1);
x_588 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_589 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_588, x_3, x_4, x_5, x_513);
return x_589;
}
case 6:
{
lean_object* x_590; uint8_t x_591; 
lean_dec(x_514);
x_590 = lean_ctor_get(x_520, 0);
lean_inc(x_590);
lean_dec(x_520);
x_591 = l_Lean_isExtern(x_515, x_102);
if (x_591 == 0)
{
lean_object* x_592; 
lean_dec(x_506);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_592 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_513);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_ctor_get(x_593, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_593, 1);
lean_inc(x_596);
lean_dec(x_593);
x_597 = lean_ctor_get(x_590, 3);
lean_inc(x_597);
lean_dec(x_590);
x_598 = lean_array_get_size(x_502);
x_599 = l_Array_extract___rarg(x_502, x_597, x_598);
lean_dec(x_598);
lean_dec(x_502);
x_600 = lean_array_get_size(x_596);
x_601 = lean_unsigned_to_nat(0u);
x_602 = lean_unsigned_to_nat(1u);
x_603 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_600);
lean_ctor_set(x_603, 2, x_602);
x_604 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_605 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2(x_596, x_599, x_603, x_603, x_604, x_601, lean_box(0), lean_box(0), x_3, x_4, x_5, x_594);
lean_dec(x_603);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
x_608 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_595, x_596, x_599, x_606, x_3, x_4, x_5, x_607);
lean_dec(x_599);
lean_dec(x_596);
return x_608;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_590);
lean_dec(x_502);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_609 = lean_ctor_get(x_592, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_592, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_611 = x_592;
} else {
 lean_dec_ref(x_592);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
else
{
lean_object* x_613; 
lean_dec(x_590);
lean_dec(x_502);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_506);
lean_inc(x_2);
lean_inc(x_1);
x_613 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_506, x_3, x_4, x_5, x_513);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_616, 0, x_102);
lean_ctor_set(x_616, 1, x_506);
x_617 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_616, x_3, x_4, x_5, x_615);
return x_617;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_618 = lean_ctor_get(x_613, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_619 = x_613;
} else {
 lean_dec_ref(x_613);
 x_619 = lean_box(0);
}
x_620 = lean_ctor_get(x_614, 0);
lean_inc(x_620);
lean_dec(x_614);
if (lean_is_scalar(x_619)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_619;
}
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_618);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_622 = lean_ctor_get(x_613, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_613, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_624 = x_613;
} else {
 lean_dec_ref(x_613);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_623);
return x_625;
}
}
}
case 7:
{
lean_object* x_626; uint8_t x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_506);
lean_dec(x_502);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 x_626 = x_520;
} else {
 lean_dec_ref(x_520);
 x_626 = lean_box(0);
}
x_627 = 1;
x_628 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_629 = l_Lean_Name_toString(x_102, x_627, x_628);
if (lean_is_scalar(x_626)) {
 x_630 = lean_alloc_ctor(3, 1, 0);
} else {
 x_630 = x_626;
 lean_ctor_set_tag(x_630, 3);
}
lean_ctor_set(x_630, 0, x_629);
x_631 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_632 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_630);
x_633 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_634 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
x_635 = l_Lean_MessageData_ofFormat(x_634);
x_636 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_635, x_3, x_4, x_5, x_513);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_636;
}
default: 
{
lean_object* x_637; 
lean_dec(x_520);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_502);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_506);
lean_inc(x_2);
lean_inc(x_1);
x_637 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_506, x_3, x_4, x_5, x_513);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_640 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_640, 0, x_102);
lean_ctor_set(x_640, 1, x_506);
x_641 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_640, x_3, x_4, x_5, x_639);
return x_641;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_642 = lean_ctor_get(x_637, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_643 = x_637;
} else {
 lean_dec_ref(x_637);
 x_643 = lean_box(0);
}
x_644 = lean_ctor_get(x_638, 0);
lean_inc(x_644);
lean_dec(x_638);
if (lean_is_scalar(x_643)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_643;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_642);
return x_645;
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_646 = lean_ctor_get(x_637, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_637, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_648 = x_637;
} else {
 lean_dec_ref(x_637);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
}
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_506);
lean_dec(x_502);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_650 = lean_ctor_get(x_508, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_651 = x_508;
} else {
 lean_dec_ref(x_508);
 x_651 = lean_box(0);
}
x_652 = lean_ctor_get(x_509, 0);
lean_inc(x_652);
lean_dec(x_509);
if (lean_is_scalar(x_651)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_651;
}
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_650);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_506);
lean_dec(x_502);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_654 = lean_ctor_get(x_508, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_508, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_656 = x_508;
} else {
 lean_dec_ref(x_508);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(1, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_654);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_502);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_658 = lean_ctor_get(x_505, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_505, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_660 = x_505;
} else {
 lean_dec_ref(x_505);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_658);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
}
case 1:
{
lean_object* x_662; 
x_662 = lean_ctor_get(x_102, 0);
lean_inc(x_662);
switch (lean_obj_tag(x_662)) {
case 0:
{
uint8_t x_663; 
x_663 = !lean_is_exclusive(x_7);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; size_t x_667; size_t x_668; lean_object* x_669; 
x_664 = lean_ctor_get(x_7, 2);
x_665 = lean_ctor_get(x_7, 1);
lean_dec(x_665);
x_666 = lean_ctor_get(x_7, 0);
lean_dec(x_666);
x_667 = lean_array_size(x_664);
x_668 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_664);
x_669 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_667, x_668, x_664, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_670);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_672 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_670, x_3, x_4, x_5, x_671);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; 
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = lean_st_ref_get(x_5, x_674);
x_676 = !lean_is_exclusive(x_675);
if (x_676 == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; lean_object* x_681; 
x_677 = lean_ctor_get(x_675, 0);
x_678 = lean_ctor_get(x_675, 1);
x_679 = lean_ctor_get(x_677, 0);
lean_inc(x_679);
lean_dec(x_677);
x_680 = 0;
lean_inc(x_102);
lean_inc(x_679);
x_681 = l_Lean_Environment_find_x3f(x_679, x_102, x_680);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; 
lean_dec(x_679);
lean_free_object(x_675);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_682 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_683 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_682, x_3, x_4, x_5, x_678);
return x_683;
}
else
{
lean_object* x_684; 
x_684 = lean_ctor_get(x_681, 0);
lean_inc(x_684);
lean_dec(x_681);
switch (lean_obj_tag(x_684)) {
case 0:
{
uint8_t x_685; 
lean_dec(x_679);
lean_free_object(x_7);
lean_dec(x_664);
x_685 = !lean_is_exclusive(x_684);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_686 = lean_ctor_get(x_684, 0);
lean_dec(x_686);
x_687 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_688 = lean_name_eq(x_102, x_687);
if (x_688 == 0)
{
lean_object* x_689; uint8_t x_690; 
x_689 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_690 = lean_name_eq(x_102, x_689);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; 
lean_free_object(x_675);
lean_inc(x_102);
x_691 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_678);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
if (lean_obj_tag(x_692) == 0)
{
uint8_t x_693; 
lean_dec(x_670);
lean_dec(x_2);
lean_dec(x_1);
x_693 = !lean_is_exclusive(x_691);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; uint8_t x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_694 = lean_ctor_get(x_691, 1);
x_695 = lean_ctor_get(x_691, 0);
lean_dec(x_695);
x_696 = 1;
x_697 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_698 = l_Lean_Name_toString(x_102, x_696, x_697);
lean_ctor_set_tag(x_684, 3);
lean_ctor_set(x_684, 0, x_698);
x_699 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_691, 5);
lean_ctor_set(x_691, 1, x_684);
lean_ctor_set(x_691, 0, x_699);
x_700 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_701 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_701, 0, x_691);
lean_ctor_set(x_701, 1, x_700);
x_702 = l_Lean_MessageData_ofFormat(x_701);
x_703 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_702, x_3, x_4, x_5, x_694);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_703;
}
else
{
lean_object* x_704; uint8_t x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_704 = lean_ctor_get(x_691, 1);
lean_inc(x_704);
lean_dec(x_691);
x_705 = 1;
x_706 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_707 = l_Lean_Name_toString(x_102, x_705, x_706);
lean_ctor_set_tag(x_684, 3);
lean_ctor_set(x_684, 0, x_707);
x_708 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_709 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_709, 0, x_708);
lean_ctor_set(x_709, 1, x_684);
x_710 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_711 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
x_712 = l_Lean_MessageData_ofFormat(x_711);
x_713 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_712, x_3, x_4, x_5, x_704);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_713;
}
}
else
{
uint8_t x_714; 
lean_free_object(x_684);
x_714 = !lean_is_exclusive(x_691);
if (x_714 == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; 
x_715 = lean_ctor_get(x_691, 1);
x_716 = lean_ctor_get(x_691, 0);
lean_dec(x_716);
x_717 = lean_ctor_get(x_692, 0);
lean_inc(x_717);
lean_dec(x_692);
x_718 = lean_array_get_size(x_670);
x_719 = l_Lean_IR_Decl_params(x_717);
lean_dec(x_717);
x_720 = lean_array_get_size(x_719);
lean_dec(x_719);
x_721 = lean_nat_dec_lt(x_718, x_720);
if (x_721 == 0)
{
uint8_t x_722; 
x_722 = lean_nat_dec_eq(x_718, x_720);
if (x_722 == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_723 = lean_unsigned_to_nat(0u);
x_724 = l_Array_extract___rarg(x_670, x_723, x_720);
x_725 = l_Array_extract___rarg(x_670, x_720, x_718);
lean_dec(x_718);
lean_dec(x_670);
lean_ctor_set_tag(x_691, 6);
lean_ctor_set(x_691, 1, x_724);
lean_ctor_set(x_691, 0, x_102);
x_726 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_691, x_725, x_3, x_4, x_5, x_715);
return x_726;
}
else
{
lean_object* x_727; 
lean_dec(x_720);
lean_dec(x_718);
lean_ctor_set_tag(x_691, 6);
lean_ctor_set(x_691, 1, x_670);
lean_ctor_set(x_691, 0, x_102);
x_727 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_691, x_3, x_4, x_5, x_715);
return x_727;
}
}
else
{
lean_object* x_728; 
lean_dec(x_720);
lean_dec(x_718);
lean_ctor_set_tag(x_691, 7);
lean_ctor_set(x_691, 1, x_670);
lean_ctor_set(x_691, 0, x_102);
x_728 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_691, x_3, x_4, x_5, x_715);
return x_728;
}
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; 
x_729 = lean_ctor_get(x_691, 1);
lean_inc(x_729);
lean_dec(x_691);
x_730 = lean_ctor_get(x_692, 0);
lean_inc(x_730);
lean_dec(x_692);
x_731 = lean_array_get_size(x_670);
x_732 = l_Lean_IR_Decl_params(x_730);
lean_dec(x_730);
x_733 = lean_array_get_size(x_732);
lean_dec(x_732);
x_734 = lean_nat_dec_lt(x_731, x_733);
if (x_734 == 0)
{
uint8_t x_735; 
x_735 = lean_nat_dec_eq(x_731, x_733);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_736 = lean_unsigned_to_nat(0u);
x_737 = l_Array_extract___rarg(x_670, x_736, x_733);
x_738 = l_Array_extract___rarg(x_670, x_733, x_731);
lean_dec(x_731);
lean_dec(x_670);
x_739 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_739, 0, x_102);
lean_ctor_set(x_739, 1, x_737);
x_740 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_739, x_738, x_3, x_4, x_5, x_729);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; 
lean_dec(x_733);
lean_dec(x_731);
x_741 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_741, 0, x_102);
lean_ctor_set(x_741, 1, x_670);
x_742 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_741, x_3, x_4, x_5, x_729);
return x_742;
}
}
else
{
lean_object* x_743; lean_object* x_744; 
lean_dec(x_733);
lean_dec(x_731);
x_743 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_743, 0, x_102);
lean_ctor_set(x_743, 1, x_670);
x_744 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_743, x_3, x_4, x_5, x_729);
return x_744;
}
}
}
}
else
{
lean_object* x_745; 
lean_free_object(x_684);
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_745 = lean_box(13);
lean_ctor_set(x_675, 0, x_745);
return x_675;
}
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_free_object(x_684);
lean_free_object(x_675);
lean_dec(x_102);
x_746 = l_Lean_IR_instInhabitedArg;
x_747 = lean_unsigned_to_nat(2u);
x_748 = lean_array_get(x_746, x_670, x_747);
lean_dec(x_670);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
lean_dec(x_748);
x_750 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_749, x_3, x_4, x_5, x_678);
return x_750;
}
else
{
lean_object* x_751; lean_object* x_752; 
x_751 = lean_box(0);
x_752 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_751, x_3, x_4, x_5, x_678);
return x_752;
}
}
}
else
{
lean_object* x_753; uint8_t x_754; 
lean_dec(x_684);
x_753 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_754 = lean_name_eq(x_102, x_753);
if (x_754 == 0)
{
lean_object* x_755; uint8_t x_756; 
x_755 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_756 = lean_name_eq(x_102, x_755);
if (x_756 == 0)
{
lean_object* x_757; lean_object* x_758; 
lean_free_object(x_675);
lean_inc(x_102);
x_757 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_678);
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; uint8_t x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_670);
lean_dec(x_2);
lean_dec(x_1);
x_759 = lean_ctor_get(x_757, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 lean_ctor_release(x_757, 1);
 x_760 = x_757;
} else {
 lean_dec_ref(x_757);
 x_760 = lean_box(0);
}
x_761 = 1;
x_762 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_763 = l_Lean_Name_toString(x_102, x_761, x_762);
x_764 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_764, 0, x_763);
x_765 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_760)) {
 x_766 = lean_alloc_ctor(5, 2, 0);
} else {
 x_766 = x_760;
 lean_ctor_set_tag(x_766, 5);
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_764);
x_767 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_768 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
x_769 = l_Lean_MessageData_ofFormat(x_768);
x_770 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_769, x_3, x_4, x_5, x_759);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_770;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint8_t x_777; 
x_771 = lean_ctor_get(x_757, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 lean_ctor_release(x_757, 1);
 x_772 = x_757;
} else {
 lean_dec_ref(x_757);
 x_772 = lean_box(0);
}
x_773 = lean_ctor_get(x_758, 0);
lean_inc(x_773);
lean_dec(x_758);
x_774 = lean_array_get_size(x_670);
x_775 = l_Lean_IR_Decl_params(x_773);
lean_dec(x_773);
x_776 = lean_array_get_size(x_775);
lean_dec(x_775);
x_777 = lean_nat_dec_lt(x_774, x_776);
if (x_777 == 0)
{
uint8_t x_778; 
x_778 = lean_nat_dec_eq(x_774, x_776);
if (x_778 == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_779 = lean_unsigned_to_nat(0u);
x_780 = l_Array_extract___rarg(x_670, x_779, x_776);
x_781 = l_Array_extract___rarg(x_670, x_776, x_774);
lean_dec(x_774);
lean_dec(x_670);
if (lean_is_scalar(x_772)) {
 x_782 = lean_alloc_ctor(6, 2, 0);
} else {
 x_782 = x_772;
 lean_ctor_set_tag(x_782, 6);
}
lean_ctor_set(x_782, 0, x_102);
lean_ctor_set(x_782, 1, x_780);
x_783 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_782, x_781, x_3, x_4, x_5, x_771);
return x_783;
}
else
{
lean_object* x_784; lean_object* x_785; 
lean_dec(x_776);
lean_dec(x_774);
if (lean_is_scalar(x_772)) {
 x_784 = lean_alloc_ctor(6, 2, 0);
} else {
 x_784 = x_772;
 lean_ctor_set_tag(x_784, 6);
}
lean_ctor_set(x_784, 0, x_102);
lean_ctor_set(x_784, 1, x_670);
x_785 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_784, x_3, x_4, x_5, x_771);
return x_785;
}
}
else
{
lean_object* x_786; lean_object* x_787; 
lean_dec(x_776);
lean_dec(x_774);
if (lean_is_scalar(x_772)) {
 x_786 = lean_alloc_ctor(7, 2, 0);
} else {
 x_786 = x_772;
 lean_ctor_set_tag(x_786, 7);
}
lean_ctor_set(x_786, 0, x_102);
lean_ctor_set(x_786, 1, x_670);
x_787 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_786, x_3, x_4, x_5, x_771);
return x_787;
}
}
}
else
{
lean_object* x_788; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_788 = lean_box(13);
lean_ctor_set(x_675, 0, x_788);
return x_675;
}
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
lean_free_object(x_675);
lean_dec(x_102);
x_789 = l_Lean_IR_instInhabitedArg;
x_790 = lean_unsigned_to_nat(2u);
x_791 = lean_array_get(x_789, x_670, x_790);
lean_dec(x_670);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; lean_object* x_793; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
lean_dec(x_791);
x_793 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_792, x_3, x_4, x_5, x_678);
return x_793;
}
else
{
lean_object* x_794; lean_object* x_795; 
x_794 = lean_box(0);
x_795 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_794, x_3, x_4, x_5, x_678);
return x_795;
}
}
}
}
case 2:
{
lean_object* x_796; lean_object* x_797; 
lean_dec(x_684);
lean_dec(x_679);
lean_free_object(x_675);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_796 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_797 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_796, x_3, x_4, x_5, x_678);
return x_797;
}
case 4:
{
uint8_t x_798; 
lean_dec(x_679);
lean_free_object(x_675);
lean_free_object(x_7);
lean_dec(x_664);
x_798 = !lean_is_exclusive(x_684);
if (x_798 == 0)
{
lean_object* x_799; lean_object* x_800; uint8_t x_801; 
x_799 = lean_ctor_get(x_684, 0);
lean_dec(x_799);
x_800 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_801 = lean_name_eq(x_102, x_800);
if (x_801 == 0)
{
uint8_t x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_670);
lean_dec(x_2);
lean_dec(x_1);
x_802 = 1;
x_803 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_804 = l_Lean_Name_toString(x_102, x_802, x_803);
lean_ctor_set_tag(x_684, 3);
lean_ctor_set(x_684, 0, x_804);
x_805 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_806 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_806, 0, x_805);
lean_ctor_set(x_806, 1, x_684);
x_807 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_808 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_808, 0, x_806);
lean_ctor_set(x_808, 1, x_807);
x_809 = l_Lean_MessageData_ofFormat(x_808);
x_810 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_809, x_3, x_4, x_5, x_678);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_810;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_free_object(x_684);
lean_dec(x_102);
x_811 = l_Lean_IR_instInhabitedArg;
x_812 = lean_unsigned_to_nat(2u);
x_813 = lean_array_get(x_811, x_670, x_812);
lean_dec(x_670);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; 
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
lean_dec(x_813);
x_815 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_814, x_3, x_4, x_5, x_678);
return x_815;
}
else
{
lean_object* x_816; lean_object* x_817; 
x_816 = lean_box(0);
x_817 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_816, x_3, x_4, x_5, x_678);
return x_817;
}
}
}
else
{
lean_object* x_818; uint8_t x_819; 
lean_dec(x_684);
x_818 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_819 = lean_name_eq(x_102, x_818);
if (x_819 == 0)
{
uint8_t x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_dec(x_670);
lean_dec(x_2);
lean_dec(x_1);
x_820 = 1;
x_821 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_822 = l_Lean_Name_toString(x_102, x_820, x_821);
x_823 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_823, 0, x_822);
x_824 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_825 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
x_826 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_827 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set(x_827, 1, x_826);
x_828 = l_Lean_MessageData_ofFormat(x_827);
x_829 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_828, x_3, x_4, x_5, x_678);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_829;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_102);
x_830 = l_Lean_IR_instInhabitedArg;
x_831 = lean_unsigned_to_nat(2u);
x_832 = lean_array_get(x_830, x_670, x_831);
lean_dec(x_670);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
lean_dec(x_832);
x_834 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_833, x_3, x_4, x_5, x_678);
return x_834;
}
else
{
lean_object* x_835; lean_object* x_836; 
x_835 = lean_box(0);
x_836 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_835, x_3, x_4, x_5, x_678);
return x_836;
}
}
}
}
case 5:
{
lean_object* x_837; lean_object* x_838; 
lean_dec(x_684);
lean_dec(x_679);
lean_free_object(x_675);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_837 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_838 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_837, x_3, x_4, x_5, x_678);
return x_838;
}
case 6:
{
lean_object* x_839; uint8_t x_840; 
lean_free_object(x_675);
x_839 = lean_ctor_get(x_684, 0);
lean_inc(x_839);
lean_dec(x_684);
lean_inc(x_102);
x_840 = l_Lean_isExtern(x_679, x_102);
if (x_840 == 0)
{
lean_object* x_841; 
lean_dec(x_670);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_841 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_678);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
x_844 = lean_ctor_get(x_842, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_842, 1);
lean_inc(x_845);
lean_dec(x_842);
x_846 = lean_ctor_get(x_839, 3);
lean_inc(x_846);
lean_dec(x_839);
x_847 = lean_array_get_size(x_664);
x_848 = l_Array_extract___rarg(x_664, x_846, x_847);
lean_dec(x_847);
lean_dec(x_664);
x_849 = lean_array_get_size(x_845);
x_850 = lean_unsigned_to_nat(0u);
x_851 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_851);
lean_ctor_set(x_7, 1, x_849);
lean_ctor_set(x_7, 0, x_850);
x_852 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_853 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3(x_845, x_848, x_7, x_7, x_852, x_850, lean_box(0), lean_box(0), x_3, x_4, x_5, x_843);
lean_dec(x_7);
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
x_856 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_844, x_845, x_848, x_854, x_3, x_4, x_5, x_855);
lean_dec(x_848);
lean_dec(x_845);
return x_856;
}
else
{
uint8_t x_857; 
lean_dec(x_839);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_857 = !lean_is_exclusive(x_841);
if (x_857 == 0)
{
return x_841;
}
else
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_858 = lean_ctor_get(x_841, 0);
x_859 = lean_ctor_get(x_841, 1);
lean_inc(x_859);
lean_inc(x_858);
lean_dec(x_841);
x_860 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_860, 0, x_858);
lean_ctor_set(x_860, 1, x_859);
return x_860;
}
}
}
else
{
lean_object* x_861; 
lean_dec(x_839);
lean_free_object(x_7);
lean_dec(x_664);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_670);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_861 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_670, x_3, x_4, x_5, x_678);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
x_864 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_864, 0, x_102);
lean_ctor_set(x_864, 1, x_670);
x_865 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_864, x_3, x_4, x_5, x_863);
return x_865;
}
else
{
uint8_t x_866; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_866 = !lean_is_exclusive(x_861);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; 
x_867 = lean_ctor_get(x_861, 0);
lean_dec(x_867);
x_868 = lean_ctor_get(x_862, 0);
lean_inc(x_868);
lean_dec(x_862);
lean_ctor_set(x_861, 0, x_868);
return x_861;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_869 = lean_ctor_get(x_861, 1);
lean_inc(x_869);
lean_dec(x_861);
x_870 = lean_ctor_get(x_862, 0);
lean_inc(x_870);
lean_dec(x_862);
x_871 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_871, 0, x_870);
lean_ctor_set(x_871, 1, x_869);
return x_871;
}
}
}
else
{
uint8_t x_872; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_872 = !lean_is_exclusive(x_861);
if (x_872 == 0)
{
return x_861;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_861, 0);
x_874 = lean_ctor_get(x_861, 1);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_861);
x_875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_875, 0, x_873);
lean_ctor_set(x_875, 1, x_874);
return x_875;
}
}
}
}
case 7:
{
uint8_t x_876; 
lean_dec(x_679);
lean_free_object(x_675);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_2);
lean_dec(x_1);
x_876 = !lean_is_exclusive(x_684);
if (x_876 == 0)
{
lean_object* x_877; uint8_t x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_877 = lean_ctor_get(x_684, 0);
lean_dec(x_877);
x_878 = 1;
x_879 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_880 = l_Lean_Name_toString(x_102, x_878, x_879);
lean_ctor_set_tag(x_684, 3);
lean_ctor_set(x_684, 0, x_880);
x_881 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_882 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_684);
x_883 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_884 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_884, 0, x_882);
lean_ctor_set(x_884, 1, x_883);
x_885 = l_Lean_MessageData_ofFormat(x_884);
x_886 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_885, x_3, x_4, x_5, x_678);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_886;
}
else
{
uint8_t x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_684);
x_887 = 1;
x_888 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_889 = l_Lean_Name_toString(x_102, x_887, x_888);
x_890 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_890, 0, x_889);
x_891 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_892 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_892, 0, x_891);
lean_ctor_set(x_892, 1, x_890);
x_893 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_894 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_894, 0, x_892);
lean_ctor_set(x_894, 1, x_893);
x_895 = l_Lean_MessageData_ofFormat(x_894);
x_896 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_895, x_3, x_4, x_5, x_678);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_896;
}
}
default: 
{
lean_object* x_897; 
lean_dec(x_684);
lean_dec(x_679);
lean_free_object(x_675);
lean_free_object(x_7);
lean_dec(x_664);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_670);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_897 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_670, x_3, x_4, x_5, x_678);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; 
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
lean_dec(x_897);
x_900 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_900, 0, x_102);
lean_ctor_set(x_900, 1, x_670);
x_901 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_900, x_3, x_4, x_5, x_899);
return x_901;
}
else
{
uint8_t x_902; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_902 = !lean_is_exclusive(x_897);
if (x_902 == 0)
{
lean_object* x_903; lean_object* x_904; 
x_903 = lean_ctor_get(x_897, 0);
lean_dec(x_903);
x_904 = lean_ctor_get(x_898, 0);
lean_inc(x_904);
lean_dec(x_898);
lean_ctor_set(x_897, 0, x_904);
return x_897;
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_905 = lean_ctor_get(x_897, 1);
lean_inc(x_905);
lean_dec(x_897);
x_906 = lean_ctor_get(x_898, 0);
lean_inc(x_906);
lean_dec(x_898);
x_907 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_907, 0, x_906);
lean_ctor_set(x_907, 1, x_905);
return x_907;
}
}
}
else
{
uint8_t x_908; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_908 = !lean_is_exclusive(x_897);
if (x_908 == 0)
{
return x_897;
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_909 = lean_ctor_get(x_897, 0);
x_910 = lean_ctor_get(x_897, 1);
lean_inc(x_910);
lean_inc(x_909);
lean_dec(x_897);
x_911 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_911, 0, x_909);
lean_ctor_set(x_911, 1, x_910);
return x_911;
}
}
}
}
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; uint8_t x_915; lean_object* x_916; 
x_912 = lean_ctor_get(x_675, 0);
x_913 = lean_ctor_get(x_675, 1);
lean_inc(x_913);
lean_inc(x_912);
lean_dec(x_675);
x_914 = lean_ctor_get(x_912, 0);
lean_inc(x_914);
lean_dec(x_912);
x_915 = 0;
lean_inc(x_102);
lean_inc(x_914);
x_916 = l_Lean_Environment_find_x3f(x_914, x_102, x_915);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; 
lean_dec(x_914);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_917 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_918 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_917, x_3, x_4, x_5, x_913);
return x_918;
}
else
{
lean_object* x_919; 
x_919 = lean_ctor_get(x_916, 0);
lean_inc(x_919);
lean_dec(x_916);
switch (lean_obj_tag(x_919)) {
case 0:
{
lean_object* x_920; lean_object* x_921; uint8_t x_922; 
lean_dec(x_914);
lean_free_object(x_7);
lean_dec(x_664);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 x_920 = x_919;
} else {
 lean_dec_ref(x_919);
 x_920 = lean_box(0);
}
x_921 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_922 = lean_name_eq(x_102, x_921);
if (x_922 == 0)
{
lean_object* x_923; uint8_t x_924; 
x_923 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_924 = lean_name_eq(x_102, x_923);
if (x_924 == 0)
{
lean_object* x_925; lean_object* x_926; 
lean_inc(x_102);
x_925 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_913);
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; uint8_t x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_670);
lean_dec(x_2);
lean_dec(x_1);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 x_928 = x_925;
} else {
 lean_dec_ref(x_925);
 x_928 = lean_box(0);
}
x_929 = 1;
x_930 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_931 = l_Lean_Name_toString(x_102, x_929, x_930);
if (lean_is_scalar(x_920)) {
 x_932 = lean_alloc_ctor(3, 1, 0);
} else {
 x_932 = x_920;
 lean_ctor_set_tag(x_932, 3);
}
lean_ctor_set(x_932, 0, x_931);
x_933 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_928)) {
 x_934 = lean_alloc_ctor(5, 2, 0);
} else {
 x_934 = x_928;
 lean_ctor_set_tag(x_934, 5);
}
lean_ctor_set(x_934, 0, x_933);
lean_ctor_set(x_934, 1, x_932);
x_935 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_936 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_936, 0, x_934);
lean_ctor_set(x_936, 1, x_935);
x_937 = l_Lean_MessageData_ofFormat(x_936);
x_938 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_937, x_3, x_4, x_5, x_927);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_938;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; uint8_t x_945; 
lean_dec(x_920);
x_939 = lean_ctor_get(x_925, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 x_940 = x_925;
} else {
 lean_dec_ref(x_925);
 x_940 = lean_box(0);
}
x_941 = lean_ctor_get(x_926, 0);
lean_inc(x_941);
lean_dec(x_926);
x_942 = lean_array_get_size(x_670);
x_943 = l_Lean_IR_Decl_params(x_941);
lean_dec(x_941);
x_944 = lean_array_get_size(x_943);
lean_dec(x_943);
x_945 = lean_nat_dec_lt(x_942, x_944);
if (x_945 == 0)
{
uint8_t x_946; 
x_946 = lean_nat_dec_eq(x_942, x_944);
if (x_946 == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_947 = lean_unsigned_to_nat(0u);
x_948 = l_Array_extract___rarg(x_670, x_947, x_944);
x_949 = l_Array_extract___rarg(x_670, x_944, x_942);
lean_dec(x_942);
lean_dec(x_670);
if (lean_is_scalar(x_940)) {
 x_950 = lean_alloc_ctor(6, 2, 0);
} else {
 x_950 = x_940;
 lean_ctor_set_tag(x_950, 6);
}
lean_ctor_set(x_950, 0, x_102);
lean_ctor_set(x_950, 1, x_948);
x_951 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_950, x_949, x_3, x_4, x_5, x_939);
return x_951;
}
else
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_944);
lean_dec(x_942);
if (lean_is_scalar(x_940)) {
 x_952 = lean_alloc_ctor(6, 2, 0);
} else {
 x_952 = x_940;
 lean_ctor_set_tag(x_952, 6);
}
lean_ctor_set(x_952, 0, x_102);
lean_ctor_set(x_952, 1, x_670);
x_953 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_952, x_3, x_4, x_5, x_939);
return x_953;
}
}
else
{
lean_object* x_954; lean_object* x_955; 
lean_dec(x_944);
lean_dec(x_942);
if (lean_is_scalar(x_940)) {
 x_954 = lean_alloc_ctor(7, 2, 0);
} else {
 x_954 = x_940;
 lean_ctor_set_tag(x_954, 7);
}
lean_ctor_set(x_954, 0, x_102);
lean_ctor_set(x_954, 1, x_670);
x_955 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_954, x_3, x_4, x_5, x_939);
return x_955;
}
}
}
else
{
lean_object* x_956; lean_object* x_957; 
lean_dec(x_920);
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_956 = lean_box(13);
x_957 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_957, 0, x_956);
lean_ctor_set(x_957, 1, x_913);
return x_957;
}
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
lean_dec(x_920);
lean_dec(x_102);
x_958 = l_Lean_IR_instInhabitedArg;
x_959 = lean_unsigned_to_nat(2u);
x_960 = lean_array_get(x_958, x_670, x_959);
lean_dec(x_670);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; 
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
lean_dec(x_960);
x_962 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_961, x_3, x_4, x_5, x_913);
return x_962;
}
else
{
lean_object* x_963; lean_object* x_964; 
x_963 = lean_box(0);
x_964 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_963, x_3, x_4, x_5, x_913);
return x_964;
}
}
}
case 2:
{
lean_object* x_965; lean_object* x_966; 
lean_dec(x_919);
lean_dec(x_914);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_965 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_966 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_965, x_3, x_4, x_5, x_913);
return x_966;
}
case 4:
{
lean_object* x_967; lean_object* x_968; uint8_t x_969; 
lean_dec(x_914);
lean_free_object(x_7);
lean_dec(x_664);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 x_967 = x_919;
} else {
 lean_dec_ref(x_919);
 x_967 = lean_box(0);
}
x_968 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_969 = lean_name_eq(x_102, x_968);
if (x_969 == 0)
{
uint8_t x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_670);
lean_dec(x_2);
lean_dec(x_1);
x_970 = 1;
x_971 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_972 = l_Lean_Name_toString(x_102, x_970, x_971);
if (lean_is_scalar(x_967)) {
 x_973 = lean_alloc_ctor(3, 1, 0);
} else {
 x_973 = x_967;
 lean_ctor_set_tag(x_973, 3);
}
lean_ctor_set(x_973, 0, x_972);
x_974 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_975 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_975, 0, x_974);
lean_ctor_set(x_975, 1, x_973);
x_976 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_977 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
x_978 = l_Lean_MessageData_ofFormat(x_977);
x_979 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_978, x_3, x_4, x_5, x_913);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_979;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
lean_dec(x_967);
lean_dec(x_102);
x_980 = l_Lean_IR_instInhabitedArg;
x_981 = lean_unsigned_to_nat(2u);
x_982 = lean_array_get(x_980, x_670, x_981);
lean_dec(x_670);
if (lean_obj_tag(x_982) == 0)
{
lean_object* x_983; lean_object* x_984; 
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
lean_dec(x_982);
x_984 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_983, x_3, x_4, x_5, x_913);
return x_984;
}
else
{
lean_object* x_985; lean_object* x_986; 
x_985 = lean_box(0);
x_986 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_985, x_3, x_4, x_5, x_913);
return x_986;
}
}
}
case 5:
{
lean_object* x_987; lean_object* x_988; 
lean_dec(x_919);
lean_dec(x_914);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_987 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_988 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_987, x_3, x_4, x_5, x_913);
return x_988;
}
case 6:
{
lean_object* x_989; uint8_t x_990; 
x_989 = lean_ctor_get(x_919, 0);
lean_inc(x_989);
lean_dec(x_919);
lean_inc(x_102);
x_990 = l_Lean_isExtern(x_914, x_102);
if (x_990 == 0)
{
lean_object* x_991; 
lean_dec(x_670);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_991 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_913);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec(x_991);
x_994 = lean_ctor_get(x_992, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_992, 1);
lean_inc(x_995);
lean_dec(x_992);
x_996 = lean_ctor_get(x_989, 3);
lean_inc(x_996);
lean_dec(x_989);
x_997 = lean_array_get_size(x_664);
x_998 = l_Array_extract___rarg(x_664, x_996, x_997);
lean_dec(x_997);
lean_dec(x_664);
x_999 = lean_array_get_size(x_995);
x_1000 = lean_unsigned_to_nat(0u);
x_1001 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_1001);
lean_ctor_set(x_7, 1, x_999);
lean_ctor_set(x_7, 0, x_1000);
x_1002 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_1003 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3(x_995, x_998, x_7, x_7, x_1002, x_1000, lean_box(0), lean_box(0), x_3, x_4, x_5, x_993);
lean_dec(x_7);
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1003, 1);
lean_inc(x_1005);
lean_dec(x_1003);
x_1006 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_994, x_995, x_998, x_1004, x_3, x_4, x_5, x_1005);
lean_dec(x_998);
lean_dec(x_995);
return x_1006;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_989);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1007 = lean_ctor_get(x_991, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_991, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1009 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1009 = lean_box(0);
}
if (lean_is_scalar(x_1009)) {
 x_1010 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1010 = x_1009;
}
lean_ctor_set(x_1010, 0, x_1007);
lean_ctor_set(x_1010, 1, x_1008);
return x_1010;
}
}
else
{
lean_object* x_1011; 
lean_dec(x_989);
lean_free_object(x_7);
lean_dec(x_664);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_670);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1011 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_670, x_3, x_4, x_5, x_913);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; 
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1013 = lean_ctor_get(x_1011, 1);
lean_inc(x_1013);
lean_dec(x_1011);
x_1014 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1014, 0, x_102);
lean_ctor_set(x_1014, 1, x_670);
x_1015 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1014, x_3, x_4, x_5, x_1013);
return x_1015;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1016 = lean_ctor_get(x_1011, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_1011)) {
 lean_ctor_release(x_1011, 0);
 lean_ctor_release(x_1011, 1);
 x_1017 = x_1011;
} else {
 lean_dec_ref(x_1011);
 x_1017 = lean_box(0);
}
x_1018 = lean_ctor_get(x_1012, 0);
lean_inc(x_1018);
lean_dec(x_1012);
if (lean_is_scalar(x_1017)) {
 x_1019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1019 = x_1017;
}
lean_ctor_set(x_1019, 0, x_1018);
lean_ctor_set(x_1019, 1, x_1016);
return x_1019;
}
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1020 = lean_ctor_get(x_1011, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1011, 1);
lean_inc(x_1021);
if (lean_is_exclusive(x_1011)) {
 lean_ctor_release(x_1011, 0);
 lean_ctor_release(x_1011, 1);
 x_1022 = x_1011;
} else {
 lean_dec_ref(x_1011);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1020);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
}
}
case 7:
{
lean_object* x_1024; uint8_t x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
lean_dec(x_914);
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 x_1024 = x_919;
} else {
 lean_dec_ref(x_919);
 x_1024 = lean_box(0);
}
x_1025 = 1;
x_1026 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1027 = l_Lean_Name_toString(x_102, x_1025, x_1026);
if (lean_is_scalar(x_1024)) {
 x_1028 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1028 = x_1024;
 lean_ctor_set_tag(x_1028, 3);
}
lean_ctor_set(x_1028, 0, x_1027);
x_1029 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1030 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1030, 0, x_1029);
lean_ctor_set(x_1030, 1, x_1028);
x_1031 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1032 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1032, 0, x_1030);
lean_ctor_set(x_1032, 1, x_1031);
x_1033 = l_Lean_MessageData_ofFormat(x_1032);
x_1034 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1033, x_3, x_4, x_5, x_913);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1034;
}
default: 
{
lean_object* x_1035; 
lean_dec(x_919);
lean_dec(x_914);
lean_free_object(x_7);
lean_dec(x_664);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_670);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1035 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_670, x_3, x_4, x_5, x_913);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; 
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1037 = lean_ctor_get(x_1035, 1);
lean_inc(x_1037);
lean_dec(x_1035);
x_1038 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1038, 0, x_102);
lean_ctor_set(x_1038, 1, x_670);
x_1039 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1038, x_3, x_4, x_5, x_1037);
return x_1039;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1040 = lean_ctor_get(x_1035, 1);
lean_inc(x_1040);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1041 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1041 = lean_box(0);
}
x_1042 = lean_ctor_get(x_1036, 0);
lean_inc(x_1042);
lean_dec(x_1036);
if (lean_is_scalar(x_1041)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_1041;
}
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_1040);
return x_1043;
}
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_670);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1044 = lean_ctor_get(x_1035, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1035, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1046 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1046 = lean_box(0);
}
if (lean_is_scalar(x_1046)) {
 x_1047 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1047 = x_1046;
}
lean_ctor_set(x_1047, 0, x_1044);
lean_ctor_set(x_1047, 1, x_1045);
return x_1047;
}
}
}
}
}
}
else
{
uint8_t x_1048; 
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1048 = !lean_is_exclusive(x_672);
if (x_1048 == 0)
{
lean_object* x_1049; lean_object* x_1050; 
x_1049 = lean_ctor_get(x_672, 0);
lean_dec(x_1049);
x_1050 = lean_ctor_get(x_673, 0);
lean_inc(x_1050);
lean_dec(x_673);
lean_ctor_set(x_672, 0, x_1050);
return x_672;
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1051 = lean_ctor_get(x_672, 1);
lean_inc(x_1051);
lean_dec(x_672);
x_1052 = lean_ctor_get(x_673, 0);
lean_inc(x_1052);
lean_dec(x_673);
x_1053 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_1051);
return x_1053;
}
}
}
else
{
uint8_t x_1054; 
lean_dec(x_670);
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1054 = !lean_is_exclusive(x_672);
if (x_1054 == 0)
{
return x_672;
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1055 = lean_ctor_get(x_672, 0);
x_1056 = lean_ctor_get(x_672, 1);
lean_inc(x_1056);
lean_inc(x_1055);
lean_dec(x_672);
x_1057 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1057, 0, x_1055);
lean_ctor_set(x_1057, 1, x_1056);
return x_1057;
}
}
}
else
{
uint8_t x_1058; 
lean_free_object(x_7);
lean_dec(x_664);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1058 = !lean_is_exclusive(x_669);
if (x_1058 == 0)
{
return x_669;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1059 = lean_ctor_get(x_669, 0);
x_1060 = lean_ctor_get(x_669, 1);
lean_inc(x_1060);
lean_inc(x_1059);
lean_dec(x_669);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1059);
lean_ctor_set(x_1061, 1, x_1060);
return x_1061;
}
}
}
else
{
lean_object* x_1062; size_t x_1063; size_t x_1064; lean_object* x_1065; 
x_1062 = lean_ctor_get(x_7, 2);
lean_inc(x_1062);
lean_dec(x_7);
x_1063 = lean_array_size(x_1062);
x_1064 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1062);
x_1065 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_1063, x_1064, x_1062, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec(x_1065);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1066);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1068 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1066, x_3, x_4, x_5, x_1067);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; 
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
if (lean_obj_tag(x_1069) == 0)
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; uint8_t x_1076; lean_object* x_1077; 
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
lean_dec(x_1068);
x_1071 = lean_st_ref_get(x_5, x_1070);
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1074 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1074 = lean_box(0);
}
x_1075 = lean_ctor_get(x_1072, 0);
lean_inc(x_1075);
lean_dec(x_1072);
x_1076 = 0;
lean_inc(x_102);
lean_inc(x_1075);
x_1077 = l_Lean_Environment_find_x3f(x_1075, x_102, x_1076);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; 
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1066);
lean_dec(x_1062);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1078 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_1079 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1078, x_3, x_4, x_5, x_1073);
return x_1079;
}
else
{
lean_object* x_1080; 
x_1080 = lean_ctor_get(x_1077, 0);
lean_inc(x_1080);
lean_dec(x_1077);
switch (lean_obj_tag(x_1080)) {
case 0:
{
lean_object* x_1081; lean_object* x_1082; uint8_t x_1083; 
lean_dec(x_1075);
lean_dec(x_1062);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 x_1081 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1081 = lean_box(0);
}
x_1082 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_1083 = lean_name_eq(x_102, x_1082);
if (x_1083 == 0)
{
lean_object* x_1084; uint8_t x_1085; 
x_1084 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_1085 = lean_name_eq(x_102, x_1084);
if (x_1085 == 0)
{
lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_1074);
lean_inc(x_102);
x_1086 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_1073);
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
lean_dec(x_1066);
lean_dec(x_2);
lean_dec(x_1);
x_1088 = lean_ctor_get(x_1086, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1089 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1089 = lean_box(0);
}
x_1090 = 1;
x_1091 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1092 = l_Lean_Name_toString(x_102, x_1090, x_1091);
if (lean_is_scalar(x_1081)) {
 x_1093 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1093 = x_1081;
 lean_ctor_set_tag(x_1093, 3);
}
lean_ctor_set(x_1093, 0, x_1092);
x_1094 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_1089)) {
 x_1095 = lean_alloc_ctor(5, 2, 0);
} else {
 x_1095 = x_1089;
 lean_ctor_set_tag(x_1095, 5);
}
lean_ctor_set(x_1095, 0, x_1094);
lean_ctor_set(x_1095, 1, x_1093);
x_1096 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1097 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1097, 0, x_1095);
lean_ctor_set(x_1097, 1, x_1096);
x_1098 = l_Lean_MessageData_ofFormat(x_1097);
x_1099 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1098, x_3, x_4, x_5, x_1088);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1099;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; uint8_t x_1106; 
lean_dec(x_1081);
x_1100 = lean_ctor_get(x_1086, 1);
lean_inc(x_1100);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1101 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1101 = lean_box(0);
}
x_1102 = lean_ctor_get(x_1087, 0);
lean_inc(x_1102);
lean_dec(x_1087);
x_1103 = lean_array_get_size(x_1066);
x_1104 = l_Lean_IR_Decl_params(x_1102);
lean_dec(x_1102);
x_1105 = lean_array_get_size(x_1104);
lean_dec(x_1104);
x_1106 = lean_nat_dec_lt(x_1103, x_1105);
if (x_1106 == 0)
{
uint8_t x_1107; 
x_1107 = lean_nat_dec_eq(x_1103, x_1105);
if (x_1107 == 0)
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
x_1108 = lean_unsigned_to_nat(0u);
x_1109 = l_Array_extract___rarg(x_1066, x_1108, x_1105);
x_1110 = l_Array_extract___rarg(x_1066, x_1105, x_1103);
lean_dec(x_1103);
lean_dec(x_1066);
if (lean_is_scalar(x_1101)) {
 x_1111 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1111 = x_1101;
 lean_ctor_set_tag(x_1111, 6);
}
lean_ctor_set(x_1111, 0, x_102);
lean_ctor_set(x_1111, 1, x_1109);
x_1112 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1111, x_1110, x_3, x_4, x_5, x_1100);
return x_1112;
}
else
{
lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_1105);
lean_dec(x_1103);
if (lean_is_scalar(x_1101)) {
 x_1113 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1113 = x_1101;
 lean_ctor_set_tag(x_1113, 6);
}
lean_ctor_set(x_1113, 0, x_102);
lean_ctor_set(x_1113, 1, x_1066);
x_1114 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1113, x_3, x_4, x_5, x_1100);
return x_1114;
}
}
else
{
lean_object* x_1115; lean_object* x_1116; 
lean_dec(x_1105);
lean_dec(x_1103);
if (lean_is_scalar(x_1101)) {
 x_1115 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1115 = x_1101;
 lean_ctor_set_tag(x_1115, 7);
}
lean_ctor_set(x_1115, 0, x_102);
lean_ctor_set(x_1115, 1, x_1066);
x_1116 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1115, x_3, x_4, x_5, x_1100);
return x_1116;
}
}
}
else
{
lean_object* x_1117; lean_object* x_1118; 
lean_dec(x_1081);
lean_dec(x_1066);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1117 = lean_box(13);
if (lean_is_scalar(x_1074)) {
 x_1118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1118 = x_1074;
}
lean_ctor_set(x_1118, 0, x_1117);
lean_ctor_set(x_1118, 1, x_1073);
return x_1118;
}
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
lean_dec(x_1081);
lean_dec(x_1074);
lean_dec(x_102);
x_1119 = l_Lean_IR_instInhabitedArg;
x_1120 = lean_unsigned_to_nat(2u);
x_1121 = lean_array_get(x_1119, x_1066, x_1120);
lean_dec(x_1066);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
lean_dec(x_1121);
x_1123 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1122, x_3, x_4, x_5, x_1073);
return x_1123;
}
else
{
lean_object* x_1124; lean_object* x_1125; 
x_1124 = lean_box(0);
x_1125 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1124, x_3, x_4, x_5, x_1073);
return x_1125;
}
}
}
case 2:
{
lean_object* x_1126; lean_object* x_1127; 
lean_dec(x_1080);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1066);
lean_dec(x_1062);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1126 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_1127 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1126, x_3, x_4, x_5, x_1073);
return x_1127;
}
case 4:
{
lean_object* x_1128; lean_object* x_1129; uint8_t x_1130; 
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1062);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 x_1128 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1128 = lean_box(0);
}
x_1129 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_1130 = lean_name_eq(x_102, x_1129);
if (x_1130 == 0)
{
uint8_t x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1066);
lean_dec(x_2);
lean_dec(x_1);
x_1131 = 1;
x_1132 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1133 = l_Lean_Name_toString(x_102, x_1131, x_1132);
if (lean_is_scalar(x_1128)) {
 x_1134 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1134 = x_1128;
 lean_ctor_set_tag(x_1134, 3);
}
lean_ctor_set(x_1134, 0, x_1133);
x_1135 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_1136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1136, 0, x_1135);
lean_ctor_set(x_1136, 1, x_1134);
x_1137 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_1138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1138, 0, x_1136);
lean_ctor_set(x_1138, 1, x_1137);
x_1139 = l_Lean_MessageData_ofFormat(x_1138);
x_1140 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1139, x_3, x_4, x_5, x_1073);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1140;
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
lean_dec(x_1128);
lean_dec(x_102);
x_1141 = l_Lean_IR_instInhabitedArg;
x_1142 = lean_unsigned_to_nat(2u);
x_1143 = lean_array_get(x_1141, x_1066, x_1142);
lean_dec(x_1066);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; lean_object* x_1145; 
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
lean_dec(x_1143);
x_1145 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1144, x_3, x_4, x_5, x_1073);
return x_1145;
}
else
{
lean_object* x_1146; lean_object* x_1147; 
x_1146 = lean_box(0);
x_1147 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1146, x_3, x_4, x_5, x_1073);
return x_1147;
}
}
}
case 5:
{
lean_object* x_1148; lean_object* x_1149; 
lean_dec(x_1080);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1066);
lean_dec(x_1062);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1148 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_1149 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1148, x_3, x_4, x_5, x_1073);
return x_1149;
}
case 6:
{
lean_object* x_1150; uint8_t x_1151; 
lean_dec(x_1074);
x_1150 = lean_ctor_get(x_1080, 0);
lean_inc(x_1150);
lean_dec(x_1080);
lean_inc(x_102);
x_1151 = l_Lean_isExtern(x_1075, x_102);
if (x_1151 == 0)
{
lean_object* x_1152; 
lean_dec(x_1066);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1152 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_1073);
if (lean_obj_tag(x_1152) == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = lean_ctor_get(x_1153, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1153, 1);
lean_inc(x_1156);
lean_dec(x_1153);
x_1157 = lean_ctor_get(x_1150, 3);
lean_inc(x_1157);
lean_dec(x_1150);
x_1158 = lean_array_get_size(x_1062);
x_1159 = l_Array_extract___rarg(x_1062, x_1157, x_1158);
lean_dec(x_1158);
lean_dec(x_1062);
x_1160 = lean_array_get_size(x_1156);
x_1161 = lean_unsigned_to_nat(0u);
x_1162 = lean_unsigned_to_nat(1u);
x_1163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1160);
lean_ctor_set(x_1163, 2, x_1162);
x_1164 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_1165 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3(x_1156, x_1159, x_1163, x_1163, x_1164, x_1161, lean_box(0), lean_box(0), x_3, x_4, x_5, x_1154);
lean_dec(x_1163);
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1168 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_1155, x_1156, x_1159, x_1166, x_3, x_4, x_5, x_1167);
lean_dec(x_1159);
lean_dec(x_1156);
return x_1168;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1150);
lean_dec(x_1062);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1169 = lean_ctor_get(x_1152, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1152, 1);
lean_inc(x_1170);
if (lean_is_exclusive(x_1152)) {
 lean_ctor_release(x_1152, 0);
 lean_ctor_release(x_1152, 1);
 x_1171 = x_1152;
} else {
 lean_dec_ref(x_1152);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1169);
lean_ctor_set(x_1172, 1, x_1170);
return x_1172;
}
}
else
{
lean_object* x_1173; 
lean_dec(x_1150);
lean_dec(x_1062);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1066);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1173 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1066, x_3, x_4, x_5, x_1073);
if (lean_obj_tag(x_1173) == 0)
{
lean_object* x_1174; 
x_1174 = lean_ctor_get(x_1173, 0);
lean_inc(x_1174);
if (lean_obj_tag(x_1174) == 0)
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
x_1175 = lean_ctor_get(x_1173, 1);
lean_inc(x_1175);
lean_dec(x_1173);
x_1176 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1176, 0, x_102);
lean_ctor_set(x_1176, 1, x_1066);
x_1177 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1176, x_3, x_4, x_5, x_1175);
return x_1177;
}
else
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_1066);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1178 = lean_ctor_get(x_1173, 1);
lean_inc(x_1178);
if (lean_is_exclusive(x_1173)) {
 lean_ctor_release(x_1173, 0);
 lean_ctor_release(x_1173, 1);
 x_1179 = x_1173;
} else {
 lean_dec_ref(x_1173);
 x_1179 = lean_box(0);
}
x_1180 = lean_ctor_get(x_1174, 0);
lean_inc(x_1180);
lean_dec(x_1174);
if (lean_is_scalar(x_1179)) {
 x_1181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1181 = x_1179;
}
lean_ctor_set(x_1181, 0, x_1180);
lean_ctor_set(x_1181, 1, x_1178);
return x_1181;
}
}
else
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
lean_dec(x_1066);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1182 = lean_ctor_get(x_1173, 0);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1173, 1);
lean_inc(x_1183);
if (lean_is_exclusive(x_1173)) {
 lean_ctor_release(x_1173, 0);
 lean_ctor_release(x_1173, 1);
 x_1184 = x_1173;
} else {
 lean_dec_ref(x_1173);
 x_1184 = lean_box(0);
}
if (lean_is_scalar(x_1184)) {
 x_1185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1185 = x_1184;
}
lean_ctor_set(x_1185, 0, x_1182);
lean_ctor_set(x_1185, 1, x_1183);
return x_1185;
}
}
}
case 7:
{
lean_object* x_1186; uint8_t x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1066);
lean_dec(x_1062);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 x_1186 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1186 = lean_box(0);
}
x_1187 = 1;
x_1188 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1189 = l_Lean_Name_toString(x_102, x_1187, x_1188);
if (lean_is_scalar(x_1186)) {
 x_1190 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1190 = x_1186;
 lean_ctor_set_tag(x_1190, 3);
}
lean_ctor_set(x_1190, 0, x_1189);
x_1191 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1192 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1192, 0, x_1191);
lean_ctor_set(x_1192, 1, x_1190);
x_1193 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1194 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
x_1195 = l_Lean_MessageData_ofFormat(x_1194);
x_1196 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1195, x_3, x_4, x_5, x_1073);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1196;
}
default: 
{
lean_object* x_1197; 
lean_dec(x_1080);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1062);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1066);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1197 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1066, x_3, x_4, x_5, x_1073);
if (lean_obj_tag(x_1197) == 0)
{
lean_object* x_1198; 
x_1198 = lean_ctor_get(x_1197, 0);
lean_inc(x_1198);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
x_1199 = lean_ctor_get(x_1197, 1);
lean_inc(x_1199);
lean_dec(x_1197);
x_1200 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1200, 0, x_102);
lean_ctor_set(x_1200, 1, x_1066);
x_1201 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1200, x_3, x_4, x_5, x_1199);
return x_1201;
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
lean_dec(x_1066);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1202 = lean_ctor_get(x_1197, 1);
lean_inc(x_1202);
if (lean_is_exclusive(x_1197)) {
 lean_ctor_release(x_1197, 0);
 lean_ctor_release(x_1197, 1);
 x_1203 = x_1197;
} else {
 lean_dec_ref(x_1197);
 x_1203 = lean_box(0);
}
x_1204 = lean_ctor_get(x_1198, 0);
lean_inc(x_1204);
lean_dec(x_1198);
if (lean_is_scalar(x_1203)) {
 x_1205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1205 = x_1203;
}
lean_ctor_set(x_1205, 0, x_1204);
lean_ctor_set(x_1205, 1, x_1202);
return x_1205;
}
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
lean_dec(x_1066);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1206 = lean_ctor_get(x_1197, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1197, 1);
lean_inc(x_1207);
if (lean_is_exclusive(x_1197)) {
 lean_ctor_release(x_1197, 0);
 lean_ctor_release(x_1197, 1);
 x_1208 = x_1197;
} else {
 lean_dec_ref(x_1197);
 x_1208 = lean_box(0);
}
if (lean_is_scalar(x_1208)) {
 x_1209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1209 = x_1208;
}
lean_ctor_set(x_1209, 0, x_1206);
lean_ctor_set(x_1209, 1, x_1207);
return x_1209;
}
}
}
}
}
else
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
lean_dec(x_1066);
lean_dec(x_1062);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1210 = lean_ctor_get(x_1068, 1);
lean_inc(x_1210);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 lean_ctor_release(x_1068, 1);
 x_1211 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1211 = lean_box(0);
}
x_1212 = lean_ctor_get(x_1069, 0);
lean_inc(x_1212);
lean_dec(x_1069);
if (lean_is_scalar(x_1211)) {
 x_1213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1213 = x_1211;
}
lean_ctor_set(x_1213, 0, x_1212);
lean_ctor_set(x_1213, 1, x_1210);
return x_1213;
}
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
lean_dec(x_1066);
lean_dec(x_1062);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1214 = lean_ctor_get(x_1068, 0);
lean_inc(x_1214);
x_1215 = lean_ctor_get(x_1068, 1);
lean_inc(x_1215);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 lean_ctor_release(x_1068, 1);
 x_1216 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1216 = lean_box(0);
}
if (lean_is_scalar(x_1216)) {
 x_1217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1217 = x_1216;
}
lean_ctor_set(x_1217, 0, x_1214);
lean_ctor_set(x_1217, 1, x_1215);
return x_1217;
}
}
else
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_1062);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1218 = lean_ctor_get(x_1065, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1065, 1);
lean_inc(x_1219);
if (lean_is_exclusive(x_1065)) {
 lean_ctor_release(x_1065, 0);
 lean_ctor_release(x_1065, 1);
 x_1220 = x_1065;
} else {
 lean_dec_ref(x_1065);
 x_1220 = lean_box(0);
}
if (lean_is_scalar(x_1220)) {
 x_1221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1221 = x_1220;
}
lean_ctor_set(x_1221, 0, x_1218);
lean_ctor_set(x_1221, 1, x_1219);
return x_1221;
}
}
}
case 1:
{
lean_object* x_1222; 
x_1222 = lean_ctor_get(x_662, 0);
lean_inc(x_1222);
switch (lean_obj_tag(x_1222)) {
case 0:
{
uint8_t x_1223; 
x_1223 = !lean_is_exclusive(x_7);
if (x_1223 == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; uint8_t x_1230; 
x_1224 = lean_ctor_get(x_7, 2);
x_1225 = lean_ctor_get(x_7, 1);
lean_dec(x_1225);
x_1226 = lean_ctor_get(x_7, 0);
lean_dec(x_1226);
x_1227 = lean_ctor_get(x_102, 1);
lean_inc(x_1227);
x_1228 = lean_ctor_get(x_662, 1);
lean_inc(x_1228);
lean_dec(x_662);
x_1229 = l_Lean_IR_ToIR_lowerLet___closed__32;
x_1230 = lean_string_dec_eq(x_1228, x_1229);
lean_dec(x_1228);
if (x_1230 == 0)
{
size_t x_1231; size_t x_1232; lean_object* x_1233; 
lean_dec(x_1227);
x_1231 = lean_array_size(x_1224);
x_1232 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1224);
x_1233 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_1231, x_1232, x_1224, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_1233) == 0)
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1234 = lean_ctor_get(x_1233, 0);
lean_inc(x_1234);
x_1235 = lean_ctor_get(x_1233, 1);
lean_inc(x_1235);
lean_dec(x_1233);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1234);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1236 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1234, x_3, x_4, x_5, x_1235);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; 
x_1237 = lean_ctor_get(x_1236, 0);
lean_inc(x_1237);
if (lean_obj_tag(x_1237) == 0)
{
lean_object* x_1238; lean_object* x_1239; uint8_t x_1240; 
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
lean_dec(x_1236);
x_1239 = lean_st_ref_get(x_5, x_1238);
x_1240 = !lean_is_exclusive(x_1239);
if (x_1240 == 0)
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; uint8_t x_1244; lean_object* x_1245; 
x_1241 = lean_ctor_get(x_1239, 0);
x_1242 = lean_ctor_get(x_1239, 1);
x_1243 = lean_ctor_get(x_1241, 0);
lean_inc(x_1243);
lean_dec(x_1241);
x_1244 = 0;
lean_inc(x_102);
lean_inc(x_1243);
x_1245 = l_Lean_Environment_find_x3f(x_1243, x_102, x_1244);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; 
lean_dec(x_1243);
lean_free_object(x_1239);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1246 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_1247 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1246, x_3, x_4, x_5, x_1242);
return x_1247;
}
else
{
lean_object* x_1248; 
x_1248 = lean_ctor_get(x_1245, 0);
lean_inc(x_1248);
lean_dec(x_1245);
switch (lean_obj_tag(x_1248)) {
case 0:
{
uint8_t x_1249; 
lean_dec(x_1243);
lean_free_object(x_7);
lean_dec(x_1224);
x_1249 = !lean_is_exclusive(x_1248);
if (x_1249 == 0)
{
lean_object* x_1250; lean_object* x_1251; uint8_t x_1252; 
x_1250 = lean_ctor_get(x_1248, 0);
lean_dec(x_1250);
x_1251 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_1252 = lean_name_eq(x_102, x_1251);
if (x_1252 == 0)
{
lean_object* x_1253; uint8_t x_1254; 
x_1253 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_1254 = lean_name_eq(x_102, x_1253);
if (x_1254 == 0)
{
lean_object* x_1255; lean_object* x_1256; 
lean_free_object(x_1239);
lean_inc(x_102);
x_1255 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_1242);
x_1256 = lean_ctor_get(x_1255, 0);
lean_inc(x_1256);
if (lean_obj_tag(x_1256) == 0)
{
uint8_t x_1257; 
lean_dec(x_1234);
lean_dec(x_2);
lean_dec(x_1);
x_1257 = !lean_is_exclusive(x_1255);
if (x_1257 == 0)
{
lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1258 = lean_ctor_get(x_1255, 1);
x_1259 = lean_ctor_get(x_1255, 0);
lean_dec(x_1259);
x_1260 = 1;
x_1261 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1262 = l_Lean_Name_toString(x_102, x_1260, x_1261);
lean_ctor_set_tag(x_1248, 3);
lean_ctor_set(x_1248, 0, x_1262);
x_1263 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_1255, 5);
lean_ctor_set(x_1255, 1, x_1248);
lean_ctor_set(x_1255, 0, x_1263);
x_1264 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1265 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1265, 0, x_1255);
lean_ctor_set(x_1265, 1, x_1264);
x_1266 = l_Lean_MessageData_ofFormat(x_1265);
x_1267 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1266, x_3, x_4, x_5, x_1258);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1267;
}
else
{
lean_object* x_1268; uint8_t x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1268 = lean_ctor_get(x_1255, 1);
lean_inc(x_1268);
lean_dec(x_1255);
x_1269 = 1;
x_1270 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1271 = l_Lean_Name_toString(x_102, x_1269, x_1270);
lean_ctor_set_tag(x_1248, 3);
lean_ctor_set(x_1248, 0, x_1271);
x_1272 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_1273 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1273, 0, x_1272);
lean_ctor_set(x_1273, 1, x_1248);
x_1274 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1275 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1275, 0, x_1273);
lean_ctor_set(x_1275, 1, x_1274);
x_1276 = l_Lean_MessageData_ofFormat(x_1275);
x_1277 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1276, x_3, x_4, x_5, x_1268);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1277;
}
}
else
{
uint8_t x_1278; 
lean_free_object(x_1248);
x_1278 = !lean_is_exclusive(x_1255);
if (x_1278 == 0)
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; uint8_t x_1285; 
x_1279 = lean_ctor_get(x_1255, 1);
x_1280 = lean_ctor_get(x_1255, 0);
lean_dec(x_1280);
x_1281 = lean_ctor_get(x_1256, 0);
lean_inc(x_1281);
lean_dec(x_1256);
x_1282 = lean_array_get_size(x_1234);
x_1283 = l_Lean_IR_Decl_params(x_1281);
lean_dec(x_1281);
x_1284 = lean_array_get_size(x_1283);
lean_dec(x_1283);
x_1285 = lean_nat_dec_lt(x_1282, x_1284);
if (x_1285 == 0)
{
uint8_t x_1286; 
x_1286 = lean_nat_dec_eq(x_1282, x_1284);
if (x_1286 == 0)
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; 
x_1287 = lean_unsigned_to_nat(0u);
x_1288 = l_Array_extract___rarg(x_1234, x_1287, x_1284);
x_1289 = l_Array_extract___rarg(x_1234, x_1284, x_1282);
lean_dec(x_1282);
lean_dec(x_1234);
lean_ctor_set_tag(x_1255, 6);
lean_ctor_set(x_1255, 1, x_1288);
lean_ctor_set(x_1255, 0, x_102);
x_1290 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1255, x_1289, x_3, x_4, x_5, x_1279);
return x_1290;
}
else
{
lean_object* x_1291; 
lean_dec(x_1284);
lean_dec(x_1282);
lean_ctor_set_tag(x_1255, 6);
lean_ctor_set(x_1255, 1, x_1234);
lean_ctor_set(x_1255, 0, x_102);
x_1291 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1255, x_3, x_4, x_5, x_1279);
return x_1291;
}
}
else
{
lean_object* x_1292; 
lean_dec(x_1284);
lean_dec(x_1282);
lean_ctor_set_tag(x_1255, 7);
lean_ctor_set(x_1255, 1, x_1234);
lean_ctor_set(x_1255, 0, x_102);
x_1292 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1255, x_3, x_4, x_5, x_1279);
return x_1292;
}
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; uint8_t x_1298; 
x_1293 = lean_ctor_get(x_1255, 1);
lean_inc(x_1293);
lean_dec(x_1255);
x_1294 = lean_ctor_get(x_1256, 0);
lean_inc(x_1294);
lean_dec(x_1256);
x_1295 = lean_array_get_size(x_1234);
x_1296 = l_Lean_IR_Decl_params(x_1294);
lean_dec(x_1294);
x_1297 = lean_array_get_size(x_1296);
lean_dec(x_1296);
x_1298 = lean_nat_dec_lt(x_1295, x_1297);
if (x_1298 == 0)
{
uint8_t x_1299; 
x_1299 = lean_nat_dec_eq(x_1295, x_1297);
if (x_1299 == 0)
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
x_1300 = lean_unsigned_to_nat(0u);
x_1301 = l_Array_extract___rarg(x_1234, x_1300, x_1297);
x_1302 = l_Array_extract___rarg(x_1234, x_1297, x_1295);
lean_dec(x_1295);
lean_dec(x_1234);
x_1303 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1303, 0, x_102);
lean_ctor_set(x_1303, 1, x_1301);
x_1304 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1303, x_1302, x_3, x_4, x_5, x_1293);
return x_1304;
}
else
{
lean_object* x_1305; lean_object* x_1306; 
lean_dec(x_1297);
lean_dec(x_1295);
x_1305 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1305, 0, x_102);
lean_ctor_set(x_1305, 1, x_1234);
x_1306 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1305, x_3, x_4, x_5, x_1293);
return x_1306;
}
}
else
{
lean_object* x_1307; lean_object* x_1308; 
lean_dec(x_1297);
lean_dec(x_1295);
x_1307 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1307, 0, x_102);
lean_ctor_set(x_1307, 1, x_1234);
x_1308 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1307, x_3, x_4, x_5, x_1293);
return x_1308;
}
}
}
}
else
{
lean_object* x_1309; 
lean_free_object(x_1248);
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1309 = lean_box(13);
lean_ctor_set(x_1239, 0, x_1309);
return x_1239;
}
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
lean_free_object(x_1248);
lean_free_object(x_1239);
lean_dec(x_102);
x_1310 = l_Lean_IR_instInhabitedArg;
x_1311 = lean_unsigned_to_nat(2u);
x_1312 = lean_array_get(x_1310, x_1234, x_1311);
lean_dec(x_1234);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; lean_object* x_1314; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
lean_dec(x_1312);
x_1314 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1313, x_3, x_4, x_5, x_1242);
return x_1314;
}
else
{
lean_object* x_1315; lean_object* x_1316; 
x_1315 = lean_box(0);
x_1316 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1315, x_3, x_4, x_5, x_1242);
return x_1316;
}
}
}
else
{
lean_object* x_1317; uint8_t x_1318; 
lean_dec(x_1248);
x_1317 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_1318 = lean_name_eq(x_102, x_1317);
if (x_1318 == 0)
{
lean_object* x_1319; uint8_t x_1320; 
x_1319 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_1320 = lean_name_eq(x_102, x_1319);
if (x_1320 == 0)
{
lean_object* x_1321; lean_object* x_1322; 
lean_free_object(x_1239);
lean_inc(x_102);
x_1321 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_1242);
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; uint8_t x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
lean_dec(x_1234);
lean_dec(x_2);
lean_dec(x_1);
x_1323 = lean_ctor_get(x_1321, 1);
lean_inc(x_1323);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 lean_ctor_release(x_1321, 1);
 x_1324 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1324 = lean_box(0);
}
x_1325 = 1;
x_1326 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1327 = l_Lean_Name_toString(x_102, x_1325, x_1326);
x_1328 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1328, 0, x_1327);
x_1329 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_1324)) {
 x_1330 = lean_alloc_ctor(5, 2, 0);
} else {
 x_1330 = x_1324;
 lean_ctor_set_tag(x_1330, 5);
}
lean_ctor_set(x_1330, 0, x_1329);
lean_ctor_set(x_1330, 1, x_1328);
x_1331 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1332 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1332, 0, x_1330);
lean_ctor_set(x_1332, 1, x_1331);
x_1333 = l_Lean_MessageData_ofFormat(x_1332);
x_1334 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1333, x_3, x_4, x_5, x_1323);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1334;
}
else
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; uint8_t x_1341; 
x_1335 = lean_ctor_get(x_1321, 1);
lean_inc(x_1335);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 lean_ctor_release(x_1321, 1);
 x_1336 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1336 = lean_box(0);
}
x_1337 = lean_ctor_get(x_1322, 0);
lean_inc(x_1337);
lean_dec(x_1322);
x_1338 = lean_array_get_size(x_1234);
x_1339 = l_Lean_IR_Decl_params(x_1337);
lean_dec(x_1337);
x_1340 = lean_array_get_size(x_1339);
lean_dec(x_1339);
x_1341 = lean_nat_dec_lt(x_1338, x_1340);
if (x_1341 == 0)
{
uint8_t x_1342; 
x_1342 = lean_nat_dec_eq(x_1338, x_1340);
if (x_1342 == 0)
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
x_1343 = lean_unsigned_to_nat(0u);
x_1344 = l_Array_extract___rarg(x_1234, x_1343, x_1340);
x_1345 = l_Array_extract___rarg(x_1234, x_1340, x_1338);
lean_dec(x_1338);
lean_dec(x_1234);
if (lean_is_scalar(x_1336)) {
 x_1346 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1346 = x_1336;
 lean_ctor_set_tag(x_1346, 6);
}
lean_ctor_set(x_1346, 0, x_102);
lean_ctor_set(x_1346, 1, x_1344);
x_1347 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1346, x_1345, x_3, x_4, x_5, x_1335);
return x_1347;
}
else
{
lean_object* x_1348; lean_object* x_1349; 
lean_dec(x_1340);
lean_dec(x_1338);
if (lean_is_scalar(x_1336)) {
 x_1348 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1348 = x_1336;
 lean_ctor_set_tag(x_1348, 6);
}
lean_ctor_set(x_1348, 0, x_102);
lean_ctor_set(x_1348, 1, x_1234);
x_1349 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1348, x_3, x_4, x_5, x_1335);
return x_1349;
}
}
else
{
lean_object* x_1350; lean_object* x_1351; 
lean_dec(x_1340);
lean_dec(x_1338);
if (lean_is_scalar(x_1336)) {
 x_1350 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1350 = x_1336;
 lean_ctor_set_tag(x_1350, 7);
}
lean_ctor_set(x_1350, 0, x_102);
lean_ctor_set(x_1350, 1, x_1234);
x_1351 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1350, x_3, x_4, x_5, x_1335);
return x_1351;
}
}
}
else
{
lean_object* x_1352; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1352 = lean_box(13);
lean_ctor_set(x_1239, 0, x_1352);
return x_1239;
}
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
lean_free_object(x_1239);
lean_dec(x_102);
x_1353 = l_Lean_IR_instInhabitedArg;
x_1354 = lean_unsigned_to_nat(2u);
x_1355 = lean_array_get(x_1353, x_1234, x_1354);
lean_dec(x_1234);
if (lean_obj_tag(x_1355) == 0)
{
lean_object* x_1356; lean_object* x_1357; 
x_1356 = lean_ctor_get(x_1355, 0);
lean_inc(x_1356);
lean_dec(x_1355);
x_1357 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1356, x_3, x_4, x_5, x_1242);
return x_1357;
}
else
{
lean_object* x_1358; lean_object* x_1359; 
x_1358 = lean_box(0);
x_1359 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1358, x_3, x_4, x_5, x_1242);
return x_1359;
}
}
}
}
case 2:
{
lean_object* x_1360; lean_object* x_1361; 
lean_dec(x_1248);
lean_dec(x_1243);
lean_free_object(x_1239);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1360 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_1361 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1360, x_3, x_4, x_5, x_1242);
return x_1361;
}
case 4:
{
uint8_t x_1362; 
lean_dec(x_1243);
lean_free_object(x_1239);
lean_free_object(x_7);
lean_dec(x_1224);
x_1362 = !lean_is_exclusive(x_1248);
if (x_1362 == 0)
{
lean_object* x_1363; lean_object* x_1364; uint8_t x_1365; 
x_1363 = lean_ctor_get(x_1248, 0);
lean_dec(x_1363);
x_1364 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_1365 = lean_name_eq(x_102, x_1364);
if (x_1365 == 0)
{
uint8_t x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_1234);
lean_dec(x_2);
lean_dec(x_1);
x_1366 = 1;
x_1367 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1368 = l_Lean_Name_toString(x_102, x_1366, x_1367);
lean_ctor_set_tag(x_1248, 3);
lean_ctor_set(x_1248, 0, x_1368);
x_1369 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_1370 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1370, 0, x_1369);
lean_ctor_set(x_1370, 1, x_1248);
x_1371 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_1372 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1372, 0, x_1370);
lean_ctor_set(x_1372, 1, x_1371);
x_1373 = l_Lean_MessageData_ofFormat(x_1372);
x_1374 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1373, x_3, x_4, x_5, x_1242);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1374;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_free_object(x_1248);
lean_dec(x_102);
x_1375 = l_Lean_IR_instInhabitedArg;
x_1376 = lean_unsigned_to_nat(2u);
x_1377 = lean_array_get(x_1375, x_1234, x_1376);
lean_dec(x_1234);
if (lean_obj_tag(x_1377) == 0)
{
lean_object* x_1378; lean_object* x_1379; 
x_1378 = lean_ctor_get(x_1377, 0);
lean_inc(x_1378);
lean_dec(x_1377);
x_1379 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1378, x_3, x_4, x_5, x_1242);
return x_1379;
}
else
{
lean_object* x_1380; lean_object* x_1381; 
x_1380 = lean_box(0);
x_1381 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1380, x_3, x_4, x_5, x_1242);
return x_1381;
}
}
}
else
{
lean_object* x_1382; uint8_t x_1383; 
lean_dec(x_1248);
x_1382 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_1383 = lean_name_eq(x_102, x_1382);
if (x_1383 == 0)
{
uint8_t x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
lean_dec(x_1234);
lean_dec(x_2);
lean_dec(x_1);
x_1384 = 1;
x_1385 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1386 = l_Lean_Name_toString(x_102, x_1384, x_1385);
x_1387 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1387, 0, x_1386);
x_1388 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_1389 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1389, 0, x_1388);
lean_ctor_set(x_1389, 1, x_1387);
x_1390 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_1391 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1391, 0, x_1389);
lean_ctor_set(x_1391, 1, x_1390);
x_1392 = l_Lean_MessageData_ofFormat(x_1391);
x_1393 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1392, x_3, x_4, x_5, x_1242);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1393;
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
lean_dec(x_102);
x_1394 = l_Lean_IR_instInhabitedArg;
x_1395 = lean_unsigned_to_nat(2u);
x_1396 = lean_array_get(x_1394, x_1234, x_1395);
lean_dec(x_1234);
if (lean_obj_tag(x_1396) == 0)
{
lean_object* x_1397; lean_object* x_1398; 
x_1397 = lean_ctor_get(x_1396, 0);
lean_inc(x_1397);
lean_dec(x_1396);
x_1398 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1397, x_3, x_4, x_5, x_1242);
return x_1398;
}
else
{
lean_object* x_1399; lean_object* x_1400; 
x_1399 = lean_box(0);
x_1400 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1399, x_3, x_4, x_5, x_1242);
return x_1400;
}
}
}
}
case 5:
{
lean_object* x_1401; lean_object* x_1402; 
lean_dec(x_1248);
lean_dec(x_1243);
lean_free_object(x_1239);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1401 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_1402 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1401, x_3, x_4, x_5, x_1242);
return x_1402;
}
case 6:
{
lean_object* x_1403; uint8_t x_1404; 
lean_free_object(x_1239);
x_1403 = lean_ctor_get(x_1248, 0);
lean_inc(x_1403);
lean_dec(x_1248);
lean_inc(x_102);
x_1404 = l_Lean_isExtern(x_1243, x_102);
if (x_1404 == 0)
{
lean_object* x_1405; 
lean_dec(x_1234);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1405 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_1242);
if (lean_obj_tag(x_1405) == 0)
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
x_1406 = lean_ctor_get(x_1405, 0);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1405, 1);
lean_inc(x_1407);
lean_dec(x_1405);
x_1408 = lean_ctor_get(x_1406, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1406, 1);
lean_inc(x_1409);
lean_dec(x_1406);
x_1410 = lean_ctor_get(x_1403, 3);
lean_inc(x_1410);
lean_dec(x_1403);
x_1411 = lean_array_get_size(x_1224);
x_1412 = l_Array_extract___rarg(x_1224, x_1410, x_1411);
lean_dec(x_1411);
lean_dec(x_1224);
x_1413 = lean_array_get_size(x_1409);
x_1414 = lean_unsigned_to_nat(0u);
x_1415 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_1415);
lean_ctor_set(x_7, 1, x_1413);
lean_ctor_set(x_7, 0, x_1414);
x_1416 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_1417 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4(x_1409, x_1412, x_7, x_7, x_1416, x_1414, lean_box(0), lean_box(0), x_3, x_4, x_5, x_1407);
lean_dec(x_7);
x_1418 = lean_ctor_get(x_1417, 0);
lean_inc(x_1418);
x_1419 = lean_ctor_get(x_1417, 1);
lean_inc(x_1419);
lean_dec(x_1417);
x_1420 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_1408, x_1409, x_1412, x_1418, x_3, x_4, x_5, x_1419);
lean_dec(x_1412);
lean_dec(x_1409);
return x_1420;
}
else
{
uint8_t x_1421; 
lean_dec(x_1403);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1421 = !lean_is_exclusive(x_1405);
if (x_1421 == 0)
{
return x_1405;
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
x_1422 = lean_ctor_get(x_1405, 0);
x_1423 = lean_ctor_get(x_1405, 1);
lean_inc(x_1423);
lean_inc(x_1422);
lean_dec(x_1405);
x_1424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1424, 0, x_1422);
lean_ctor_set(x_1424, 1, x_1423);
return x_1424;
}
}
}
else
{
lean_object* x_1425; 
lean_dec(x_1403);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1234);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1425 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1234, x_3, x_4, x_5, x_1242);
if (lean_obj_tag(x_1425) == 0)
{
lean_object* x_1426; 
x_1426 = lean_ctor_get(x_1425, 0);
lean_inc(x_1426);
if (lean_obj_tag(x_1426) == 0)
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
x_1427 = lean_ctor_get(x_1425, 1);
lean_inc(x_1427);
lean_dec(x_1425);
x_1428 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1428, 0, x_102);
lean_ctor_set(x_1428, 1, x_1234);
x_1429 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1428, x_3, x_4, x_5, x_1427);
return x_1429;
}
else
{
uint8_t x_1430; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1430 = !lean_is_exclusive(x_1425);
if (x_1430 == 0)
{
lean_object* x_1431; lean_object* x_1432; 
x_1431 = lean_ctor_get(x_1425, 0);
lean_dec(x_1431);
x_1432 = lean_ctor_get(x_1426, 0);
lean_inc(x_1432);
lean_dec(x_1426);
lean_ctor_set(x_1425, 0, x_1432);
return x_1425;
}
else
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1433 = lean_ctor_get(x_1425, 1);
lean_inc(x_1433);
lean_dec(x_1425);
x_1434 = lean_ctor_get(x_1426, 0);
lean_inc(x_1434);
lean_dec(x_1426);
x_1435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1435, 0, x_1434);
lean_ctor_set(x_1435, 1, x_1433);
return x_1435;
}
}
}
else
{
uint8_t x_1436; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1436 = !lean_is_exclusive(x_1425);
if (x_1436 == 0)
{
return x_1425;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
x_1437 = lean_ctor_get(x_1425, 0);
x_1438 = lean_ctor_get(x_1425, 1);
lean_inc(x_1438);
lean_inc(x_1437);
lean_dec(x_1425);
x_1439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1439, 0, x_1437);
lean_ctor_set(x_1439, 1, x_1438);
return x_1439;
}
}
}
}
case 7:
{
uint8_t x_1440; 
lean_dec(x_1243);
lean_free_object(x_1239);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1440 = !lean_is_exclusive(x_1248);
if (x_1440 == 0)
{
lean_object* x_1441; uint8_t x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
x_1441 = lean_ctor_get(x_1248, 0);
lean_dec(x_1441);
x_1442 = 1;
x_1443 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1444 = l_Lean_Name_toString(x_102, x_1442, x_1443);
lean_ctor_set_tag(x_1248, 3);
lean_ctor_set(x_1248, 0, x_1444);
x_1445 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1446 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1446, 0, x_1445);
lean_ctor_set(x_1446, 1, x_1248);
x_1447 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1448 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1448, 0, x_1446);
lean_ctor_set(x_1448, 1, x_1447);
x_1449 = l_Lean_MessageData_ofFormat(x_1448);
x_1450 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1449, x_3, x_4, x_5, x_1242);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1450;
}
else
{
uint8_t x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_1248);
x_1451 = 1;
x_1452 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1453 = l_Lean_Name_toString(x_102, x_1451, x_1452);
x_1454 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1454, 0, x_1453);
x_1455 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1456 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1456, 0, x_1455);
lean_ctor_set(x_1456, 1, x_1454);
x_1457 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1458 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1458, 0, x_1456);
lean_ctor_set(x_1458, 1, x_1457);
x_1459 = l_Lean_MessageData_ofFormat(x_1458);
x_1460 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1459, x_3, x_4, x_5, x_1242);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1460;
}
}
default: 
{
lean_object* x_1461; 
lean_dec(x_1248);
lean_dec(x_1243);
lean_free_object(x_1239);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1234);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1461 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1234, x_3, x_4, x_5, x_1242);
if (lean_obj_tag(x_1461) == 0)
{
lean_object* x_1462; 
x_1462 = lean_ctor_get(x_1461, 0);
lean_inc(x_1462);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
x_1463 = lean_ctor_get(x_1461, 1);
lean_inc(x_1463);
lean_dec(x_1461);
x_1464 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1464, 0, x_102);
lean_ctor_set(x_1464, 1, x_1234);
x_1465 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1464, x_3, x_4, x_5, x_1463);
return x_1465;
}
else
{
uint8_t x_1466; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1466 = !lean_is_exclusive(x_1461);
if (x_1466 == 0)
{
lean_object* x_1467; lean_object* x_1468; 
x_1467 = lean_ctor_get(x_1461, 0);
lean_dec(x_1467);
x_1468 = lean_ctor_get(x_1462, 0);
lean_inc(x_1468);
lean_dec(x_1462);
lean_ctor_set(x_1461, 0, x_1468);
return x_1461;
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
x_1469 = lean_ctor_get(x_1461, 1);
lean_inc(x_1469);
lean_dec(x_1461);
x_1470 = lean_ctor_get(x_1462, 0);
lean_inc(x_1470);
lean_dec(x_1462);
x_1471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1471, 0, x_1470);
lean_ctor_set(x_1471, 1, x_1469);
return x_1471;
}
}
}
else
{
uint8_t x_1472; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1472 = !lean_is_exclusive(x_1461);
if (x_1472 == 0)
{
return x_1461;
}
else
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
x_1473 = lean_ctor_get(x_1461, 0);
x_1474 = lean_ctor_get(x_1461, 1);
lean_inc(x_1474);
lean_inc(x_1473);
lean_dec(x_1461);
x_1475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1475, 0, x_1473);
lean_ctor_set(x_1475, 1, x_1474);
return x_1475;
}
}
}
}
}
}
else
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; uint8_t x_1479; lean_object* x_1480; 
x_1476 = lean_ctor_get(x_1239, 0);
x_1477 = lean_ctor_get(x_1239, 1);
lean_inc(x_1477);
lean_inc(x_1476);
lean_dec(x_1239);
x_1478 = lean_ctor_get(x_1476, 0);
lean_inc(x_1478);
lean_dec(x_1476);
x_1479 = 0;
lean_inc(x_102);
lean_inc(x_1478);
x_1480 = l_Lean_Environment_find_x3f(x_1478, x_102, x_1479);
if (lean_obj_tag(x_1480) == 0)
{
lean_object* x_1481; lean_object* x_1482; 
lean_dec(x_1478);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1481 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_1482 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1481, x_3, x_4, x_5, x_1477);
return x_1482;
}
else
{
lean_object* x_1483; 
x_1483 = lean_ctor_get(x_1480, 0);
lean_inc(x_1483);
lean_dec(x_1480);
switch (lean_obj_tag(x_1483)) {
case 0:
{
lean_object* x_1484; lean_object* x_1485; uint8_t x_1486; 
lean_dec(x_1478);
lean_free_object(x_7);
lean_dec(x_1224);
if (lean_is_exclusive(x_1483)) {
 lean_ctor_release(x_1483, 0);
 x_1484 = x_1483;
} else {
 lean_dec_ref(x_1483);
 x_1484 = lean_box(0);
}
x_1485 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_1486 = lean_name_eq(x_102, x_1485);
if (x_1486 == 0)
{
lean_object* x_1487; uint8_t x_1488; 
x_1487 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_1488 = lean_name_eq(x_102, x_1487);
if (x_1488 == 0)
{
lean_object* x_1489; lean_object* x_1490; 
lean_inc(x_102);
x_1489 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_1477);
x_1490 = lean_ctor_get(x_1489, 0);
lean_inc(x_1490);
if (lean_obj_tag(x_1490) == 0)
{
lean_object* x_1491; lean_object* x_1492; uint8_t x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; 
lean_dec(x_1234);
lean_dec(x_2);
lean_dec(x_1);
x_1491 = lean_ctor_get(x_1489, 1);
lean_inc(x_1491);
if (lean_is_exclusive(x_1489)) {
 lean_ctor_release(x_1489, 0);
 lean_ctor_release(x_1489, 1);
 x_1492 = x_1489;
} else {
 lean_dec_ref(x_1489);
 x_1492 = lean_box(0);
}
x_1493 = 1;
x_1494 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1495 = l_Lean_Name_toString(x_102, x_1493, x_1494);
if (lean_is_scalar(x_1484)) {
 x_1496 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1496 = x_1484;
 lean_ctor_set_tag(x_1496, 3);
}
lean_ctor_set(x_1496, 0, x_1495);
x_1497 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_1492)) {
 x_1498 = lean_alloc_ctor(5, 2, 0);
} else {
 x_1498 = x_1492;
 lean_ctor_set_tag(x_1498, 5);
}
lean_ctor_set(x_1498, 0, x_1497);
lean_ctor_set(x_1498, 1, x_1496);
x_1499 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1500 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1500, 0, x_1498);
lean_ctor_set(x_1500, 1, x_1499);
x_1501 = l_Lean_MessageData_ofFormat(x_1500);
x_1502 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1501, x_3, x_4, x_5, x_1491);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1502;
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; 
lean_dec(x_1484);
x_1503 = lean_ctor_get(x_1489, 1);
lean_inc(x_1503);
if (lean_is_exclusive(x_1489)) {
 lean_ctor_release(x_1489, 0);
 lean_ctor_release(x_1489, 1);
 x_1504 = x_1489;
} else {
 lean_dec_ref(x_1489);
 x_1504 = lean_box(0);
}
x_1505 = lean_ctor_get(x_1490, 0);
lean_inc(x_1505);
lean_dec(x_1490);
x_1506 = lean_array_get_size(x_1234);
x_1507 = l_Lean_IR_Decl_params(x_1505);
lean_dec(x_1505);
x_1508 = lean_array_get_size(x_1507);
lean_dec(x_1507);
x_1509 = lean_nat_dec_lt(x_1506, x_1508);
if (x_1509 == 0)
{
uint8_t x_1510; 
x_1510 = lean_nat_dec_eq(x_1506, x_1508);
if (x_1510 == 0)
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; 
x_1511 = lean_unsigned_to_nat(0u);
x_1512 = l_Array_extract___rarg(x_1234, x_1511, x_1508);
x_1513 = l_Array_extract___rarg(x_1234, x_1508, x_1506);
lean_dec(x_1506);
lean_dec(x_1234);
if (lean_is_scalar(x_1504)) {
 x_1514 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1514 = x_1504;
 lean_ctor_set_tag(x_1514, 6);
}
lean_ctor_set(x_1514, 0, x_102);
lean_ctor_set(x_1514, 1, x_1512);
x_1515 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1514, x_1513, x_3, x_4, x_5, x_1503);
return x_1515;
}
else
{
lean_object* x_1516; lean_object* x_1517; 
lean_dec(x_1508);
lean_dec(x_1506);
if (lean_is_scalar(x_1504)) {
 x_1516 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1516 = x_1504;
 lean_ctor_set_tag(x_1516, 6);
}
lean_ctor_set(x_1516, 0, x_102);
lean_ctor_set(x_1516, 1, x_1234);
x_1517 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1516, x_3, x_4, x_5, x_1503);
return x_1517;
}
}
else
{
lean_object* x_1518; lean_object* x_1519; 
lean_dec(x_1508);
lean_dec(x_1506);
if (lean_is_scalar(x_1504)) {
 x_1518 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1518 = x_1504;
 lean_ctor_set_tag(x_1518, 7);
}
lean_ctor_set(x_1518, 0, x_102);
lean_ctor_set(x_1518, 1, x_1234);
x_1519 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1518, x_3, x_4, x_5, x_1503);
return x_1519;
}
}
}
else
{
lean_object* x_1520; lean_object* x_1521; 
lean_dec(x_1484);
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1520 = lean_box(13);
x_1521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1521, 0, x_1520);
lean_ctor_set(x_1521, 1, x_1477);
return x_1521;
}
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
lean_dec(x_1484);
lean_dec(x_102);
x_1522 = l_Lean_IR_instInhabitedArg;
x_1523 = lean_unsigned_to_nat(2u);
x_1524 = lean_array_get(x_1522, x_1234, x_1523);
lean_dec(x_1234);
if (lean_obj_tag(x_1524) == 0)
{
lean_object* x_1525; lean_object* x_1526; 
x_1525 = lean_ctor_get(x_1524, 0);
lean_inc(x_1525);
lean_dec(x_1524);
x_1526 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1525, x_3, x_4, x_5, x_1477);
return x_1526;
}
else
{
lean_object* x_1527; lean_object* x_1528; 
x_1527 = lean_box(0);
x_1528 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1527, x_3, x_4, x_5, x_1477);
return x_1528;
}
}
}
case 2:
{
lean_object* x_1529; lean_object* x_1530; 
lean_dec(x_1483);
lean_dec(x_1478);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1529 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_1530 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1529, x_3, x_4, x_5, x_1477);
return x_1530;
}
case 4:
{
lean_object* x_1531; lean_object* x_1532; uint8_t x_1533; 
lean_dec(x_1478);
lean_free_object(x_7);
lean_dec(x_1224);
if (lean_is_exclusive(x_1483)) {
 lean_ctor_release(x_1483, 0);
 x_1531 = x_1483;
} else {
 lean_dec_ref(x_1483);
 x_1531 = lean_box(0);
}
x_1532 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_1533 = lean_name_eq(x_102, x_1532);
if (x_1533 == 0)
{
uint8_t x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; 
lean_dec(x_1234);
lean_dec(x_2);
lean_dec(x_1);
x_1534 = 1;
x_1535 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1536 = l_Lean_Name_toString(x_102, x_1534, x_1535);
if (lean_is_scalar(x_1531)) {
 x_1537 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1537 = x_1531;
 lean_ctor_set_tag(x_1537, 3);
}
lean_ctor_set(x_1537, 0, x_1536);
x_1538 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_1539 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1539, 0, x_1538);
lean_ctor_set(x_1539, 1, x_1537);
x_1540 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_1541 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1541, 0, x_1539);
lean_ctor_set(x_1541, 1, x_1540);
x_1542 = l_Lean_MessageData_ofFormat(x_1541);
x_1543 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1542, x_3, x_4, x_5, x_1477);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1543;
}
else
{
lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
lean_dec(x_1531);
lean_dec(x_102);
x_1544 = l_Lean_IR_instInhabitedArg;
x_1545 = lean_unsigned_to_nat(2u);
x_1546 = lean_array_get(x_1544, x_1234, x_1545);
lean_dec(x_1234);
if (lean_obj_tag(x_1546) == 0)
{
lean_object* x_1547; lean_object* x_1548; 
x_1547 = lean_ctor_get(x_1546, 0);
lean_inc(x_1547);
lean_dec(x_1546);
x_1548 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1547, x_3, x_4, x_5, x_1477);
return x_1548;
}
else
{
lean_object* x_1549; lean_object* x_1550; 
x_1549 = lean_box(0);
x_1550 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1549, x_3, x_4, x_5, x_1477);
return x_1550;
}
}
}
case 5:
{
lean_object* x_1551; lean_object* x_1552; 
lean_dec(x_1483);
lean_dec(x_1478);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_1551 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_1552 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1551, x_3, x_4, x_5, x_1477);
return x_1552;
}
case 6:
{
lean_object* x_1553; uint8_t x_1554; 
x_1553 = lean_ctor_get(x_1483, 0);
lean_inc(x_1553);
lean_dec(x_1483);
lean_inc(x_102);
x_1554 = l_Lean_isExtern(x_1478, x_102);
if (x_1554 == 0)
{
lean_object* x_1555; 
lean_dec(x_1234);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1555 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_1477);
if (lean_obj_tag(x_1555) == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
x_1556 = lean_ctor_get(x_1555, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1555, 1);
lean_inc(x_1557);
lean_dec(x_1555);
x_1558 = lean_ctor_get(x_1556, 0);
lean_inc(x_1558);
x_1559 = lean_ctor_get(x_1556, 1);
lean_inc(x_1559);
lean_dec(x_1556);
x_1560 = lean_ctor_get(x_1553, 3);
lean_inc(x_1560);
lean_dec(x_1553);
x_1561 = lean_array_get_size(x_1224);
x_1562 = l_Array_extract___rarg(x_1224, x_1560, x_1561);
lean_dec(x_1561);
lean_dec(x_1224);
x_1563 = lean_array_get_size(x_1559);
x_1564 = lean_unsigned_to_nat(0u);
x_1565 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_1565);
lean_ctor_set(x_7, 1, x_1563);
lean_ctor_set(x_7, 0, x_1564);
x_1566 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_1567 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4(x_1559, x_1562, x_7, x_7, x_1566, x_1564, lean_box(0), lean_box(0), x_3, x_4, x_5, x_1557);
lean_dec(x_7);
x_1568 = lean_ctor_get(x_1567, 0);
lean_inc(x_1568);
x_1569 = lean_ctor_get(x_1567, 1);
lean_inc(x_1569);
lean_dec(x_1567);
x_1570 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_1558, x_1559, x_1562, x_1568, x_3, x_4, x_5, x_1569);
lean_dec(x_1562);
lean_dec(x_1559);
return x_1570;
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; 
lean_dec(x_1553);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1571 = lean_ctor_get(x_1555, 0);
lean_inc(x_1571);
x_1572 = lean_ctor_get(x_1555, 1);
lean_inc(x_1572);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 lean_ctor_release(x_1555, 1);
 x_1573 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1573 = lean_box(0);
}
if (lean_is_scalar(x_1573)) {
 x_1574 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1574 = x_1573;
}
lean_ctor_set(x_1574, 0, x_1571);
lean_ctor_set(x_1574, 1, x_1572);
return x_1574;
}
}
else
{
lean_object* x_1575; 
lean_dec(x_1553);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1234);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1575 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1234, x_3, x_4, x_5, x_1477);
if (lean_obj_tag(x_1575) == 0)
{
lean_object* x_1576; 
x_1576 = lean_ctor_get(x_1575, 0);
lean_inc(x_1576);
if (lean_obj_tag(x_1576) == 0)
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
x_1577 = lean_ctor_get(x_1575, 1);
lean_inc(x_1577);
lean_dec(x_1575);
x_1578 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1578, 0, x_102);
lean_ctor_set(x_1578, 1, x_1234);
x_1579 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1578, x_3, x_4, x_5, x_1577);
return x_1579;
}
else
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1580 = lean_ctor_get(x_1575, 1);
lean_inc(x_1580);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1581 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1581 = lean_box(0);
}
x_1582 = lean_ctor_get(x_1576, 0);
lean_inc(x_1582);
lean_dec(x_1576);
if (lean_is_scalar(x_1581)) {
 x_1583 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1583 = x_1581;
}
lean_ctor_set(x_1583, 0, x_1582);
lean_ctor_set(x_1583, 1, x_1580);
return x_1583;
}
}
else
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1584 = lean_ctor_get(x_1575, 0);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1575, 1);
lean_inc(x_1585);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1586 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1586 = lean_box(0);
}
if (lean_is_scalar(x_1586)) {
 x_1587 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1587 = x_1586;
}
lean_ctor_set(x_1587, 0, x_1584);
lean_ctor_set(x_1587, 1, x_1585);
return x_1587;
}
}
}
case 7:
{
lean_object* x_1588; uint8_t x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; 
lean_dec(x_1478);
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_1483)) {
 lean_ctor_release(x_1483, 0);
 x_1588 = x_1483;
} else {
 lean_dec_ref(x_1483);
 x_1588 = lean_box(0);
}
x_1589 = 1;
x_1590 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1591 = l_Lean_Name_toString(x_102, x_1589, x_1590);
if (lean_is_scalar(x_1588)) {
 x_1592 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1592 = x_1588;
 lean_ctor_set_tag(x_1592, 3);
}
lean_ctor_set(x_1592, 0, x_1591);
x_1593 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1594 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1594, 0, x_1593);
lean_ctor_set(x_1594, 1, x_1592);
x_1595 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1596 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1596, 0, x_1594);
lean_ctor_set(x_1596, 1, x_1595);
x_1597 = l_Lean_MessageData_ofFormat(x_1596);
x_1598 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1597, x_3, x_4, x_5, x_1477);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1598;
}
default: 
{
lean_object* x_1599; 
lean_dec(x_1483);
lean_dec(x_1478);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1234);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_1599 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_1234, x_3, x_4, x_5, x_1477);
if (lean_obj_tag(x_1599) == 0)
{
lean_object* x_1600; 
x_1600 = lean_ctor_get(x_1599, 0);
lean_inc(x_1600);
if (lean_obj_tag(x_1600) == 0)
{
lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; 
x_1601 = lean_ctor_get(x_1599, 1);
lean_inc(x_1601);
lean_dec(x_1599);
x_1602 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1602, 0, x_102);
lean_ctor_set(x_1602, 1, x_1234);
x_1603 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1602, x_3, x_4, x_5, x_1601);
return x_1603;
}
else
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1604 = lean_ctor_get(x_1599, 1);
lean_inc(x_1604);
if (lean_is_exclusive(x_1599)) {
 lean_ctor_release(x_1599, 0);
 lean_ctor_release(x_1599, 1);
 x_1605 = x_1599;
} else {
 lean_dec_ref(x_1599);
 x_1605 = lean_box(0);
}
x_1606 = lean_ctor_get(x_1600, 0);
lean_inc(x_1606);
lean_dec(x_1600);
if (lean_is_scalar(x_1605)) {
 x_1607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1607 = x_1605;
}
lean_ctor_set(x_1607, 0, x_1606);
lean_ctor_set(x_1607, 1, x_1604);
return x_1607;
}
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; 
lean_dec(x_1234);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1608 = lean_ctor_get(x_1599, 0);
lean_inc(x_1608);
x_1609 = lean_ctor_get(x_1599, 1);
lean_inc(x_1609);
if (lean_is_exclusive(x_1599)) {
 lean_ctor_release(x_1599, 0);
 lean_ctor_release(x_1599, 1);
 x_1610 = x_1599;
} else {
 lean_dec_ref(x_1599);
 x_1610 = lean_box(0);
}
if (lean_is_scalar(x_1610)) {
 x_1611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1611 = x_1610;
}
lean_ctor_set(x_1611, 0, x_1608);
lean_ctor_set(x_1611, 1, x_1609);
return x_1611;
}
}
}
}
}
}
else
{
uint8_t x_1612; 
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1612 = !lean_is_exclusive(x_1236);
if (x_1612 == 0)
{
lean_object* x_1613; lean_object* x_1614; 
x_1613 = lean_ctor_get(x_1236, 0);
lean_dec(x_1613);
x_1614 = lean_ctor_get(x_1237, 0);
lean_inc(x_1614);
lean_dec(x_1237);
lean_ctor_set(x_1236, 0, x_1614);
return x_1236;
}
else
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
x_1615 = lean_ctor_get(x_1236, 1);
lean_inc(x_1615);
lean_dec(x_1236);
x_1616 = lean_ctor_get(x_1237, 0);
lean_inc(x_1616);
lean_dec(x_1237);
x_1617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1617, 0, x_1616);
lean_ctor_set(x_1617, 1, x_1615);
return x_1617;
}
}
}
else
{
uint8_t x_1618; 
lean_dec(x_1234);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1618 = !lean_is_exclusive(x_1236);
if (x_1618 == 0)
{
return x_1236;
}
else
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1619 = lean_ctor_get(x_1236, 0);
x_1620 = lean_ctor_get(x_1236, 1);
lean_inc(x_1620);
lean_inc(x_1619);
lean_dec(x_1236);
x_1621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1621, 0, x_1619);
lean_ctor_set(x_1621, 1, x_1620);
return x_1621;
}
}
}
else
{
uint8_t x_1622; 
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1622 = !lean_is_exclusive(x_1233);
if (x_1622 == 0)
{
return x_1233;
}
else
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
x_1623 = lean_ctor_get(x_1233, 0);
x_1624 = lean_ctor_get(x_1233, 1);
lean_inc(x_1624);
lean_inc(x_1623);
lean_dec(x_1233);
x_1625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1625, 0, x_1623);
lean_ctor_set(x_1625, 1, x_1624);
return x_1625;
}
}
}
else
{
lean_object* x_1626; uint8_t x_1627; 
lean_dec(x_102);
x_1626 = l_Lean_IR_ToIR_lowerLet___closed__33;
x_1627 = lean_string_dec_eq(x_1227, x_1626);
if (x_1627 == 0)
{
lean_object* x_1628; lean_object* x_1629; size_t x_1630; size_t x_1631; lean_object* x_1632; 
x_1628 = l_Lean_Name_str___override(x_1222, x_1229);
x_1629 = l_Lean_Name_str___override(x_1628, x_1227);
x_1630 = lean_array_size(x_1224);
x_1631 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1224);
x_1632 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_1630, x_1631, x_1224, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_1632) == 0)
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
x_1633 = lean_ctor_get(x_1632, 0);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1632, 1);
lean_inc(x_1634);
lean_dec(x_1632);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1633);
lean_inc(x_1629);
lean_inc(x_2);
lean_inc(x_1);
x_1635 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_1629, x_1633, x_3, x_4, x_5, x_1634);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; 
x_1636 = lean_ctor_get(x_1635, 0);
lean_inc(x_1636);
if (lean_obj_tag(x_1636) == 0)
{
lean_object* x_1637; lean_object* x_1638; uint8_t x_1639; 
x_1637 = lean_ctor_get(x_1635, 1);
lean_inc(x_1637);
lean_dec(x_1635);
x_1638 = lean_st_ref_get(x_5, x_1637);
x_1639 = !lean_is_exclusive(x_1638);
if (x_1639 == 0)
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; uint8_t x_1643; lean_object* x_1644; 
x_1640 = lean_ctor_get(x_1638, 0);
x_1641 = lean_ctor_get(x_1638, 1);
x_1642 = lean_ctor_get(x_1640, 0);
lean_inc(x_1642);
lean_dec(x_1640);
x_1643 = 0;
lean_inc(x_1629);
lean_inc(x_1642);
x_1644 = l_Lean_Environment_find_x3f(x_1642, x_1629, x_1643);
if (lean_obj_tag(x_1644) == 0)
{
lean_object* x_1645; lean_object* x_1646; 
lean_dec(x_1642);
lean_free_object(x_1638);
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1645 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_1646 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1645, x_3, x_4, x_5, x_1641);
return x_1646;
}
else
{
lean_object* x_1647; 
x_1647 = lean_ctor_get(x_1644, 0);
lean_inc(x_1647);
lean_dec(x_1644);
switch (lean_obj_tag(x_1647)) {
case 0:
{
uint8_t x_1648; 
lean_dec(x_1642);
lean_free_object(x_7);
lean_dec(x_1224);
x_1648 = !lean_is_exclusive(x_1647);
if (x_1648 == 0)
{
lean_object* x_1649; lean_object* x_1650; uint8_t x_1651; 
x_1649 = lean_ctor_get(x_1647, 0);
lean_dec(x_1649);
x_1650 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_1651 = lean_name_eq(x_1629, x_1650);
if (x_1651 == 0)
{
lean_object* x_1652; uint8_t x_1653; 
x_1652 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_1653 = lean_name_eq(x_1629, x_1652);
if (x_1653 == 0)
{
lean_object* x_1654; lean_object* x_1655; 
lean_free_object(x_1638);
lean_inc(x_1629);
x_1654 = l_Lean_IR_ToIR_findDecl(x_1629, x_3, x_4, x_5, x_1641);
x_1655 = lean_ctor_get(x_1654, 0);
lean_inc(x_1655);
if (lean_obj_tag(x_1655) == 0)
{
uint8_t x_1656; 
lean_dec(x_1633);
lean_dec(x_2);
lean_dec(x_1);
x_1656 = !lean_is_exclusive(x_1654);
if (x_1656 == 0)
{
lean_object* x_1657; lean_object* x_1658; uint8_t x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
x_1657 = lean_ctor_get(x_1654, 1);
x_1658 = lean_ctor_get(x_1654, 0);
lean_dec(x_1658);
x_1659 = 1;
x_1660 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1661 = l_Lean_Name_toString(x_1629, x_1659, x_1660);
lean_ctor_set_tag(x_1647, 3);
lean_ctor_set(x_1647, 0, x_1661);
x_1662 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_1654, 5);
lean_ctor_set(x_1654, 1, x_1647);
lean_ctor_set(x_1654, 0, x_1662);
x_1663 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1664 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1664, 0, x_1654);
lean_ctor_set(x_1664, 1, x_1663);
x_1665 = l_Lean_MessageData_ofFormat(x_1664);
x_1666 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1665, x_3, x_4, x_5, x_1657);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1666;
}
else
{
lean_object* x_1667; uint8_t x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
x_1667 = lean_ctor_get(x_1654, 1);
lean_inc(x_1667);
lean_dec(x_1654);
x_1668 = 1;
x_1669 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1670 = l_Lean_Name_toString(x_1629, x_1668, x_1669);
lean_ctor_set_tag(x_1647, 3);
lean_ctor_set(x_1647, 0, x_1670);
x_1671 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_1672 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1672, 0, x_1671);
lean_ctor_set(x_1672, 1, x_1647);
x_1673 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1674 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1674, 0, x_1672);
lean_ctor_set(x_1674, 1, x_1673);
x_1675 = l_Lean_MessageData_ofFormat(x_1674);
x_1676 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1675, x_3, x_4, x_5, x_1667);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1676;
}
}
else
{
uint8_t x_1677; 
lean_free_object(x_1647);
x_1677 = !lean_is_exclusive(x_1654);
if (x_1677 == 0)
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; uint8_t x_1684; 
x_1678 = lean_ctor_get(x_1654, 1);
x_1679 = lean_ctor_get(x_1654, 0);
lean_dec(x_1679);
x_1680 = lean_ctor_get(x_1655, 0);
lean_inc(x_1680);
lean_dec(x_1655);
x_1681 = lean_array_get_size(x_1633);
x_1682 = l_Lean_IR_Decl_params(x_1680);
lean_dec(x_1680);
x_1683 = lean_array_get_size(x_1682);
lean_dec(x_1682);
x_1684 = lean_nat_dec_lt(x_1681, x_1683);
if (x_1684 == 0)
{
uint8_t x_1685; 
x_1685 = lean_nat_dec_eq(x_1681, x_1683);
if (x_1685 == 0)
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
x_1686 = lean_unsigned_to_nat(0u);
x_1687 = l_Array_extract___rarg(x_1633, x_1686, x_1683);
x_1688 = l_Array_extract___rarg(x_1633, x_1683, x_1681);
lean_dec(x_1681);
lean_dec(x_1633);
lean_ctor_set_tag(x_1654, 6);
lean_ctor_set(x_1654, 1, x_1687);
lean_ctor_set(x_1654, 0, x_1629);
x_1689 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1654, x_1688, x_3, x_4, x_5, x_1678);
return x_1689;
}
else
{
lean_object* x_1690; 
lean_dec(x_1683);
lean_dec(x_1681);
lean_ctor_set_tag(x_1654, 6);
lean_ctor_set(x_1654, 1, x_1633);
lean_ctor_set(x_1654, 0, x_1629);
x_1690 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1654, x_3, x_4, x_5, x_1678);
return x_1690;
}
}
else
{
lean_object* x_1691; 
lean_dec(x_1683);
lean_dec(x_1681);
lean_ctor_set_tag(x_1654, 7);
lean_ctor_set(x_1654, 1, x_1633);
lean_ctor_set(x_1654, 0, x_1629);
x_1691 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1654, x_3, x_4, x_5, x_1678);
return x_1691;
}
}
else
{
lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; uint8_t x_1697; 
x_1692 = lean_ctor_get(x_1654, 1);
lean_inc(x_1692);
lean_dec(x_1654);
x_1693 = lean_ctor_get(x_1655, 0);
lean_inc(x_1693);
lean_dec(x_1655);
x_1694 = lean_array_get_size(x_1633);
x_1695 = l_Lean_IR_Decl_params(x_1693);
lean_dec(x_1693);
x_1696 = lean_array_get_size(x_1695);
lean_dec(x_1695);
x_1697 = lean_nat_dec_lt(x_1694, x_1696);
if (x_1697 == 0)
{
uint8_t x_1698; 
x_1698 = lean_nat_dec_eq(x_1694, x_1696);
if (x_1698 == 0)
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; 
x_1699 = lean_unsigned_to_nat(0u);
x_1700 = l_Array_extract___rarg(x_1633, x_1699, x_1696);
x_1701 = l_Array_extract___rarg(x_1633, x_1696, x_1694);
lean_dec(x_1694);
lean_dec(x_1633);
x_1702 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1702, 0, x_1629);
lean_ctor_set(x_1702, 1, x_1700);
x_1703 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1702, x_1701, x_3, x_4, x_5, x_1692);
return x_1703;
}
else
{
lean_object* x_1704; lean_object* x_1705; 
lean_dec(x_1696);
lean_dec(x_1694);
x_1704 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1704, 0, x_1629);
lean_ctor_set(x_1704, 1, x_1633);
x_1705 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1704, x_3, x_4, x_5, x_1692);
return x_1705;
}
}
else
{
lean_object* x_1706; lean_object* x_1707; 
lean_dec(x_1696);
lean_dec(x_1694);
x_1706 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1706, 0, x_1629);
lean_ctor_set(x_1706, 1, x_1633);
x_1707 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1706, x_3, x_4, x_5, x_1692);
return x_1707;
}
}
}
}
else
{
lean_object* x_1708; 
lean_free_object(x_1647);
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1708 = lean_box(13);
lean_ctor_set(x_1638, 0, x_1708);
return x_1638;
}
}
else
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; 
lean_free_object(x_1647);
lean_free_object(x_1638);
lean_dec(x_1629);
x_1709 = l_Lean_IR_instInhabitedArg;
x_1710 = lean_unsigned_to_nat(2u);
x_1711 = lean_array_get(x_1709, x_1633, x_1710);
lean_dec(x_1633);
if (lean_obj_tag(x_1711) == 0)
{
lean_object* x_1712; lean_object* x_1713; 
x_1712 = lean_ctor_get(x_1711, 0);
lean_inc(x_1712);
lean_dec(x_1711);
x_1713 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1712, x_3, x_4, x_5, x_1641);
return x_1713;
}
else
{
lean_object* x_1714; lean_object* x_1715; 
x_1714 = lean_box(0);
x_1715 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1714, x_3, x_4, x_5, x_1641);
return x_1715;
}
}
}
else
{
lean_object* x_1716; uint8_t x_1717; 
lean_dec(x_1647);
x_1716 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_1717 = lean_name_eq(x_1629, x_1716);
if (x_1717 == 0)
{
lean_object* x_1718; uint8_t x_1719; 
x_1718 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_1719 = lean_name_eq(x_1629, x_1718);
if (x_1719 == 0)
{
lean_object* x_1720; lean_object* x_1721; 
lean_free_object(x_1638);
lean_inc(x_1629);
x_1720 = l_Lean_IR_ToIR_findDecl(x_1629, x_3, x_4, x_5, x_1641);
x_1721 = lean_ctor_get(x_1720, 0);
lean_inc(x_1721);
if (lean_obj_tag(x_1721) == 0)
{
lean_object* x_1722; lean_object* x_1723; uint8_t x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; 
lean_dec(x_1633);
lean_dec(x_2);
lean_dec(x_1);
x_1722 = lean_ctor_get(x_1720, 1);
lean_inc(x_1722);
if (lean_is_exclusive(x_1720)) {
 lean_ctor_release(x_1720, 0);
 lean_ctor_release(x_1720, 1);
 x_1723 = x_1720;
} else {
 lean_dec_ref(x_1720);
 x_1723 = lean_box(0);
}
x_1724 = 1;
x_1725 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1726 = l_Lean_Name_toString(x_1629, x_1724, x_1725);
x_1727 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1727, 0, x_1726);
x_1728 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_1723)) {
 x_1729 = lean_alloc_ctor(5, 2, 0);
} else {
 x_1729 = x_1723;
 lean_ctor_set_tag(x_1729, 5);
}
lean_ctor_set(x_1729, 0, x_1728);
lean_ctor_set(x_1729, 1, x_1727);
x_1730 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1731 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1731, 0, x_1729);
lean_ctor_set(x_1731, 1, x_1730);
x_1732 = l_Lean_MessageData_ofFormat(x_1731);
x_1733 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1732, x_3, x_4, x_5, x_1722);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1733;
}
else
{
lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; uint8_t x_1740; 
x_1734 = lean_ctor_get(x_1720, 1);
lean_inc(x_1734);
if (lean_is_exclusive(x_1720)) {
 lean_ctor_release(x_1720, 0);
 lean_ctor_release(x_1720, 1);
 x_1735 = x_1720;
} else {
 lean_dec_ref(x_1720);
 x_1735 = lean_box(0);
}
x_1736 = lean_ctor_get(x_1721, 0);
lean_inc(x_1736);
lean_dec(x_1721);
x_1737 = lean_array_get_size(x_1633);
x_1738 = l_Lean_IR_Decl_params(x_1736);
lean_dec(x_1736);
x_1739 = lean_array_get_size(x_1738);
lean_dec(x_1738);
x_1740 = lean_nat_dec_lt(x_1737, x_1739);
if (x_1740 == 0)
{
uint8_t x_1741; 
x_1741 = lean_nat_dec_eq(x_1737, x_1739);
if (x_1741 == 0)
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; 
x_1742 = lean_unsigned_to_nat(0u);
x_1743 = l_Array_extract___rarg(x_1633, x_1742, x_1739);
x_1744 = l_Array_extract___rarg(x_1633, x_1739, x_1737);
lean_dec(x_1737);
lean_dec(x_1633);
if (lean_is_scalar(x_1735)) {
 x_1745 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1745 = x_1735;
 lean_ctor_set_tag(x_1745, 6);
}
lean_ctor_set(x_1745, 0, x_1629);
lean_ctor_set(x_1745, 1, x_1743);
x_1746 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1745, x_1744, x_3, x_4, x_5, x_1734);
return x_1746;
}
else
{
lean_object* x_1747; lean_object* x_1748; 
lean_dec(x_1739);
lean_dec(x_1737);
if (lean_is_scalar(x_1735)) {
 x_1747 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1747 = x_1735;
 lean_ctor_set_tag(x_1747, 6);
}
lean_ctor_set(x_1747, 0, x_1629);
lean_ctor_set(x_1747, 1, x_1633);
x_1748 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1747, x_3, x_4, x_5, x_1734);
return x_1748;
}
}
else
{
lean_object* x_1749; lean_object* x_1750; 
lean_dec(x_1739);
lean_dec(x_1737);
if (lean_is_scalar(x_1735)) {
 x_1749 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1749 = x_1735;
 lean_ctor_set_tag(x_1749, 7);
}
lean_ctor_set(x_1749, 0, x_1629);
lean_ctor_set(x_1749, 1, x_1633);
x_1750 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1749, x_3, x_4, x_5, x_1734);
return x_1750;
}
}
}
else
{
lean_object* x_1751; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1751 = lean_box(13);
lean_ctor_set(x_1638, 0, x_1751);
return x_1638;
}
}
else
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
lean_free_object(x_1638);
lean_dec(x_1629);
x_1752 = l_Lean_IR_instInhabitedArg;
x_1753 = lean_unsigned_to_nat(2u);
x_1754 = lean_array_get(x_1752, x_1633, x_1753);
lean_dec(x_1633);
if (lean_obj_tag(x_1754) == 0)
{
lean_object* x_1755; lean_object* x_1756; 
x_1755 = lean_ctor_get(x_1754, 0);
lean_inc(x_1755);
lean_dec(x_1754);
x_1756 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1755, x_3, x_4, x_5, x_1641);
return x_1756;
}
else
{
lean_object* x_1757; lean_object* x_1758; 
x_1757 = lean_box(0);
x_1758 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1757, x_3, x_4, x_5, x_1641);
return x_1758;
}
}
}
}
case 2:
{
lean_object* x_1759; lean_object* x_1760; 
lean_dec(x_1647);
lean_dec(x_1642);
lean_free_object(x_1638);
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1759 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_1760 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1759, x_3, x_4, x_5, x_1641);
return x_1760;
}
case 4:
{
uint8_t x_1761; 
lean_dec(x_1642);
lean_free_object(x_1638);
lean_free_object(x_7);
lean_dec(x_1224);
x_1761 = !lean_is_exclusive(x_1647);
if (x_1761 == 0)
{
lean_object* x_1762; lean_object* x_1763; uint8_t x_1764; 
x_1762 = lean_ctor_get(x_1647, 0);
lean_dec(x_1762);
x_1763 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_1764 = lean_name_eq(x_1629, x_1763);
if (x_1764 == 0)
{
uint8_t x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; 
lean_dec(x_1633);
lean_dec(x_2);
lean_dec(x_1);
x_1765 = 1;
x_1766 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1767 = l_Lean_Name_toString(x_1629, x_1765, x_1766);
lean_ctor_set_tag(x_1647, 3);
lean_ctor_set(x_1647, 0, x_1767);
x_1768 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_1769 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1769, 0, x_1768);
lean_ctor_set(x_1769, 1, x_1647);
x_1770 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_1771 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1771, 0, x_1769);
lean_ctor_set(x_1771, 1, x_1770);
x_1772 = l_Lean_MessageData_ofFormat(x_1771);
x_1773 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1772, x_3, x_4, x_5, x_1641);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1773;
}
else
{
lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; 
lean_free_object(x_1647);
lean_dec(x_1629);
x_1774 = l_Lean_IR_instInhabitedArg;
x_1775 = lean_unsigned_to_nat(2u);
x_1776 = lean_array_get(x_1774, x_1633, x_1775);
lean_dec(x_1633);
if (lean_obj_tag(x_1776) == 0)
{
lean_object* x_1777; lean_object* x_1778; 
x_1777 = lean_ctor_get(x_1776, 0);
lean_inc(x_1777);
lean_dec(x_1776);
x_1778 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1777, x_3, x_4, x_5, x_1641);
return x_1778;
}
else
{
lean_object* x_1779; lean_object* x_1780; 
x_1779 = lean_box(0);
x_1780 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1779, x_3, x_4, x_5, x_1641);
return x_1780;
}
}
}
else
{
lean_object* x_1781; uint8_t x_1782; 
lean_dec(x_1647);
x_1781 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_1782 = lean_name_eq(x_1629, x_1781);
if (x_1782 == 0)
{
uint8_t x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; 
lean_dec(x_1633);
lean_dec(x_2);
lean_dec(x_1);
x_1783 = 1;
x_1784 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1785 = l_Lean_Name_toString(x_1629, x_1783, x_1784);
x_1786 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1786, 0, x_1785);
x_1787 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_1788 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1788, 0, x_1787);
lean_ctor_set(x_1788, 1, x_1786);
x_1789 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_1790 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1790, 0, x_1788);
lean_ctor_set(x_1790, 1, x_1789);
x_1791 = l_Lean_MessageData_ofFormat(x_1790);
x_1792 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1791, x_3, x_4, x_5, x_1641);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1792;
}
else
{
lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; 
lean_dec(x_1629);
x_1793 = l_Lean_IR_instInhabitedArg;
x_1794 = lean_unsigned_to_nat(2u);
x_1795 = lean_array_get(x_1793, x_1633, x_1794);
lean_dec(x_1633);
if (lean_obj_tag(x_1795) == 0)
{
lean_object* x_1796; lean_object* x_1797; 
x_1796 = lean_ctor_get(x_1795, 0);
lean_inc(x_1796);
lean_dec(x_1795);
x_1797 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1796, x_3, x_4, x_5, x_1641);
return x_1797;
}
else
{
lean_object* x_1798; lean_object* x_1799; 
x_1798 = lean_box(0);
x_1799 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1798, x_3, x_4, x_5, x_1641);
return x_1799;
}
}
}
}
case 5:
{
lean_object* x_1800; lean_object* x_1801; 
lean_dec(x_1647);
lean_dec(x_1642);
lean_free_object(x_1638);
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1800 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_1801 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1800, x_3, x_4, x_5, x_1641);
return x_1801;
}
case 6:
{
lean_object* x_1802; uint8_t x_1803; 
lean_free_object(x_1638);
x_1802 = lean_ctor_get(x_1647, 0);
lean_inc(x_1802);
lean_dec(x_1647);
lean_inc(x_1629);
x_1803 = l_Lean_isExtern(x_1642, x_1629);
if (x_1803 == 0)
{
lean_object* x_1804; 
lean_dec(x_1633);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1804 = l_Lean_IR_ToIR_getCtorInfo(x_1629, x_3, x_4, x_5, x_1641);
if (lean_obj_tag(x_1804) == 0)
{
lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; 
x_1805 = lean_ctor_get(x_1804, 0);
lean_inc(x_1805);
x_1806 = lean_ctor_get(x_1804, 1);
lean_inc(x_1806);
lean_dec(x_1804);
x_1807 = lean_ctor_get(x_1805, 0);
lean_inc(x_1807);
x_1808 = lean_ctor_get(x_1805, 1);
lean_inc(x_1808);
lean_dec(x_1805);
x_1809 = lean_ctor_get(x_1802, 3);
lean_inc(x_1809);
lean_dec(x_1802);
x_1810 = lean_array_get_size(x_1224);
x_1811 = l_Array_extract___rarg(x_1224, x_1809, x_1810);
lean_dec(x_1810);
lean_dec(x_1224);
x_1812 = lean_array_get_size(x_1808);
x_1813 = lean_unsigned_to_nat(0u);
x_1814 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_1814);
lean_ctor_set(x_7, 1, x_1812);
lean_ctor_set(x_7, 0, x_1813);
x_1815 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_1816 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5(x_1808, x_1811, x_7, x_7, x_1815, x_1813, lean_box(0), lean_box(0), x_3, x_4, x_5, x_1806);
lean_dec(x_7);
x_1817 = lean_ctor_get(x_1816, 0);
lean_inc(x_1817);
x_1818 = lean_ctor_get(x_1816, 1);
lean_inc(x_1818);
lean_dec(x_1816);
x_1819 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_1807, x_1808, x_1811, x_1817, x_3, x_4, x_5, x_1818);
lean_dec(x_1811);
lean_dec(x_1808);
return x_1819;
}
else
{
uint8_t x_1820; 
lean_dec(x_1802);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1820 = !lean_is_exclusive(x_1804);
if (x_1820 == 0)
{
return x_1804;
}
else
{
lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; 
x_1821 = lean_ctor_get(x_1804, 0);
x_1822 = lean_ctor_get(x_1804, 1);
lean_inc(x_1822);
lean_inc(x_1821);
lean_dec(x_1804);
x_1823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1823, 0, x_1821);
lean_ctor_set(x_1823, 1, x_1822);
return x_1823;
}
}
}
else
{
lean_object* x_1824; 
lean_dec(x_1802);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1633);
lean_inc(x_1629);
lean_inc(x_2);
lean_inc(x_1);
x_1824 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_1629, x_1633, x_3, x_4, x_5, x_1641);
if (lean_obj_tag(x_1824) == 0)
{
lean_object* x_1825; 
x_1825 = lean_ctor_get(x_1824, 0);
lean_inc(x_1825);
if (lean_obj_tag(x_1825) == 0)
{
lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; 
x_1826 = lean_ctor_get(x_1824, 1);
lean_inc(x_1826);
lean_dec(x_1824);
x_1827 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1827, 0, x_1629);
lean_ctor_set(x_1827, 1, x_1633);
x_1828 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1827, x_3, x_4, x_5, x_1826);
return x_1828;
}
else
{
uint8_t x_1829; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1829 = !lean_is_exclusive(x_1824);
if (x_1829 == 0)
{
lean_object* x_1830; lean_object* x_1831; 
x_1830 = lean_ctor_get(x_1824, 0);
lean_dec(x_1830);
x_1831 = lean_ctor_get(x_1825, 0);
lean_inc(x_1831);
lean_dec(x_1825);
lean_ctor_set(x_1824, 0, x_1831);
return x_1824;
}
else
{
lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; 
x_1832 = lean_ctor_get(x_1824, 1);
lean_inc(x_1832);
lean_dec(x_1824);
x_1833 = lean_ctor_get(x_1825, 0);
lean_inc(x_1833);
lean_dec(x_1825);
x_1834 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1834, 0, x_1833);
lean_ctor_set(x_1834, 1, x_1832);
return x_1834;
}
}
}
else
{
uint8_t x_1835; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1835 = !lean_is_exclusive(x_1824);
if (x_1835 == 0)
{
return x_1824;
}
else
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; 
x_1836 = lean_ctor_get(x_1824, 0);
x_1837 = lean_ctor_get(x_1824, 1);
lean_inc(x_1837);
lean_inc(x_1836);
lean_dec(x_1824);
x_1838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1838, 0, x_1836);
lean_ctor_set(x_1838, 1, x_1837);
return x_1838;
}
}
}
}
case 7:
{
uint8_t x_1839; 
lean_dec(x_1642);
lean_free_object(x_1638);
lean_dec(x_1633);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1839 = !lean_is_exclusive(x_1647);
if (x_1839 == 0)
{
lean_object* x_1840; uint8_t x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; 
x_1840 = lean_ctor_get(x_1647, 0);
lean_dec(x_1840);
x_1841 = 1;
x_1842 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1843 = l_Lean_Name_toString(x_1629, x_1841, x_1842);
lean_ctor_set_tag(x_1647, 3);
lean_ctor_set(x_1647, 0, x_1843);
x_1844 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1845 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1845, 0, x_1844);
lean_ctor_set(x_1845, 1, x_1647);
x_1846 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1847 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1847, 0, x_1845);
lean_ctor_set(x_1847, 1, x_1846);
x_1848 = l_Lean_MessageData_ofFormat(x_1847);
x_1849 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1848, x_3, x_4, x_5, x_1641);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1849;
}
else
{
uint8_t x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; 
lean_dec(x_1647);
x_1850 = 1;
x_1851 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1852 = l_Lean_Name_toString(x_1629, x_1850, x_1851);
x_1853 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1853, 0, x_1852);
x_1854 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1855 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1855, 0, x_1854);
lean_ctor_set(x_1855, 1, x_1853);
x_1856 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1857 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1857, 0, x_1855);
lean_ctor_set(x_1857, 1, x_1856);
x_1858 = l_Lean_MessageData_ofFormat(x_1857);
x_1859 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1858, x_3, x_4, x_5, x_1641);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1859;
}
}
default: 
{
lean_object* x_1860; 
lean_dec(x_1647);
lean_dec(x_1642);
lean_free_object(x_1638);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1633);
lean_inc(x_1629);
lean_inc(x_2);
lean_inc(x_1);
x_1860 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_1629, x_1633, x_3, x_4, x_5, x_1641);
if (lean_obj_tag(x_1860) == 0)
{
lean_object* x_1861; 
x_1861 = lean_ctor_get(x_1860, 0);
lean_inc(x_1861);
if (lean_obj_tag(x_1861) == 0)
{
lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; 
x_1862 = lean_ctor_get(x_1860, 1);
lean_inc(x_1862);
lean_dec(x_1860);
x_1863 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1863, 0, x_1629);
lean_ctor_set(x_1863, 1, x_1633);
x_1864 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1863, x_3, x_4, x_5, x_1862);
return x_1864;
}
else
{
uint8_t x_1865; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1865 = !lean_is_exclusive(x_1860);
if (x_1865 == 0)
{
lean_object* x_1866; lean_object* x_1867; 
x_1866 = lean_ctor_get(x_1860, 0);
lean_dec(x_1866);
x_1867 = lean_ctor_get(x_1861, 0);
lean_inc(x_1867);
lean_dec(x_1861);
lean_ctor_set(x_1860, 0, x_1867);
return x_1860;
}
else
{
lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; 
x_1868 = lean_ctor_get(x_1860, 1);
lean_inc(x_1868);
lean_dec(x_1860);
x_1869 = lean_ctor_get(x_1861, 0);
lean_inc(x_1869);
lean_dec(x_1861);
x_1870 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1870, 0, x_1869);
lean_ctor_set(x_1870, 1, x_1868);
return x_1870;
}
}
}
else
{
uint8_t x_1871; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1871 = !lean_is_exclusive(x_1860);
if (x_1871 == 0)
{
return x_1860;
}
else
{
lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
x_1872 = lean_ctor_get(x_1860, 0);
x_1873 = lean_ctor_get(x_1860, 1);
lean_inc(x_1873);
lean_inc(x_1872);
lean_dec(x_1860);
x_1874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1874, 0, x_1872);
lean_ctor_set(x_1874, 1, x_1873);
return x_1874;
}
}
}
}
}
}
else
{
lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; uint8_t x_1878; lean_object* x_1879; 
x_1875 = lean_ctor_get(x_1638, 0);
x_1876 = lean_ctor_get(x_1638, 1);
lean_inc(x_1876);
lean_inc(x_1875);
lean_dec(x_1638);
x_1877 = lean_ctor_get(x_1875, 0);
lean_inc(x_1877);
lean_dec(x_1875);
x_1878 = 0;
lean_inc(x_1629);
lean_inc(x_1877);
x_1879 = l_Lean_Environment_find_x3f(x_1877, x_1629, x_1878);
if (lean_obj_tag(x_1879) == 0)
{
lean_object* x_1880; lean_object* x_1881; 
lean_dec(x_1877);
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1880 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_1881 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1880, x_3, x_4, x_5, x_1876);
return x_1881;
}
else
{
lean_object* x_1882; 
x_1882 = lean_ctor_get(x_1879, 0);
lean_inc(x_1882);
lean_dec(x_1879);
switch (lean_obj_tag(x_1882)) {
case 0:
{
lean_object* x_1883; lean_object* x_1884; uint8_t x_1885; 
lean_dec(x_1877);
lean_free_object(x_7);
lean_dec(x_1224);
if (lean_is_exclusive(x_1882)) {
 lean_ctor_release(x_1882, 0);
 x_1883 = x_1882;
} else {
 lean_dec_ref(x_1882);
 x_1883 = lean_box(0);
}
x_1884 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_1885 = lean_name_eq(x_1629, x_1884);
if (x_1885 == 0)
{
lean_object* x_1886; uint8_t x_1887; 
x_1886 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_1887 = lean_name_eq(x_1629, x_1886);
if (x_1887 == 0)
{
lean_object* x_1888; lean_object* x_1889; 
lean_inc(x_1629);
x_1888 = l_Lean_IR_ToIR_findDecl(x_1629, x_3, x_4, x_5, x_1876);
x_1889 = lean_ctor_get(x_1888, 0);
lean_inc(x_1889);
if (lean_obj_tag(x_1889) == 0)
{
lean_object* x_1890; lean_object* x_1891; uint8_t x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; 
lean_dec(x_1633);
lean_dec(x_2);
lean_dec(x_1);
x_1890 = lean_ctor_get(x_1888, 1);
lean_inc(x_1890);
if (lean_is_exclusive(x_1888)) {
 lean_ctor_release(x_1888, 0);
 lean_ctor_release(x_1888, 1);
 x_1891 = x_1888;
} else {
 lean_dec_ref(x_1888);
 x_1891 = lean_box(0);
}
x_1892 = 1;
x_1893 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1894 = l_Lean_Name_toString(x_1629, x_1892, x_1893);
if (lean_is_scalar(x_1883)) {
 x_1895 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1895 = x_1883;
 lean_ctor_set_tag(x_1895, 3);
}
lean_ctor_set(x_1895, 0, x_1894);
x_1896 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_1891)) {
 x_1897 = lean_alloc_ctor(5, 2, 0);
} else {
 x_1897 = x_1891;
 lean_ctor_set_tag(x_1897, 5);
}
lean_ctor_set(x_1897, 0, x_1896);
lean_ctor_set(x_1897, 1, x_1895);
x_1898 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_1899 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1899, 0, x_1897);
lean_ctor_set(x_1899, 1, x_1898);
x_1900 = l_Lean_MessageData_ofFormat(x_1899);
x_1901 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1900, x_3, x_4, x_5, x_1890);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1901;
}
else
{
lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; uint8_t x_1908; 
lean_dec(x_1883);
x_1902 = lean_ctor_get(x_1888, 1);
lean_inc(x_1902);
if (lean_is_exclusive(x_1888)) {
 lean_ctor_release(x_1888, 0);
 lean_ctor_release(x_1888, 1);
 x_1903 = x_1888;
} else {
 lean_dec_ref(x_1888);
 x_1903 = lean_box(0);
}
x_1904 = lean_ctor_get(x_1889, 0);
lean_inc(x_1904);
lean_dec(x_1889);
x_1905 = lean_array_get_size(x_1633);
x_1906 = l_Lean_IR_Decl_params(x_1904);
lean_dec(x_1904);
x_1907 = lean_array_get_size(x_1906);
lean_dec(x_1906);
x_1908 = lean_nat_dec_lt(x_1905, x_1907);
if (x_1908 == 0)
{
uint8_t x_1909; 
x_1909 = lean_nat_dec_eq(x_1905, x_1907);
if (x_1909 == 0)
{
lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; 
x_1910 = lean_unsigned_to_nat(0u);
x_1911 = l_Array_extract___rarg(x_1633, x_1910, x_1907);
x_1912 = l_Array_extract___rarg(x_1633, x_1907, x_1905);
lean_dec(x_1905);
lean_dec(x_1633);
if (lean_is_scalar(x_1903)) {
 x_1913 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1913 = x_1903;
 lean_ctor_set_tag(x_1913, 6);
}
lean_ctor_set(x_1913, 0, x_1629);
lean_ctor_set(x_1913, 1, x_1911);
x_1914 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_1913, x_1912, x_3, x_4, x_5, x_1902);
return x_1914;
}
else
{
lean_object* x_1915; lean_object* x_1916; 
lean_dec(x_1907);
lean_dec(x_1905);
if (lean_is_scalar(x_1903)) {
 x_1915 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1915 = x_1903;
 lean_ctor_set_tag(x_1915, 6);
}
lean_ctor_set(x_1915, 0, x_1629);
lean_ctor_set(x_1915, 1, x_1633);
x_1916 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1915, x_3, x_4, x_5, x_1902);
return x_1916;
}
}
else
{
lean_object* x_1917; lean_object* x_1918; 
lean_dec(x_1907);
lean_dec(x_1905);
if (lean_is_scalar(x_1903)) {
 x_1917 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1917 = x_1903;
 lean_ctor_set_tag(x_1917, 7);
}
lean_ctor_set(x_1917, 0, x_1629);
lean_ctor_set(x_1917, 1, x_1633);
x_1918 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1917, x_3, x_4, x_5, x_1902);
return x_1918;
}
}
}
else
{
lean_object* x_1919; lean_object* x_1920; 
lean_dec(x_1883);
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1919 = lean_box(13);
x_1920 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1920, 0, x_1919);
lean_ctor_set(x_1920, 1, x_1876);
return x_1920;
}
}
else
{
lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; 
lean_dec(x_1883);
lean_dec(x_1629);
x_1921 = l_Lean_IR_instInhabitedArg;
x_1922 = lean_unsigned_to_nat(2u);
x_1923 = lean_array_get(x_1921, x_1633, x_1922);
lean_dec(x_1633);
if (lean_obj_tag(x_1923) == 0)
{
lean_object* x_1924; lean_object* x_1925; 
x_1924 = lean_ctor_get(x_1923, 0);
lean_inc(x_1924);
lean_dec(x_1923);
x_1925 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1924, x_3, x_4, x_5, x_1876);
return x_1925;
}
else
{
lean_object* x_1926; lean_object* x_1927; 
x_1926 = lean_box(0);
x_1927 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1926, x_3, x_4, x_5, x_1876);
return x_1927;
}
}
}
case 2:
{
lean_object* x_1928; lean_object* x_1929; 
lean_dec(x_1882);
lean_dec(x_1877);
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1928 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_1929 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1928, x_3, x_4, x_5, x_1876);
return x_1929;
}
case 4:
{
lean_object* x_1930; lean_object* x_1931; uint8_t x_1932; 
lean_dec(x_1877);
lean_free_object(x_7);
lean_dec(x_1224);
if (lean_is_exclusive(x_1882)) {
 lean_ctor_release(x_1882, 0);
 x_1930 = x_1882;
} else {
 lean_dec_ref(x_1882);
 x_1930 = lean_box(0);
}
x_1931 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_1932 = lean_name_eq(x_1629, x_1931);
if (x_1932 == 0)
{
uint8_t x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; 
lean_dec(x_1633);
lean_dec(x_2);
lean_dec(x_1);
x_1933 = 1;
x_1934 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1935 = l_Lean_Name_toString(x_1629, x_1933, x_1934);
if (lean_is_scalar(x_1930)) {
 x_1936 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1936 = x_1930;
 lean_ctor_set_tag(x_1936, 3);
}
lean_ctor_set(x_1936, 0, x_1935);
x_1937 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_1938 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1938, 0, x_1937);
lean_ctor_set(x_1938, 1, x_1936);
x_1939 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_1940 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1940, 0, x_1938);
lean_ctor_set(x_1940, 1, x_1939);
x_1941 = l_Lean_MessageData_ofFormat(x_1940);
x_1942 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1941, x_3, x_4, x_5, x_1876);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1942;
}
else
{
lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; 
lean_dec(x_1930);
lean_dec(x_1629);
x_1943 = l_Lean_IR_instInhabitedArg;
x_1944 = lean_unsigned_to_nat(2u);
x_1945 = lean_array_get(x_1943, x_1633, x_1944);
lean_dec(x_1633);
if (lean_obj_tag(x_1945) == 0)
{
lean_object* x_1946; lean_object* x_1947; 
x_1946 = lean_ctor_get(x_1945, 0);
lean_inc(x_1946);
lean_dec(x_1945);
x_1947 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_1946, x_3, x_4, x_5, x_1876);
return x_1947;
}
else
{
lean_object* x_1948; lean_object* x_1949; 
x_1948 = lean_box(0);
x_1949 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_1948, x_3, x_4, x_5, x_1876);
return x_1949;
}
}
}
case 5:
{
lean_object* x_1950; lean_object* x_1951; 
lean_dec(x_1882);
lean_dec(x_1877);
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
x_1950 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_1951 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_1950, x_3, x_4, x_5, x_1876);
return x_1951;
}
case 6:
{
lean_object* x_1952; uint8_t x_1953; 
x_1952 = lean_ctor_get(x_1882, 0);
lean_inc(x_1952);
lean_dec(x_1882);
lean_inc(x_1629);
x_1953 = l_Lean_isExtern(x_1877, x_1629);
if (x_1953 == 0)
{
lean_object* x_1954; 
lean_dec(x_1633);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1954 = l_Lean_IR_ToIR_getCtorInfo(x_1629, x_3, x_4, x_5, x_1876);
if (lean_obj_tag(x_1954) == 0)
{
lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; 
x_1955 = lean_ctor_get(x_1954, 0);
lean_inc(x_1955);
x_1956 = lean_ctor_get(x_1954, 1);
lean_inc(x_1956);
lean_dec(x_1954);
x_1957 = lean_ctor_get(x_1955, 0);
lean_inc(x_1957);
x_1958 = lean_ctor_get(x_1955, 1);
lean_inc(x_1958);
lean_dec(x_1955);
x_1959 = lean_ctor_get(x_1952, 3);
lean_inc(x_1959);
lean_dec(x_1952);
x_1960 = lean_array_get_size(x_1224);
x_1961 = l_Array_extract___rarg(x_1224, x_1959, x_1960);
lean_dec(x_1960);
lean_dec(x_1224);
x_1962 = lean_array_get_size(x_1958);
x_1963 = lean_unsigned_to_nat(0u);
x_1964 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_1964);
lean_ctor_set(x_7, 1, x_1962);
lean_ctor_set(x_7, 0, x_1963);
x_1965 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_1966 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5(x_1958, x_1961, x_7, x_7, x_1965, x_1963, lean_box(0), lean_box(0), x_3, x_4, x_5, x_1956);
lean_dec(x_7);
x_1967 = lean_ctor_get(x_1966, 0);
lean_inc(x_1967);
x_1968 = lean_ctor_get(x_1966, 1);
lean_inc(x_1968);
lean_dec(x_1966);
x_1969 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_1957, x_1958, x_1961, x_1967, x_3, x_4, x_5, x_1968);
lean_dec(x_1961);
lean_dec(x_1958);
return x_1969;
}
else
{
lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; 
lean_dec(x_1952);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1970 = lean_ctor_get(x_1954, 0);
lean_inc(x_1970);
x_1971 = lean_ctor_get(x_1954, 1);
lean_inc(x_1971);
if (lean_is_exclusive(x_1954)) {
 lean_ctor_release(x_1954, 0);
 lean_ctor_release(x_1954, 1);
 x_1972 = x_1954;
} else {
 lean_dec_ref(x_1954);
 x_1972 = lean_box(0);
}
if (lean_is_scalar(x_1972)) {
 x_1973 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1973 = x_1972;
}
lean_ctor_set(x_1973, 0, x_1970);
lean_ctor_set(x_1973, 1, x_1971);
return x_1973;
}
}
else
{
lean_object* x_1974; 
lean_dec(x_1952);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1633);
lean_inc(x_1629);
lean_inc(x_2);
lean_inc(x_1);
x_1974 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_1629, x_1633, x_3, x_4, x_5, x_1876);
if (lean_obj_tag(x_1974) == 0)
{
lean_object* x_1975; 
x_1975 = lean_ctor_get(x_1974, 0);
lean_inc(x_1975);
if (lean_obj_tag(x_1975) == 0)
{
lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; 
x_1976 = lean_ctor_get(x_1974, 1);
lean_inc(x_1976);
lean_dec(x_1974);
x_1977 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_1977, 0, x_1629);
lean_ctor_set(x_1977, 1, x_1633);
x_1978 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_1977, x_3, x_4, x_5, x_1976);
return x_1978;
}
else
{
lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1979 = lean_ctor_get(x_1974, 1);
lean_inc(x_1979);
if (lean_is_exclusive(x_1974)) {
 lean_ctor_release(x_1974, 0);
 lean_ctor_release(x_1974, 1);
 x_1980 = x_1974;
} else {
 lean_dec_ref(x_1974);
 x_1980 = lean_box(0);
}
x_1981 = lean_ctor_get(x_1975, 0);
lean_inc(x_1981);
lean_dec(x_1975);
if (lean_is_scalar(x_1980)) {
 x_1982 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1982 = x_1980;
}
lean_ctor_set(x_1982, 0, x_1981);
lean_ctor_set(x_1982, 1, x_1979);
return x_1982;
}
}
else
{
lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1983 = lean_ctor_get(x_1974, 0);
lean_inc(x_1983);
x_1984 = lean_ctor_get(x_1974, 1);
lean_inc(x_1984);
if (lean_is_exclusive(x_1974)) {
 lean_ctor_release(x_1974, 0);
 lean_ctor_release(x_1974, 1);
 x_1985 = x_1974;
} else {
 lean_dec_ref(x_1974);
 x_1985 = lean_box(0);
}
if (lean_is_scalar(x_1985)) {
 x_1986 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1986 = x_1985;
}
lean_ctor_set(x_1986, 0, x_1983);
lean_ctor_set(x_1986, 1, x_1984);
return x_1986;
}
}
}
case 7:
{
lean_object* x_1987; uint8_t x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; 
lean_dec(x_1877);
lean_dec(x_1633);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_1882)) {
 lean_ctor_release(x_1882, 0);
 x_1987 = x_1882;
} else {
 lean_dec_ref(x_1882);
 x_1987 = lean_box(0);
}
x_1988 = 1;
x_1989 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_1990 = l_Lean_Name_toString(x_1629, x_1988, x_1989);
if (lean_is_scalar(x_1987)) {
 x_1991 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1991 = x_1987;
 lean_ctor_set_tag(x_1991, 3);
}
lean_ctor_set(x_1991, 0, x_1990);
x_1992 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_1993 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1993, 0, x_1992);
lean_ctor_set(x_1993, 1, x_1991);
x_1994 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_1995 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1995, 0, x_1993);
lean_ctor_set(x_1995, 1, x_1994);
x_1996 = l_Lean_MessageData_ofFormat(x_1995);
x_1997 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1996, x_3, x_4, x_5, x_1876);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1997;
}
default: 
{
lean_object* x_1998; 
lean_dec(x_1882);
lean_dec(x_1877);
lean_free_object(x_7);
lean_dec(x_1224);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1633);
lean_inc(x_1629);
lean_inc(x_2);
lean_inc(x_1);
x_1998 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_1629, x_1633, x_3, x_4, x_5, x_1876);
if (lean_obj_tag(x_1998) == 0)
{
lean_object* x_1999; 
x_1999 = lean_ctor_get(x_1998, 0);
lean_inc(x_1999);
if (lean_obj_tag(x_1999) == 0)
{
lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; 
x_2000 = lean_ctor_get(x_1998, 1);
lean_inc(x_2000);
lean_dec(x_1998);
x_2001 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2001, 0, x_1629);
lean_ctor_set(x_2001, 1, x_1633);
x_2002 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2001, x_3, x_4, x_5, x_2000);
return x_2002;
}
else
{
lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2003 = lean_ctor_get(x_1998, 1);
lean_inc(x_2003);
if (lean_is_exclusive(x_1998)) {
 lean_ctor_release(x_1998, 0);
 lean_ctor_release(x_1998, 1);
 x_2004 = x_1998;
} else {
 lean_dec_ref(x_1998);
 x_2004 = lean_box(0);
}
x_2005 = lean_ctor_get(x_1999, 0);
lean_inc(x_2005);
lean_dec(x_1999);
if (lean_is_scalar(x_2004)) {
 x_2006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2006 = x_2004;
}
lean_ctor_set(x_2006, 0, x_2005);
lean_ctor_set(x_2006, 1, x_2003);
return x_2006;
}
}
else
{
lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2007 = lean_ctor_get(x_1998, 0);
lean_inc(x_2007);
x_2008 = lean_ctor_get(x_1998, 1);
lean_inc(x_2008);
if (lean_is_exclusive(x_1998)) {
 lean_ctor_release(x_1998, 0);
 lean_ctor_release(x_1998, 1);
 x_2009 = x_1998;
} else {
 lean_dec_ref(x_1998);
 x_2009 = lean_box(0);
}
if (lean_is_scalar(x_2009)) {
 x_2010 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2010 = x_2009;
}
lean_ctor_set(x_2010, 0, x_2007);
lean_ctor_set(x_2010, 1, x_2008);
return x_2010;
}
}
}
}
}
}
else
{
uint8_t x_2011; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2011 = !lean_is_exclusive(x_1635);
if (x_2011 == 0)
{
lean_object* x_2012; lean_object* x_2013; 
x_2012 = lean_ctor_get(x_1635, 0);
lean_dec(x_2012);
x_2013 = lean_ctor_get(x_1636, 0);
lean_inc(x_2013);
lean_dec(x_1636);
lean_ctor_set(x_1635, 0, x_2013);
return x_1635;
}
else
{
lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; 
x_2014 = lean_ctor_get(x_1635, 1);
lean_inc(x_2014);
lean_dec(x_1635);
x_2015 = lean_ctor_get(x_1636, 0);
lean_inc(x_2015);
lean_dec(x_1636);
x_2016 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2016, 0, x_2015);
lean_ctor_set(x_2016, 1, x_2014);
return x_2016;
}
}
}
else
{
uint8_t x_2017; 
lean_dec(x_1633);
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2017 = !lean_is_exclusive(x_1635);
if (x_2017 == 0)
{
return x_1635;
}
else
{
lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; 
x_2018 = lean_ctor_get(x_1635, 0);
x_2019 = lean_ctor_get(x_1635, 1);
lean_inc(x_2019);
lean_inc(x_2018);
lean_dec(x_1635);
x_2020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2020, 0, x_2018);
lean_ctor_set(x_2020, 1, x_2019);
return x_2020;
}
}
}
else
{
uint8_t x_2021; 
lean_dec(x_1629);
lean_free_object(x_7);
lean_dec(x_1224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2021 = !lean_is_exclusive(x_1632);
if (x_2021 == 0)
{
return x_1632;
}
else
{
lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; 
x_2022 = lean_ctor_get(x_1632, 0);
x_2023 = lean_ctor_get(x_1632, 1);
lean_inc(x_2023);
lean_inc(x_2022);
lean_dec(x_1632);
x_2024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2024, 0, x_2022);
lean_ctor_set(x_2024, 1, x_2023);
return x_2024;
}
}
}
else
{
size_t x_2025; size_t x_2026; lean_object* x_2027; 
lean_dec(x_1227);
lean_free_object(x_7);
x_2025 = lean_array_size(x_1224);
x_2026 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2027 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_2025, x_2026, x_1224, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_2027) == 0)
{
lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; uint8_t x_2032; 
x_2028 = lean_ctor_get(x_2027, 0);
lean_inc(x_2028);
x_2029 = lean_ctor_get(x_2027, 1);
lean_inc(x_2029);
lean_dec(x_2027);
x_2030 = lean_ctor_get(x_1, 0);
lean_inc(x_2030);
lean_dec(x_1);
x_2031 = l_Lean_IR_ToIR_bindVar(x_2030, x_3, x_4, x_5, x_2029);
x_2032 = !lean_is_exclusive(x_2031);
if (x_2032 == 0)
{
lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; uint8_t x_2036; 
x_2033 = lean_ctor_get(x_2031, 0);
x_2034 = lean_ctor_get(x_2031, 1);
x_2035 = l_Lean_IR_ToIR_newVar(x_3, x_4, x_5, x_2034);
x_2036 = !lean_is_exclusive(x_2035);
if (x_2036 == 0)
{
lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; 
x_2037 = lean_ctor_get(x_2035, 0);
x_2038 = lean_ctor_get(x_2035, 1);
x_2039 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_2038);
if (lean_obj_tag(x_2039) == 0)
{
uint8_t x_2040; 
x_2040 = !lean_is_exclusive(x_2039);
if (x_2040 == 0)
{
lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; 
x_2041 = lean_ctor_get(x_2039, 0);
x_2042 = l_Lean_IR_instInhabitedArg;
x_2043 = lean_unsigned_to_nat(0u);
x_2044 = lean_array_get(x_2042, x_2028, x_2043);
lean_dec(x_2028);
lean_inc(x_2037);
x_2045 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2045, 0, x_2037);
x_2046 = lean_box(0);
lean_ctor_set_tag(x_2035, 1);
lean_ctor_set(x_2035, 1, x_2046);
lean_ctor_set(x_2035, 0, x_2045);
lean_ctor_set_tag(x_2031, 1);
lean_ctor_set(x_2031, 1, x_2035);
lean_ctor_set(x_2031, 0, x_2044);
x_2047 = lean_array_mk(x_2031);
x_2048 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_2049 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2049, 0, x_2048);
lean_ctor_set(x_2049, 1, x_2047);
x_2050 = lean_box(7);
x_2051 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2051, 0, x_2033);
lean_ctor_set(x_2051, 1, x_2050);
lean_ctor_set(x_2051, 2, x_2049);
lean_ctor_set(x_2051, 3, x_2041);
x_2052 = l_Lean_IR_ToIR_lowerLet___closed__37;
x_2053 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2053, 0, x_2037);
lean_ctor_set(x_2053, 1, x_2050);
lean_ctor_set(x_2053, 2, x_2052);
lean_ctor_set(x_2053, 3, x_2051);
lean_ctor_set(x_2039, 0, x_2053);
return x_2039;
}
else
{
lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; 
x_2054 = lean_ctor_get(x_2039, 0);
x_2055 = lean_ctor_get(x_2039, 1);
lean_inc(x_2055);
lean_inc(x_2054);
lean_dec(x_2039);
x_2056 = l_Lean_IR_instInhabitedArg;
x_2057 = lean_unsigned_to_nat(0u);
x_2058 = lean_array_get(x_2056, x_2028, x_2057);
lean_dec(x_2028);
lean_inc(x_2037);
x_2059 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2059, 0, x_2037);
x_2060 = lean_box(0);
lean_ctor_set_tag(x_2035, 1);
lean_ctor_set(x_2035, 1, x_2060);
lean_ctor_set(x_2035, 0, x_2059);
lean_ctor_set_tag(x_2031, 1);
lean_ctor_set(x_2031, 1, x_2035);
lean_ctor_set(x_2031, 0, x_2058);
x_2061 = lean_array_mk(x_2031);
x_2062 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_2063 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2063, 0, x_2062);
lean_ctor_set(x_2063, 1, x_2061);
x_2064 = lean_box(7);
x_2065 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2065, 0, x_2033);
lean_ctor_set(x_2065, 1, x_2064);
lean_ctor_set(x_2065, 2, x_2063);
lean_ctor_set(x_2065, 3, x_2054);
x_2066 = l_Lean_IR_ToIR_lowerLet___closed__37;
x_2067 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2067, 0, x_2037);
lean_ctor_set(x_2067, 1, x_2064);
lean_ctor_set(x_2067, 2, x_2066);
lean_ctor_set(x_2067, 3, x_2065);
x_2068 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2068, 0, x_2067);
lean_ctor_set(x_2068, 1, x_2055);
return x_2068;
}
}
else
{
uint8_t x_2069; 
lean_free_object(x_2035);
lean_dec(x_2037);
lean_free_object(x_2031);
lean_dec(x_2033);
lean_dec(x_2028);
x_2069 = !lean_is_exclusive(x_2039);
if (x_2069 == 0)
{
return x_2039;
}
else
{
lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; 
x_2070 = lean_ctor_get(x_2039, 0);
x_2071 = lean_ctor_get(x_2039, 1);
lean_inc(x_2071);
lean_inc(x_2070);
lean_dec(x_2039);
x_2072 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2072, 0, x_2070);
lean_ctor_set(x_2072, 1, x_2071);
return x_2072;
}
}
}
else
{
lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; 
x_2073 = lean_ctor_get(x_2035, 0);
x_2074 = lean_ctor_get(x_2035, 1);
lean_inc(x_2074);
lean_inc(x_2073);
lean_dec(x_2035);
x_2075 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_2074);
if (lean_obj_tag(x_2075) == 0)
{
lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; 
x_2076 = lean_ctor_get(x_2075, 0);
lean_inc(x_2076);
x_2077 = lean_ctor_get(x_2075, 1);
lean_inc(x_2077);
if (lean_is_exclusive(x_2075)) {
 lean_ctor_release(x_2075, 0);
 lean_ctor_release(x_2075, 1);
 x_2078 = x_2075;
} else {
 lean_dec_ref(x_2075);
 x_2078 = lean_box(0);
}
x_2079 = l_Lean_IR_instInhabitedArg;
x_2080 = lean_unsigned_to_nat(0u);
x_2081 = lean_array_get(x_2079, x_2028, x_2080);
lean_dec(x_2028);
lean_inc(x_2073);
x_2082 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2082, 0, x_2073);
x_2083 = lean_box(0);
x_2084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2084, 0, x_2082);
lean_ctor_set(x_2084, 1, x_2083);
lean_ctor_set_tag(x_2031, 1);
lean_ctor_set(x_2031, 1, x_2084);
lean_ctor_set(x_2031, 0, x_2081);
x_2085 = lean_array_mk(x_2031);
x_2086 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_2087 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2087, 0, x_2086);
lean_ctor_set(x_2087, 1, x_2085);
x_2088 = lean_box(7);
x_2089 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2089, 0, x_2033);
lean_ctor_set(x_2089, 1, x_2088);
lean_ctor_set(x_2089, 2, x_2087);
lean_ctor_set(x_2089, 3, x_2076);
x_2090 = l_Lean_IR_ToIR_lowerLet___closed__37;
x_2091 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2091, 0, x_2073);
lean_ctor_set(x_2091, 1, x_2088);
lean_ctor_set(x_2091, 2, x_2090);
lean_ctor_set(x_2091, 3, x_2089);
if (lean_is_scalar(x_2078)) {
 x_2092 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2092 = x_2078;
}
lean_ctor_set(x_2092, 0, x_2091);
lean_ctor_set(x_2092, 1, x_2077);
return x_2092;
}
else
{
lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; 
lean_dec(x_2073);
lean_free_object(x_2031);
lean_dec(x_2033);
lean_dec(x_2028);
x_2093 = lean_ctor_get(x_2075, 0);
lean_inc(x_2093);
x_2094 = lean_ctor_get(x_2075, 1);
lean_inc(x_2094);
if (lean_is_exclusive(x_2075)) {
 lean_ctor_release(x_2075, 0);
 lean_ctor_release(x_2075, 1);
 x_2095 = x_2075;
} else {
 lean_dec_ref(x_2075);
 x_2095 = lean_box(0);
}
if (lean_is_scalar(x_2095)) {
 x_2096 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2096 = x_2095;
}
lean_ctor_set(x_2096, 0, x_2093);
lean_ctor_set(x_2096, 1, x_2094);
return x_2096;
}
}
}
else
{
lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; 
x_2097 = lean_ctor_get(x_2031, 0);
x_2098 = lean_ctor_get(x_2031, 1);
lean_inc(x_2098);
lean_inc(x_2097);
lean_dec(x_2031);
x_2099 = l_Lean_IR_ToIR_newVar(x_3, x_4, x_5, x_2098);
x_2100 = lean_ctor_get(x_2099, 0);
lean_inc(x_2100);
x_2101 = lean_ctor_get(x_2099, 1);
lean_inc(x_2101);
if (lean_is_exclusive(x_2099)) {
 lean_ctor_release(x_2099, 0);
 lean_ctor_release(x_2099, 1);
 x_2102 = x_2099;
} else {
 lean_dec_ref(x_2099);
 x_2102 = lean_box(0);
}
x_2103 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_2101);
if (lean_obj_tag(x_2103) == 0)
{
lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; 
x_2104 = lean_ctor_get(x_2103, 0);
lean_inc(x_2104);
x_2105 = lean_ctor_get(x_2103, 1);
lean_inc(x_2105);
if (lean_is_exclusive(x_2103)) {
 lean_ctor_release(x_2103, 0);
 lean_ctor_release(x_2103, 1);
 x_2106 = x_2103;
} else {
 lean_dec_ref(x_2103);
 x_2106 = lean_box(0);
}
x_2107 = l_Lean_IR_instInhabitedArg;
x_2108 = lean_unsigned_to_nat(0u);
x_2109 = lean_array_get(x_2107, x_2028, x_2108);
lean_dec(x_2028);
lean_inc(x_2100);
x_2110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2110, 0, x_2100);
x_2111 = lean_box(0);
if (lean_is_scalar(x_2102)) {
 x_2112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2112 = x_2102;
 lean_ctor_set_tag(x_2112, 1);
}
lean_ctor_set(x_2112, 0, x_2110);
lean_ctor_set(x_2112, 1, x_2111);
x_2113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2113, 0, x_2109);
lean_ctor_set(x_2113, 1, x_2112);
x_2114 = lean_array_mk(x_2113);
x_2115 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_2116 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2116, 0, x_2115);
lean_ctor_set(x_2116, 1, x_2114);
x_2117 = lean_box(7);
x_2118 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2118, 0, x_2097);
lean_ctor_set(x_2118, 1, x_2117);
lean_ctor_set(x_2118, 2, x_2116);
lean_ctor_set(x_2118, 3, x_2104);
x_2119 = l_Lean_IR_ToIR_lowerLet___closed__37;
x_2120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2120, 0, x_2100);
lean_ctor_set(x_2120, 1, x_2117);
lean_ctor_set(x_2120, 2, x_2119);
lean_ctor_set(x_2120, 3, x_2118);
if (lean_is_scalar(x_2106)) {
 x_2121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2121 = x_2106;
}
lean_ctor_set(x_2121, 0, x_2120);
lean_ctor_set(x_2121, 1, x_2105);
return x_2121;
}
else
{
lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; 
lean_dec(x_2102);
lean_dec(x_2100);
lean_dec(x_2097);
lean_dec(x_2028);
x_2122 = lean_ctor_get(x_2103, 0);
lean_inc(x_2122);
x_2123 = lean_ctor_get(x_2103, 1);
lean_inc(x_2123);
if (lean_is_exclusive(x_2103)) {
 lean_ctor_release(x_2103, 0);
 lean_ctor_release(x_2103, 1);
 x_2124 = x_2103;
} else {
 lean_dec_ref(x_2103);
 x_2124 = lean_box(0);
}
if (lean_is_scalar(x_2124)) {
 x_2125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2125 = x_2124;
}
lean_ctor_set(x_2125, 0, x_2122);
lean_ctor_set(x_2125, 1, x_2123);
return x_2125;
}
}
}
else
{
uint8_t x_2126; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2126 = !lean_is_exclusive(x_2027);
if (x_2126 == 0)
{
return x_2027;
}
else
{
lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_2127 = lean_ctor_get(x_2027, 0);
x_2128 = lean_ctor_get(x_2027, 1);
lean_inc(x_2128);
lean_inc(x_2127);
lean_dec(x_2027);
x_2129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2129, 0, x_2127);
lean_ctor_set(x_2129, 1, x_2128);
return x_2129;
}
}
}
}
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; uint8_t x_2134; 
x_2130 = lean_ctor_get(x_7, 2);
lean_inc(x_2130);
lean_dec(x_7);
x_2131 = lean_ctor_get(x_102, 1);
lean_inc(x_2131);
x_2132 = lean_ctor_get(x_662, 1);
lean_inc(x_2132);
lean_dec(x_662);
x_2133 = l_Lean_IR_ToIR_lowerLet___closed__32;
x_2134 = lean_string_dec_eq(x_2132, x_2133);
lean_dec(x_2132);
if (x_2134 == 0)
{
size_t x_2135; size_t x_2136; lean_object* x_2137; 
lean_dec(x_2131);
x_2135 = lean_array_size(x_2130);
x_2136 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2130);
x_2137 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_2135, x_2136, x_2130, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_2137) == 0)
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; 
x_2138 = lean_ctor_get(x_2137, 0);
lean_inc(x_2138);
x_2139 = lean_ctor_get(x_2137, 1);
lean_inc(x_2139);
lean_dec(x_2137);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2138);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2140 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2138, x_3, x_4, x_5, x_2139);
if (lean_obj_tag(x_2140) == 0)
{
lean_object* x_2141; 
x_2141 = lean_ctor_get(x_2140, 0);
lean_inc(x_2141);
if (lean_obj_tag(x_2141) == 0)
{
lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; uint8_t x_2148; lean_object* x_2149; 
x_2142 = lean_ctor_get(x_2140, 1);
lean_inc(x_2142);
lean_dec(x_2140);
x_2143 = lean_st_ref_get(x_5, x_2142);
x_2144 = lean_ctor_get(x_2143, 0);
lean_inc(x_2144);
x_2145 = lean_ctor_get(x_2143, 1);
lean_inc(x_2145);
if (lean_is_exclusive(x_2143)) {
 lean_ctor_release(x_2143, 0);
 lean_ctor_release(x_2143, 1);
 x_2146 = x_2143;
} else {
 lean_dec_ref(x_2143);
 x_2146 = lean_box(0);
}
x_2147 = lean_ctor_get(x_2144, 0);
lean_inc(x_2147);
lean_dec(x_2144);
x_2148 = 0;
lean_inc(x_102);
lean_inc(x_2147);
x_2149 = l_Lean_Environment_find_x3f(x_2147, x_102, x_2148);
if (lean_obj_tag(x_2149) == 0)
{
lean_object* x_2150; lean_object* x_2151; 
lean_dec(x_2147);
lean_dec(x_2146);
lean_dec(x_2138);
lean_dec(x_2130);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2150 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2151 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2150, x_3, x_4, x_5, x_2145);
return x_2151;
}
else
{
lean_object* x_2152; 
x_2152 = lean_ctor_get(x_2149, 0);
lean_inc(x_2152);
lean_dec(x_2149);
switch (lean_obj_tag(x_2152)) {
case 0:
{
lean_object* x_2153; lean_object* x_2154; uint8_t x_2155; 
lean_dec(x_2147);
lean_dec(x_2130);
if (lean_is_exclusive(x_2152)) {
 lean_ctor_release(x_2152, 0);
 x_2153 = x_2152;
} else {
 lean_dec_ref(x_2152);
 x_2153 = lean_box(0);
}
x_2154 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2155 = lean_name_eq(x_102, x_2154);
if (x_2155 == 0)
{
lean_object* x_2156; uint8_t x_2157; 
x_2156 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_2157 = lean_name_eq(x_102, x_2156);
if (x_2157 == 0)
{
lean_object* x_2158; lean_object* x_2159; 
lean_dec(x_2146);
lean_inc(x_102);
x_2158 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_2145);
x_2159 = lean_ctor_get(x_2158, 0);
lean_inc(x_2159);
if (lean_obj_tag(x_2159) == 0)
{
lean_object* x_2160; lean_object* x_2161; uint8_t x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; 
lean_dec(x_2138);
lean_dec(x_2);
lean_dec(x_1);
x_2160 = lean_ctor_get(x_2158, 1);
lean_inc(x_2160);
if (lean_is_exclusive(x_2158)) {
 lean_ctor_release(x_2158, 0);
 lean_ctor_release(x_2158, 1);
 x_2161 = x_2158;
} else {
 lean_dec_ref(x_2158);
 x_2161 = lean_box(0);
}
x_2162 = 1;
x_2163 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2164 = l_Lean_Name_toString(x_102, x_2162, x_2163);
if (lean_is_scalar(x_2153)) {
 x_2165 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2165 = x_2153;
 lean_ctor_set_tag(x_2165, 3);
}
lean_ctor_set(x_2165, 0, x_2164);
x_2166 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_2161)) {
 x_2167 = lean_alloc_ctor(5, 2, 0);
} else {
 x_2167 = x_2161;
 lean_ctor_set_tag(x_2167, 5);
}
lean_ctor_set(x_2167, 0, x_2166);
lean_ctor_set(x_2167, 1, x_2165);
x_2168 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2169 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2169, 0, x_2167);
lean_ctor_set(x_2169, 1, x_2168);
x_2170 = l_Lean_MessageData_ofFormat(x_2169);
x_2171 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2170, x_3, x_4, x_5, x_2160);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2171;
}
else
{
lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; uint8_t x_2178; 
lean_dec(x_2153);
x_2172 = lean_ctor_get(x_2158, 1);
lean_inc(x_2172);
if (lean_is_exclusive(x_2158)) {
 lean_ctor_release(x_2158, 0);
 lean_ctor_release(x_2158, 1);
 x_2173 = x_2158;
} else {
 lean_dec_ref(x_2158);
 x_2173 = lean_box(0);
}
x_2174 = lean_ctor_get(x_2159, 0);
lean_inc(x_2174);
lean_dec(x_2159);
x_2175 = lean_array_get_size(x_2138);
x_2176 = l_Lean_IR_Decl_params(x_2174);
lean_dec(x_2174);
x_2177 = lean_array_get_size(x_2176);
lean_dec(x_2176);
x_2178 = lean_nat_dec_lt(x_2175, x_2177);
if (x_2178 == 0)
{
uint8_t x_2179; 
x_2179 = lean_nat_dec_eq(x_2175, x_2177);
if (x_2179 == 0)
{
lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; 
x_2180 = lean_unsigned_to_nat(0u);
x_2181 = l_Array_extract___rarg(x_2138, x_2180, x_2177);
x_2182 = l_Array_extract___rarg(x_2138, x_2177, x_2175);
lean_dec(x_2175);
lean_dec(x_2138);
if (lean_is_scalar(x_2173)) {
 x_2183 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2183 = x_2173;
 lean_ctor_set_tag(x_2183, 6);
}
lean_ctor_set(x_2183, 0, x_102);
lean_ctor_set(x_2183, 1, x_2181);
x_2184 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_2183, x_2182, x_3, x_4, x_5, x_2172);
return x_2184;
}
else
{
lean_object* x_2185; lean_object* x_2186; 
lean_dec(x_2177);
lean_dec(x_2175);
if (lean_is_scalar(x_2173)) {
 x_2185 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2185 = x_2173;
 lean_ctor_set_tag(x_2185, 6);
}
lean_ctor_set(x_2185, 0, x_102);
lean_ctor_set(x_2185, 1, x_2138);
x_2186 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2185, x_3, x_4, x_5, x_2172);
return x_2186;
}
}
else
{
lean_object* x_2187; lean_object* x_2188; 
lean_dec(x_2177);
lean_dec(x_2175);
if (lean_is_scalar(x_2173)) {
 x_2187 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2187 = x_2173;
 lean_ctor_set_tag(x_2187, 7);
}
lean_ctor_set(x_2187, 0, x_102);
lean_ctor_set(x_2187, 1, x_2138);
x_2188 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2187, x_3, x_4, x_5, x_2172);
return x_2188;
}
}
}
else
{
lean_object* x_2189; lean_object* x_2190; 
lean_dec(x_2153);
lean_dec(x_2138);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2189 = lean_box(13);
if (lean_is_scalar(x_2146)) {
 x_2190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2190 = x_2146;
}
lean_ctor_set(x_2190, 0, x_2189);
lean_ctor_set(x_2190, 1, x_2145);
return x_2190;
}
}
else
{
lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; 
lean_dec(x_2153);
lean_dec(x_2146);
lean_dec(x_102);
x_2191 = l_Lean_IR_instInhabitedArg;
x_2192 = lean_unsigned_to_nat(2u);
x_2193 = lean_array_get(x_2191, x_2138, x_2192);
lean_dec(x_2138);
if (lean_obj_tag(x_2193) == 0)
{
lean_object* x_2194; lean_object* x_2195; 
x_2194 = lean_ctor_get(x_2193, 0);
lean_inc(x_2194);
lean_dec(x_2193);
x_2195 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2194, x_3, x_4, x_5, x_2145);
return x_2195;
}
else
{
lean_object* x_2196; lean_object* x_2197; 
x_2196 = lean_box(0);
x_2197 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2196, x_3, x_4, x_5, x_2145);
return x_2197;
}
}
}
case 2:
{
lean_object* x_2198; lean_object* x_2199; 
lean_dec(x_2152);
lean_dec(x_2147);
lean_dec(x_2146);
lean_dec(x_2138);
lean_dec(x_2130);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2198 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_2199 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2198, x_3, x_4, x_5, x_2145);
return x_2199;
}
case 4:
{
lean_object* x_2200; lean_object* x_2201; uint8_t x_2202; 
lean_dec(x_2147);
lean_dec(x_2146);
lean_dec(x_2130);
if (lean_is_exclusive(x_2152)) {
 lean_ctor_release(x_2152, 0);
 x_2200 = x_2152;
} else {
 lean_dec_ref(x_2152);
 x_2200 = lean_box(0);
}
x_2201 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_2202 = lean_name_eq(x_102, x_2201);
if (x_2202 == 0)
{
uint8_t x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; 
lean_dec(x_2138);
lean_dec(x_2);
lean_dec(x_1);
x_2203 = 1;
x_2204 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2205 = l_Lean_Name_toString(x_102, x_2203, x_2204);
if (lean_is_scalar(x_2200)) {
 x_2206 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2206 = x_2200;
 lean_ctor_set_tag(x_2206, 3);
}
lean_ctor_set(x_2206, 0, x_2205);
x_2207 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_2208 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2208, 0, x_2207);
lean_ctor_set(x_2208, 1, x_2206);
x_2209 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_2210 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2210, 0, x_2208);
lean_ctor_set(x_2210, 1, x_2209);
x_2211 = l_Lean_MessageData_ofFormat(x_2210);
x_2212 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2211, x_3, x_4, x_5, x_2145);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2212;
}
else
{
lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; 
lean_dec(x_2200);
lean_dec(x_102);
x_2213 = l_Lean_IR_instInhabitedArg;
x_2214 = lean_unsigned_to_nat(2u);
x_2215 = lean_array_get(x_2213, x_2138, x_2214);
lean_dec(x_2138);
if (lean_obj_tag(x_2215) == 0)
{
lean_object* x_2216; lean_object* x_2217; 
x_2216 = lean_ctor_get(x_2215, 0);
lean_inc(x_2216);
lean_dec(x_2215);
x_2217 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2216, x_3, x_4, x_5, x_2145);
return x_2217;
}
else
{
lean_object* x_2218; lean_object* x_2219; 
x_2218 = lean_box(0);
x_2219 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2218, x_3, x_4, x_5, x_2145);
return x_2219;
}
}
}
case 5:
{
lean_object* x_2220; lean_object* x_2221; 
lean_dec(x_2152);
lean_dec(x_2147);
lean_dec(x_2146);
lean_dec(x_2138);
lean_dec(x_2130);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2220 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_2221 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2220, x_3, x_4, x_5, x_2145);
return x_2221;
}
case 6:
{
lean_object* x_2222; uint8_t x_2223; 
lean_dec(x_2146);
x_2222 = lean_ctor_get(x_2152, 0);
lean_inc(x_2222);
lean_dec(x_2152);
lean_inc(x_102);
x_2223 = l_Lean_isExtern(x_2147, x_102);
if (x_2223 == 0)
{
lean_object* x_2224; 
lean_dec(x_2138);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2224 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_2145);
if (lean_obj_tag(x_2224) == 0)
{
lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; 
x_2225 = lean_ctor_get(x_2224, 0);
lean_inc(x_2225);
x_2226 = lean_ctor_get(x_2224, 1);
lean_inc(x_2226);
lean_dec(x_2224);
x_2227 = lean_ctor_get(x_2225, 0);
lean_inc(x_2227);
x_2228 = lean_ctor_get(x_2225, 1);
lean_inc(x_2228);
lean_dec(x_2225);
x_2229 = lean_ctor_get(x_2222, 3);
lean_inc(x_2229);
lean_dec(x_2222);
x_2230 = lean_array_get_size(x_2130);
x_2231 = l_Array_extract___rarg(x_2130, x_2229, x_2230);
lean_dec(x_2230);
lean_dec(x_2130);
x_2232 = lean_array_get_size(x_2228);
x_2233 = lean_unsigned_to_nat(0u);
x_2234 = lean_unsigned_to_nat(1u);
x_2235 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2235, 0, x_2233);
lean_ctor_set(x_2235, 1, x_2232);
lean_ctor_set(x_2235, 2, x_2234);
x_2236 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_2237 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4(x_2228, x_2231, x_2235, x_2235, x_2236, x_2233, lean_box(0), lean_box(0), x_3, x_4, x_5, x_2226);
lean_dec(x_2235);
x_2238 = lean_ctor_get(x_2237, 0);
lean_inc(x_2238);
x_2239 = lean_ctor_get(x_2237, 1);
lean_inc(x_2239);
lean_dec(x_2237);
x_2240 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_2227, x_2228, x_2231, x_2238, x_3, x_4, x_5, x_2239);
lean_dec(x_2231);
lean_dec(x_2228);
return x_2240;
}
else
{
lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; 
lean_dec(x_2222);
lean_dec(x_2130);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2241 = lean_ctor_get(x_2224, 0);
lean_inc(x_2241);
x_2242 = lean_ctor_get(x_2224, 1);
lean_inc(x_2242);
if (lean_is_exclusive(x_2224)) {
 lean_ctor_release(x_2224, 0);
 lean_ctor_release(x_2224, 1);
 x_2243 = x_2224;
} else {
 lean_dec_ref(x_2224);
 x_2243 = lean_box(0);
}
if (lean_is_scalar(x_2243)) {
 x_2244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2244 = x_2243;
}
lean_ctor_set(x_2244, 0, x_2241);
lean_ctor_set(x_2244, 1, x_2242);
return x_2244;
}
}
else
{
lean_object* x_2245; 
lean_dec(x_2222);
lean_dec(x_2130);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2138);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2245 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2138, x_3, x_4, x_5, x_2145);
if (lean_obj_tag(x_2245) == 0)
{
lean_object* x_2246; 
x_2246 = lean_ctor_get(x_2245, 0);
lean_inc(x_2246);
if (lean_obj_tag(x_2246) == 0)
{
lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; 
x_2247 = lean_ctor_get(x_2245, 1);
lean_inc(x_2247);
lean_dec(x_2245);
x_2248 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2248, 0, x_102);
lean_ctor_set(x_2248, 1, x_2138);
x_2249 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2248, x_3, x_4, x_5, x_2247);
return x_2249;
}
else
{
lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; 
lean_dec(x_2138);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2250 = lean_ctor_get(x_2245, 1);
lean_inc(x_2250);
if (lean_is_exclusive(x_2245)) {
 lean_ctor_release(x_2245, 0);
 lean_ctor_release(x_2245, 1);
 x_2251 = x_2245;
} else {
 lean_dec_ref(x_2245);
 x_2251 = lean_box(0);
}
x_2252 = lean_ctor_get(x_2246, 0);
lean_inc(x_2252);
lean_dec(x_2246);
if (lean_is_scalar(x_2251)) {
 x_2253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2253 = x_2251;
}
lean_ctor_set(x_2253, 0, x_2252);
lean_ctor_set(x_2253, 1, x_2250);
return x_2253;
}
}
else
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
lean_dec(x_2138);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2254 = lean_ctor_get(x_2245, 0);
lean_inc(x_2254);
x_2255 = lean_ctor_get(x_2245, 1);
lean_inc(x_2255);
if (lean_is_exclusive(x_2245)) {
 lean_ctor_release(x_2245, 0);
 lean_ctor_release(x_2245, 1);
 x_2256 = x_2245;
} else {
 lean_dec_ref(x_2245);
 x_2256 = lean_box(0);
}
if (lean_is_scalar(x_2256)) {
 x_2257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2257 = x_2256;
}
lean_ctor_set(x_2257, 0, x_2254);
lean_ctor_set(x_2257, 1, x_2255);
return x_2257;
}
}
}
case 7:
{
lean_object* x_2258; uint8_t x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; 
lean_dec(x_2147);
lean_dec(x_2146);
lean_dec(x_2138);
lean_dec(x_2130);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_2152)) {
 lean_ctor_release(x_2152, 0);
 x_2258 = x_2152;
} else {
 lean_dec_ref(x_2152);
 x_2258 = lean_box(0);
}
x_2259 = 1;
x_2260 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2261 = l_Lean_Name_toString(x_102, x_2259, x_2260);
if (lean_is_scalar(x_2258)) {
 x_2262 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2262 = x_2258;
 lean_ctor_set_tag(x_2262, 3);
}
lean_ctor_set(x_2262, 0, x_2261);
x_2263 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_2264 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2264, 0, x_2263);
lean_ctor_set(x_2264, 1, x_2262);
x_2265 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_2266 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2266, 0, x_2264);
lean_ctor_set(x_2266, 1, x_2265);
x_2267 = l_Lean_MessageData_ofFormat(x_2266);
x_2268 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2267, x_3, x_4, x_5, x_2145);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2268;
}
default: 
{
lean_object* x_2269; 
lean_dec(x_2152);
lean_dec(x_2147);
lean_dec(x_2146);
lean_dec(x_2130);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2138);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2269 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2138, x_3, x_4, x_5, x_2145);
if (lean_obj_tag(x_2269) == 0)
{
lean_object* x_2270; 
x_2270 = lean_ctor_get(x_2269, 0);
lean_inc(x_2270);
if (lean_obj_tag(x_2270) == 0)
{
lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; 
x_2271 = lean_ctor_get(x_2269, 1);
lean_inc(x_2271);
lean_dec(x_2269);
x_2272 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2272, 0, x_102);
lean_ctor_set(x_2272, 1, x_2138);
x_2273 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2272, x_3, x_4, x_5, x_2271);
return x_2273;
}
else
{
lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; 
lean_dec(x_2138);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2274 = lean_ctor_get(x_2269, 1);
lean_inc(x_2274);
if (lean_is_exclusive(x_2269)) {
 lean_ctor_release(x_2269, 0);
 lean_ctor_release(x_2269, 1);
 x_2275 = x_2269;
} else {
 lean_dec_ref(x_2269);
 x_2275 = lean_box(0);
}
x_2276 = lean_ctor_get(x_2270, 0);
lean_inc(x_2276);
lean_dec(x_2270);
if (lean_is_scalar(x_2275)) {
 x_2277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2277 = x_2275;
}
lean_ctor_set(x_2277, 0, x_2276);
lean_ctor_set(x_2277, 1, x_2274);
return x_2277;
}
}
else
{
lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; 
lean_dec(x_2138);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2278 = lean_ctor_get(x_2269, 0);
lean_inc(x_2278);
x_2279 = lean_ctor_get(x_2269, 1);
lean_inc(x_2279);
if (lean_is_exclusive(x_2269)) {
 lean_ctor_release(x_2269, 0);
 lean_ctor_release(x_2269, 1);
 x_2280 = x_2269;
} else {
 lean_dec_ref(x_2269);
 x_2280 = lean_box(0);
}
if (lean_is_scalar(x_2280)) {
 x_2281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2281 = x_2280;
}
lean_ctor_set(x_2281, 0, x_2278);
lean_ctor_set(x_2281, 1, x_2279);
return x_2281;
}
}
}
}
}
else
{
lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; 
lean_dec(x_2138);
lean_dec(x_2130);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2282 = lean_ctor_get(x_2140, 1);
lean_inc(x_2282);
if (lean_is_exclusive(x_2140)) {
 lean_ctor_release(x_2140, 0);
 lean_ctor_release(x_2140, 1);
 x_2283 = x_2140;
} else {
 lean_dec_ref(x_2140);
 x_2283 = lean_box(0);
}
x_2284 = lean_ctor_get(x_2141, 0);
lean_inc(x_2284);
lean_dec(x_2141);
if (lean_is_scalar(x_2283)) {
 x_2285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2285 = x_2283;
}
lean_ctor_set(x_2285, 0, x_2284);
lean_ctor_set(x_2285, 1, x_2282);
return x_2285;
}
}
else
{
lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; 
lean_dec(x_2138);
lean_dec(x_2130);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2286 = lean_ctor_get(x_2140, 0);
lean_inc(x_2286);
x_2287 = lean_ctor_get(x_2140, 1);
lean_inc(x_2287);
if (lean_is_exclusive(x_2140)) {
 lean_ctor_release(x_2140, 0);
 lean_ctor_release(x_2140, 1);
 x_2288 = x_2140;
} else {
 lean_dec_ref(x_2140);
 x_2288 = lean_box(0);
}
if (lean_is_scalar(x_2288)) {
 x_2289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2289 = x_2288;
}
lean_ctor_set(x_2289, 0, x_2286);
lean_ctor_set(x_2289, 1, x_2287);
return x_2289;
}
}
else
{
lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; 
lean_dec(x_2130);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2290 = lean_ctor_get(x_2137, 0);
lean_inc(x_2290);
x_2291 = lean_ctor_get(x_2137, 1);
lean_inc(x_2291);
if (lean_is_exclusive(x_2137)) {
 lean_ctor_release(x_2137, 0);
 lean_ctor_release(x_2137, 1);
 x_2292 = x_2137;
} else {
 lean_dec_ref(x_2137);
 x_2292 = lean_box(0);
}
if (lean_is_scalar(x_2292)) {
 x_2293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2293 = x_2292;
}
lean_ctor_set(x_2293, 0, x_2290);
lean_ctor_set(x_2293, 1, x_2291);
return x_2293;
}
}
else
{
lean_object* x_2294; uint8_t x_2295; 
lean_dec(x_102);
x_2294 = l_Lean_IR_ToIR_lowerLet___closed__33;
x_2295 = lean_string_dec_eq(x_2131, x_2294);
if (x_2295 == 0)
{
lean_object* x_2296; lean_object* x_2297; size_t x_2298; size_t x_2299; lean_object* x_2300; 
x_2296 = l_Lean_Name_str___override(x_1222, x_2133);
x_2297 = l_Lean_Name_str___override(x_2296, x_2131);
x_2298 = lean_array_size(x_2130);
x_2299 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2130);
x_2300 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_2298, x_2299, x_2130, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_2300) == 0)
{
lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; 
x_2301 = lean_ctor_get(x_2300, 0);
lean_inc(x_2301);
x_2302 = lean_ctor_get(x_2300, 1);
lean_inc(x_2302);
lean_dec(x_2300);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2301);
lean_inc(x_2297);
lean_inc(x_2);
lean_inc(x_1);
x_2303 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_2297, x_2301, x_3, x_4, x_5, x_2302);
if (lean_obj_tag(x_2303) == 0)
{
lean_object* x_2304; 
x_2304 = lean_ctor_get(x_2303, 0);
lean_inc(x_2304);
if (lean_obj_tag(x_2304) == 0)
{
lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; uint8_t x_2311; lean_object* x_2312; 
x_2305 = lean_ctor_get(x_2303, 1);
lean_inc(x_2305);
lean_dec(x_2303);
x_2306 = lean_st_ref_get(x_5, x_2305);
x_2307 = lean_ctor_get(x_2306, 0);
lean_inc(x_2307);
x_2308 = lean_ctor_get(x_2306, 1);
lean_inc(x_2308);
if (lean_is_exclusive(x_2306)) {
 lean_ctor_release(x_2306, 0);
 lean_ctor_release(x_2306, 1);
 x_2309 = x_2306;
} else {
 lean_dec_ref(x_2306);
 x_2309 = lean_box(0);
}
x_2310 = lean_ctor_get(x_2307, 0);
lean_inc(x_2310);
lean_dec(x_2307);
x_2311 = 0;
lean_inc(x_2297);
lean_inc(x_2310);
x_2312 = l_Lean_Environment_find_x3f(x_2310, x_2297, x_2311);
if (lean_obj_tag(x_2312) == 0)
{
lean_object* x_2313; lean_object* x_2314; 
lean_dec(x_2310);
lean_dec(x_2309);
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_2130);
lean_dec(x_2);
lean_dec(x_1);
x_2313 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2314 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2313, x_3, x_4, x_5, x_2308);
return x_2314;
}
else
{
lean_object* x_2315; 
x_2315 = lean_ctor_get(x_2312, 0);
lean_inc(x_2315);
lean_dec(x_2312);
switch (lean_obj_tag(x_2315)) {
case 0:
{
lean_object* x_2316; lean_object* x_2317; uint8_t x_2318; 
lean_dec(x_2310);
lean_dec(x_2130);
if (lean_is_exclusive(x_2315)) {
 lean_ctor_release(x_2315, 0);
 x_2316 = x_2315;
} else {
 lean_dec_ref(x_2315);
 x_2316 = lean_box(0);
}
x_2317 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2318 = lean_name_eq(x_2297, x_2317);
if (x_2318 == 0)
{
lean_object* x_2319; uint8_t x_2320; 
x_2319 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_2320 = lean_name_eq(x_2297, x_2319);
if (x_2320 == 0)
{
lean_object* x_2321; lean_object* x_2322; 
lean_dec(x_2309);
lean_inc(x_2297);
x_2321 = l_Lean_IR_ToIR_findDecl(x_2297, x_3, x_4, x_5, x_2308);
x_2322 = lean_ctor_get(x_2321, 0);
lean_inc(x_2322);
if (lean_obj_tag(x_2322) == 0)
{
lean_object* x_2323; lean_object* x_2324; uint8_t x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; 
lean_dec(x_2301);
lean_dec(x_2);
lean_dec(x_1);
x_2323 = lean_ctor_get(x_2321, 1);
lean_inc(x_2323);
if (lean_is_exclusive(x_2321)) {
 lean_ctor_release(x_2321, 0);
 lean_ctor_release(x_2321, 1);
 x_2324 = x_2321;
} else {
 lean_dec_ref(x_2321);
 x_2324 = lean_box(0);
}
x_2325 = 1;
x_2326 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2327 = l_Lean_Name_toString(x_2297, x_2325, x_2326);
if (lean_is_scalar(x_2316)) {
 x_2328 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2328 = x_2316;
 lean_ctor_set_tag(x_2328, 3);
}
lean_ctor_set(x_2328, 0, x_2327);
x_2329 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_2324)) {
 x_2330 = lean_alloc_ctor(5, 2, 0);
} else {
 x_2330 = x_2324;
 lean_ctor_set_tag(x_2330, 5);
}
lean_ctor_set(x_2330, 0, x_2329);
lean_ctor_set(x_2330, 1, x_2328);
x_2331 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2332 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2332, 0, x_2330);
lean_ctor_set(x_2332, 1, x_2331);
x_2333 = l_Lean_MessageData_ofFormat(x_2332);
x_2334 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2333, x_3, x_4, x_5, x_2323);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2334;
}
else
{
lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; uint8_t x_2341; 
lean_dec(x_2316);
x_2335 = lean_ctor_get(x_2321, 1);
lean_inc(x_2335);
if (lean_is_exclusive(x_2321)) {
 lean_ctor_release(x_2321, 0);
 lean_ctor_release(x_2321, 1);
 x_2336 = x_2321;
} else {
 lean_dec_ref(x_2321);
 x_2336 = lean_box(0);
}
x_2337 = lean_ctor_get(x_2322, 0);
lean_inc(x_2337);
lean_dec(x_2322);
x_2338 = lean_array_get_size(x_2301);
x_2339 = l_Lean_IR_Decl_params(x_2337);
lean_dec(x_2337);
x_2340 = lean_array_get_size(x_2339);
lean_dec(x_2339);
x_2341 = lean_nat_dec_lt(x_2338, x_2340);
if (x_2341 == 0)
{
uint8_t x_2342; 
x_2342 = lean_nat_dec_eq(x_2338, x_2340);
if (x_2342 == 0)
{
lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; 
x_2343 = lean_unsigned_to_nat(0u);
x_2344 = l_Array_extract___rarg(x_2301, x_2343, x_2340);
x_2345 = l_Array_extract___rarg(x_2301, x_2340, x_2338);
lean_dec(x_2338);
lean_dec(x_2301);
if (lean_is_scalar(x_2336)) {
 x_2346 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2346 = x_2336;
 lean_ctor_set_tag(x_2346, 6);
}
lean_ctor_set(x_2346, 0, x_2297);
lean_ctor_set(x_2346, 1, x_2344);
x_2347 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_2346, x_2345, x_3, x_4, x_5, x_2335);
return x_2347;
}
else
{
lean_object* x_2348; lean_object* x_2349; 
lean_dec(x_2340);
lean_dec(x_2338);
if (lean_is_scalar(x_2336)) {
 x_2348 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2348 = x_2336;
 lean_ctor_set_tag(x_2348, 6);
}
lean_ctor_set(x_2348, 0, x_2297);
lean_ctor_set(x_2348, 1, x_2301);
x_2349 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2348, x_3, x_4, x_5, x_2335);
return x_2349;
}
}
else
{
lean_object* x_2350; lean_object* x_2351; 
lean_dec(x_2340);
lean_dec(x_2338);
if (lean_is_scalar(x_2336)) {
 x_2350 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2350 = x_2336;
 lean_ctor_set_tag(x_2350, 7);
}
lean_ctor_set(x_2350, 0, x_2297);
lean_ctor_set(x_2350, 1, x_2301);
x_2351 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2350, x_3, x_4, x_5, x_2335);
return x_2351;
}
}
}
else
{
lean_object* x_2352; lean_object* x_2353; 
lean_dec(x_2316);
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2352 = lean_box(13);
if (lean_is_scalar(x_2309)) {
 x_2353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2353 = x_2309;
}
lean_ctor_set(x_2353, 0, x_2352);
lean_ctor_set(x_2353, 1, x_2308);
return x_2353;
}
}
else
{
lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; 
lean_dec(x_2316);
lean_dec(x_2309);
lean_dec(x_2297);
x_2354 = l_Lean_IR_instInhabitedArg;
x_2355 = lean_unsigned_to_nat(2u);
x_2356 = lean_array_get(x_2354, x_2301, x_2355);
lean_dec(x_2301);
if (lean_obj_tag(x_2356) == 0)
{
lean_object* x_2357; lean_object* x_2358; 
x_2357 = lean_ctor_get(x_2356, 0);
lean_inc(x_2357);
lean_dec(x_2356);
x_2358 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2357, x_3, x_4, x_5, x_2308);
return x_2358;
}
else
{
lean_object* x_2359; lean_object* x_2360; 
x_2359 = lean_box(0);
x_2360 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2359, x_3, x_4, x_5, x_2308);
return x_2360;
}
}
}
case 2:
{
lean_object* x_2361; lean_object* x_2362; 
lean_dec(x_2315);
lean_dec(x_2310);
lean_dec(x_2309);
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_2130);
lean_dec(x_2);
lean_dec(x_1);
x_2361 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_2362 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2361, x_3, x_4, x_5, x_2308);
return x_2362;
}
case 4:
{
lean_object* x_2363; lean_object* x_2364; uint8_t x_2365; 
lean_dec(x_2310);
lean_dec(x_2309);
lean_dec(x_2130);
if (lean_is_exclusive(x_2315)) {
 lean_ctor_release(x_2315, 0);
 x_2363 = x_2315;
} else {
 lean_dec_ref(x_2315);
 x_2363 = lean_box(0);
}
x_2364 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_2365 = lean_name_eq(x_2297, x_2364);
if (x_2365 == 0)
{
uint8_t x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; 
lean_dec(x_2301);
lean_dec(x_2);
lean_dec(x_1);
x_2366 = 1;
x_2367 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2368 = l_Lean_Name_toString(x_2297, x_2366, x_2367);
if (lean_is_scalar(x_2363)) {
 x_2369 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2369 = x_2363;
 lean_ctor_set_tag(x_2369, 3);
}
lean_ctor_set(x_2369, 0, x_2368);
x_2370 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_2371 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2371, 0, x_2370);
lean_ctor_set(x_2371, 1, x_2369);
x_2372 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_2373 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2373, 0, x_2371);
lean_ctor_set(x_2373, 1, x_2372);
x_2374 = l_Lean_MessageData_ofFormat(x_2373);
x_2375 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2374, x_3, x_4, x_5, x_2308);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2375;
}
else
{
lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; 
lean_dec(x_2363);
lean_dec(x_2297);
x_2376 = l_Lean_IR_instInhabitedArg;
x_2377 = lean_unsigned_to_nat(2u);
x_2378 = lean_array_get(x_2376, x_2301, x_2377);
lean_dec(x_2301);
if (lean_obj_tag(x_2378) == 0)
{
lean_object* x_2379; lean_object* x_2380; 
x_2379 = lean_ctor_get(x_2378, 0);
lean_inc(x_2379);
lean_dec(x_2378);
x_2380 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2379, x_3, x_4, x_5, x_2308);
return x_2380;
}
else
{
lean_object* x_2381; lean_object* x_2382; 
x_2381 = lean_box(0);
x_2382 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2381, x_3, x_4, x_5, x_2308);
return x_2382;
}
}
}
case 5:
{
lean_object* x_2383; lean_object* x_2384; 
lean_dec(x_2315);
lean_dec(x_2310);
lean_dec(x_2309);
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_2130);
lean_dec(x_2);
lean_dec(x_1);
x_2383 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_2384 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2383, x_3, x_4, x_5, x_2308);
return x_2384;
}
case 6:
{
lean_object* x_2385; uint8_t x_2386; 
lean_dec(x_2309);
x_2385 = lean_ctor_get(x_2315, 0);
lean_inc(x_2385);
lean_dec(x_2315);
lean_inc(x_2297);
x_2386 = l_Lean_isExtern(x_2310, x_2297);
if (x_2386 == 0)
{
lean_object* x_2387; 
lean_dec(x_2301);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2387 = l_Lean_IR_ToIR_getCtorInfo(x_2297, x_3, x_4, x_5, x_2308);
if (lean_obj_tag(x_2387) == 0)
{
lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; 
x_2388 = lean_ctor_get(x_2387, 0);
lean_inc(x_2388);
x_2389 = lean_ctor_get(x_2387, 1);
lean_inc(x_2389);
lean_dec(x_2387);
x_2390 = lean_ctor_get(x_2388, 0);
lean_inc(x_2390);
x_2391 = lean_ctor_get(x_2388, 1);
lean_inc(x_2391);
lean_dec(x_2388);
x_2392 = lean_ctor_get(x_2385, 3);
lean_inc(x_2392);
lean_dec(x_2385);
x_2393 = lean_array_get_size(x_2130);
x_2394 = l_Array_extract___rarg(x_2130, x_2392, x_2393);
lean_dec(x_2393);
lean_dec(x_2130);
x_2395 = lean_array_get_size(x_2391);
x_2396 = lean_unsigned_to_nat(0u);
x_2397 = lean_unsigned_to_nat(1u);
x_2398 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2398, 0, x_2396);
lean_ctor_set(x_2398, 1, x_2395);
lean_ctor_set(x_2398, 2, x_2397);
x_2399 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_2400 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5(x_2391, x_2394, x_2398, x_2398, x_2399, x_2396, lean_box(0), lean_box(0), x_3, x_4, x_5, x_2389);
lean_dec(x_2398);
x_2401 = lean_ctor_get(x_2400, 0);
lean_inc(x_2401);
x_2402 = lean_ctor_get(x_2400, 1);
lean_inc(x_2402);
lean_dec(x_2400);
x_2403 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_2390, x_2391, x_2394, x_2401, x_3, x_4, x_5, x_2402);
lean_dec(x_2394);
lean_dec(x_2391);
return x_2403;
}
else
{
lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; 
lean_dec(x_2385);
lean_dec(x_2130);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2404 = lean_ctor_get(x_2387, 0);
lean_inc(x_2404);
x_2405 = lean_ctor_get(x_2387, 1);
lean_inc(x_2405);
if (lean_is_exclusive(x_2387)) {
 lean_ctor_release(x_2387, 0);
 lean_ctor_release(x_2387, 1);
 x_2406 = x_2387;
} else {
 lean_dec_ref(x_2387);
 x_2406 = lean_box(0);
}
if (lean_is_scalar(x_2406)) {
 x_2407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2407 = x_2406;
}
lean_ctor_set(x_2407, 0, x_2404);
lean_ctor_set(x_2407, 1, x_2405);
return x_2407;
}
}
else
{
lean_object* x_2408; 
lean_dec(x_2385);
lean_dec(x_2130);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2301);
lean_inc(x_2297);
lean_inc(x_2);
lean_inc(x_1);
x_2408 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_2297, x_2301, x_3, x_4, x_5, x_2308);
if (lean_obj_tag(x_2408) == 0)
{
lean_object* x_2409; 
x_2409 = lean_ctor_get(x_2408, 0);
lean_inc(x_2409);
if (lean_obj_tag(x_2409) == 0)
{
lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; 
x_2410 = lean_ctor_get(x_2408, 1);
lean_inc(x_2410);
lean_dec(x_2408);
x_2411 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2411, 0, x_2297);
lean_ctor_set(x_2411, 1, x_2301);
x_2412 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2411, x_3, x_4, x_5, x_2410);
return x_2412;
}
else
{
lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; 
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2413 = lean_ctor_get(x_2408, 1);
lean_inc(x_2413);
if (lean_is_exclusive(x_2408)) {
 lean_ctor_release(x_2408, 0);
 lean_ctor_release(x_2408, 1);
 x_2414 = x_2408;
} else {
 lean_dec_ref(x_2408);
 x_2414 = lean_box(0);
}
x_2415 = lean_ctor_get(x_2409, 0);
lean_inc(x_2415);
lean_dec(x_2409);
if (lean_is_scalar(x_2414)) {
 x_2416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2416 = x_2414;
}
lean_ctor_set(x_2416, 0, x_2415);
lean_ctor_set(x_2416, 1, x_2413);
return x_2416;
}
}
else
{
lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; 
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2417 = lean_ctor_get(x_2408, 0);
lean_inc(x_2417);
x_2418 = lean_ctor_get(x_2408, 1);
lean_inc(x_2418);
if (lean_is_exclusive(x_2408)) {
 lean_ctor_release(x_2408, 0);
 lean_ctor_release(x_2408, 1);
 x_2419 = x_2408;
} else {
 lean_dec_ref(x_2408);
 x_2419 = lean_box(0);
}
if (lean_is_scalar(x_2419)) {
 x_2420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2420 = x_2419;
}
lean_ctor_set(x_2420, 0, x_2417);
lean_ctor_set(x_2420, 1, x_2418);
return x_2420;
}
}
}
case 7:
{
lean_object* x_2421; uint8_t x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; 
lean_dec(x_2310);
lean_dec(x_2309);
lean_dec(x_2301);
lean_dec(x_2130);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_2315)) {
 lean_ctor_release(x_2315, 0);
 x_2421 = x_2315;
} else {
 lean_dec_ref(x_2315);
 x_2421 = lean_box(0);
}
x_2422 = 1;
x_2423 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2424 = l_Lean_Name_toString(x_2297, x_2422, x_2423);
if (lean_is_scalar(x_2421)) {
 x_2425 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2425 = x_2421;
 lean_ctor_set_tag(x_2425, 3);
}
lean_ctor_set(x_2425, 0, x_2424);
x_2426 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_2427 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2427, 0, x_2426);
lean_ctor_set(x_2427, 1, x_2425);
x_2428 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_2429 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2429, 0, x_2427);
lean_ctor_set(x_2429, 1, x_2428);
x_2430 = l_Lean_MessageData_ofFormat(x_2429);
x_2431 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2430, x_3, x_4, x_5, x_2308);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2431;
}
default: 
{
lean_object* x_2432; 
lean_dec(x_2315);
lean_dec(x_2310);
lean_dec(x_2309);
lean_dec(x_2130);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2301);
lean_inc(x_2297);
lean_inc(x_2);
lean_inc(x_1);
x_2432 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_2297, x_2301, x_3, x_4, x_5, x_2308);
if (lean_obj_tag(x_2432) == 0)
{
lean_object* x_2433; 
x_2433 = lean_ctor_get(x_2432, 0);
lean_inc(x_2433);
if (lean_obj_tag(x_2433) == 0)
{
lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; 
x_2434 = lean_ctor_get(x_2432, 1);
lean_inc(x_2434);
lean_dec(x_2432);
x_2435 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2435, 0, x_2297);
lean_ctor_set(x_2435, 1, x_2301);
x_2436 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2435, x_3, x_4, x_5, x_2434);
return x_2436;
}
else
{
lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; 
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2437 = lean_ctor_get(x_2432, 1);
lean_inc(x_2437);
if (lean_is_exclusive(x_2432)) {
 lean_ctor_release(x_2432, 0);
 lean_ctor_release(x_2432, 1);
 x_2438 = x_2432;
} else {
 lean_dec_ref(x_2432);
 x_2438 = lean_box(0);
}
x_2439 = lean_ctor_get(x_2433, 0);
lean_inc(x_2439);
lean_dec(x_2433);
if (lean_is_scalar(x_2438)) {
 x_2440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2440 = x_2438;
}
lean_ctor_set(x_2440, 0, x_2439);
lean_ctor_set(x_2440, 1, x_2437);
return x_2440;
}
}
else
{
lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; 
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2441 = lean_ctor_get(x_2432, 0);
lean_inc(x_2441);
x_2442 = lean_ctor_get(x_2432, 1);
lean_inc(x_2442);
if (lean_is_exclusive(x_2432)) {
 lean_ctor_release(x_2432, 0);
 lean_ctor_release(x_2432, 1);
 x_2443 = x_2432;
} else {
 lean_dec_ref(x_2432);
 x_2443 = lean_box(0);
}
if (lean_is_scalar(x_2443)) {
 x_2444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2444 = x_2443;
}
lean_ctor_set(x_2444, 0, x_2441);
lean_ctor_set(x_2444, 1, x_2442);
return x_2444;
}
}
}
}
}
else
{
lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; 
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_2130);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2445 = lean_ctor_get(x_2303, 1);
lean_inc(x_2445);
if (lean_is_exclusive(x_2303)) {
 lean_ctor_release(x_2303, 0);
 lean_ctor_release(x_2303, 1);
 x_2446 = x_2303;
} else {
 lean_dec_ref(x_2303);
 x_2446 = lean_box(0);
}
x_2447 = lean_ctor_get(x_2304, 0);
lean_inc(x_2447);
lean_dec(x_2304);
if (lean_is_scalar(x_2446)) {
 x_2448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2448 = x_2446;
}
lean_ctor_set(x_2448, 0, x_2447);
lean_ctor_set(x_2448, 1, x_2445);
return x_2448;
}
}
else
{
lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; 
lean_dec(x_2301);
lean_dec(x_2297);
lean_dec(x_2130);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2449 = lean_ctor_get(x_2303, 0);
lean_inc(x_2449);
x_2450 = lean_ctor_get(x_2303, 1);
lean_inc(x_2450);
if (lean_is_exclusive(x_2303)) {
 lean_ctor_release(x_2303, 0);
 lean_ctor_release(x_2303, 1);
 x_2451 = x_2303;
} else {
 lean_dec_ref(x_2303);
 x_2451 = lean_box(0);
}
if (lean_is_scalar(x_2451)) {
 x_2452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2452 = x_2451;
}
lean_ctor_set(x_2452, 0, x_2449);
lean_ctor_set(x_2452, 1, x_2450);
return x_2452;
}
}
else
{
lean_object* x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; 
lean_dec(x_2297);
lean_dec(x_2130);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2453 = lean_ctor_get(x_2300, 0);
lean_inc(x_2453);
x_2454 = lean_ctor_get(x_2300, 1);
lean_inc(x_2454);
if (lean_is_exclusive(x_2300)) {
 lean_ctor_release(x_2300, 0);
 lean_ctor_release(x_2300, 1);
 x_2455 = x_2300;
} else {
 lean_dec_ref(x_2300);
 x_2455 = lean_box(0);
}
if (lean_is_scalar(x_2455)) {
 x_2456 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2456 = x_2455;
}
lean_ctor_set(x_2456, 0, x_2453);
lean_ctor_set(x_2456, 1, x_2454);
return x_2456;
}
}
else
{
size_t x_2457; size_t x_2458; lean_object* x_2459; 
lean_dec(x_2131);
x_2457 = lean_array_size(x_2130);
x_2458 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2459 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_2457, x_2458, x_2130, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_2459) == 0)
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; 
x_2460 = lean_ctor_get(x_2459, 0);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_2459, 1);
lean_inc(x_2461);
lean_dec(x_2459);
x_2462 = lean_ctor_get(x_1, 0);
lean_inc(x_2462);
lean_dec(x_1);
x_2463 = l_Lean_IR_ToIR_bindVar(x_2462, x_3, x_4, x_5, x_2461);
x_2464 = lean_ctor_get(x_2463, 0);
lean_inc(x_2464);
x_2465 = lean_ctor_get(x_2463, 1);
lean_inc(x_2465);
if (lean_is_exclusive(x_2463)) {
 lean_ctor_release(x_2463, 0);
 lean_ctor_release(x_2463, 1);
 x_2466 = x_2463;
} else {
 lean_dec_ref(x_2463);
 x_2466 = lean_box(0);
}
x_2467 = l_Lean_IR_ToIR_newVar(x_3, x_4, x_5, x_2465);
x_2468 = lean_ctor_get(x_2467, 0);
lean_inc(x_2468);
x_2469 = lean_ctor_get(x_2467, 1);
lean_inc(x_2469);
if (lean_is_exclusive(x_2467)) {
 lean_ctor_release(x_2467, 0);
 lean_ctor_release(x_2467, 1);
 x_2470 = x_2467;
} else {
 lean_dec_ref(x_2467);
 x_2470 = lean_box(0);
}
x_2471 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5, x_2469);
if (lean_obj_tag(x_2471) == 0)
{
lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; 
x_2472 = lean_ctor_get(x_2471, 0);
lean_inc(x_2472);
x_2473 = lean_ctor_get(x_2471, 1);
lean_inc(x_2473);
if (lean_is_exclusive(x_2471)) {
 lean_ctor_release(x_2471, 0);
 lean_ctor_release(x_2471, 1);
 x_2474 = x_2471;
} else {
 lean_dec_ref(x_2471);
 x_2474 = lean_box(0);
}
x_2475 = l_Lean_IR_instInhabitedArg;
x_2476 = lean_unsigned_to_nat(0u);
x_2477 = lean_array_get(x_2475, x_2460, x_2476);
lean_dec(x_2460);
lean_inc(x_2468);
x_2478 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2478, 0, x_2468);
x_2479 = lean_box(0);
if (lean_is_scalar(x_2470)) {
 x_2480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2480 = x_2470;
 lean_ctor_set_tag(x_2480, 1);
}
lean_ctor_set(x_2480, 0, x_2478);
lean_ctor_set(x_2480, 1, x_2479);
if (lean_is_scalar(x_2466)) {
 x_2481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2481 = x_2466;
 lean_ctor_set_tag(x_2481, 1);
}
lean_ctor_set(x_2481, 0, x_2477);
lean_ctor_set(x_2481, 1, x_2480);
x_2482 = lean_array_mk(x_2481);
x_2483 = l_Lean_IR_ToIR_lowerLet___closed__35;
x_2484 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2484, 0, x_2483);
lean_ctor_set(x_2484, 1, x_2482);
x_2485 = lean_box(7);
x_2486 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2486, 0, x_2464);
lean_ctor_set(x_2486, 1, x_2485);
lean_ctor_set(x_2486, 2, x_2484);
lean_ctor_set(x_2486, 3, x_2472);
x_2487 = l_Lean_IR_ToIR_lowerLet___closed__37;
x_2488 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2488, 0, x_2468);
lean_ctor_set(x_2488, 1, x_2485);
lean_ctor_set(x_2488, 2, x_2487);
lean_ctor_set(x_2488, 3, x_2486);
if (lean_is_scalar(x_2474)) {
 x_2489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2489 = x_2474;
}
lean_ctor_set(x_2489, 0, x_2488);
lean_ctor_set(x_2489, 1, x_2473);
return x_2489;
}
else
{
lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; 
lean_dec(x_2470);
lean_dec(x_2468);
lean_dec(x_2466);
lean_dec(x_2464);
lean_dec(x_2460);
x_2490 = lean_ctor_get(x_2471, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2471, 1);
lean_inc(x_2491);
if (lean_is_exclusive(x_2471)) {
 lean_ctor_release(x_2471, 0);
 lean_ctor_release(x_2471, 1);
 x_2492 = x_2471;
} else {
 lean_dec_ref(x_2471);
 x_2492 = lean_box(0);
}
if (lean_is_scalar(x_2492)) {
 x_2493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2493 = x_2492;
}
lean_ctor_set(x_2493, 0, x_2490);
lean_ctor_set(x_2493, 1, x_2491);
return x_2493;
}
}
else
{
lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2494 = lean_ctor_get(x_2459, 0);
lean_inc(x_2494);
x_2495 = lean_ctor_get(x_2459, 1);
lean_inc(x_2495);
if (lean_is_exclusive(x_2459)) {
 lean_ctor_release(x_2459, 0);
 lean_ctor_release(x_2459, 1);
 x_2496 = x_2459;
} else {
 lean_dec_ref(x_2459);
 x_2496 = lean_box(0);
}
if (lean_is_scalar(x_2496)) {
 x_2497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2497 = x_2496;
}
lean_ctor_set(x_2497, 0, x_2494);
lean_ctor_set(x_2497, 1, x_2495);
return x_2497;
}
}
}
}
}
case 1:
{
uint8_t x_2498; 
lean_dec(x_1222);
lean_dec(x_662);
x_2498 = !lean_is_exclusive(x_7);
if (x_2498 == 0)
{
lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; size_t x_2502; size_t x_2503; lean_object* x_2504; 
x_2499 = lean_ctor_get(x_7, 2);
x_2500 = lean_ctor_get(x_7, 1);
lean_dec(x_2500);
x_2501 = lean_ctor_get(x_7, 0);
lean_dec(x_2501);
x_2502 = lean_array_size(x_2499);
x_2503 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2499);
x_2504 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_2502, x_2503, x_2499, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_2504) == 0)
{
lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; 
x_2505 = lean_ctor_get(x_2504, 0);
lean_inc(x_2505);
x_2506 = lean_ctor_get(x_2504, 1);
lean_inc(x_2506);
lean_dec(x_2504);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2505);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2507 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2505, x_3, x_4, x_5, x_2506);
if (lean_obj_tag(x_2507) == 0)
{
lean_object* x_2508; 
x_2508 = lean_ctor_get(x_2507, 0);
lean_inc(x_2508);
if (lean_obj_tag(x_2508) == 0)
{
lean_object* x_2509; lean_object* x_2510; uint8_t x_2511; 
x_2509 = lean_ctor_get(x_2507, 1);
lean_inc(x_2509);
lean_dec(x_2507);
x_2510 = lean_st_ref_get(x_5, x_2509);
x_2511 = !lean_is_exclusive(x_2510);
if (x_2511 == 0)
{
lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; uint8_t x_2515; lean_object* x_2516; 
x_2512 = lean_ctor_get(x_2510, 0);
x_2513 = lean_ctor_get(x_2510, 1);
x_2514 = lean_ctor_get(x_2512, 0);
lean_inc(x_2514);
lean_dec(x_2512);
x_2515 = 0;
lean_inc(x_102);
lean_inc(x_2514);
x_2516 = l_Lean_Environment_find_x3f(x_2514, x_102, x_2515);
if (lean_obj_tag(x_2516) == 0)
{
lean_object* x_2517; lean_object* x_2518; 
lean_dec(x_2514);
lean_free_object(x_2510);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2517 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2518 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2517, x_3, x_4, x_5, x_2513);
return x_2518;
}
else
{
lean_object* x_2519; 
x_2519 = lean_ctor_get(x_2516, 0);
lean_inc(x_2519);
lean_dec(x_2516);
switch (lean_obj_tag(x_2519)) {
case 0:
{
uint8_t x_2520; 
lean_dec(x_2514);
lean_free_object(x_7);
lean_dec(x_2499);
x_2520 = !lean_is_exclusive(x_2519);
if (x_2520 == 0)
{
lean_object* x_2521; lean_object* x_2522; uint8_t x_2523; 
x_2521 = lean_ctor_get(x_2519, 0);
lean_dec(x_2521);
x_2522 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2523 = lean_name_eq(x_102, x_2522);
if (x_2523 == 0)
{
lean_object* x_2524; uint8_t x_2525; 
x_2524 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_2525 = lean_name_eq(x_102, x_2524);
if (x_2525 == 0)
{
lean_object* x_2526; lean_object* x_2527; 
lean_free_object(x_2510);
lean_inc(x_102);
x_2526 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_2513);
x_2527 = lean_ctor_get(x_2526, 0);
lean_inc(x_2527);
if (lean_obj_tag(x_2527) == 0)
{
uint8_t x_2528; 
lean_dec(x_2505);
lean_dec(x_2);
lean_dec(x_1);
x_2528 = !lean_is_exclusive(x_2526);
if (x_2528 == 0)
{
lean_object* x_2529; lean_object* x_2530; uint8_t x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; 
x_2529 = lean_ctor_get(x_2526, 1);
x_2530 = lean_ctor_get(x_2526, 0);
lean_dec(x_2530);
x_2531 = 1;
x_2532 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2533 = l_Lean_Name_toString(x_102, x_2531, x_2532);
lean_ctor_set_tag(x_2519, 3);
lean_ctor_set(x_2519, 0, x_2533);
x_2534 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_2526, 5);
lean_ctor_set(x_2526, 1, x_2519);
lean_ctor_set(x_2526, 0, x_2534);
x_2535 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2536 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2536, 0, x_2526);
lean_ctor_set(x_2536, 1, x_2535);
x_2537 = l_Lean_MessageData_ofFormat(x_2536);
x_2538 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2537, x_3, x_4, x_5, x_2529);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2538;
}
else
{
lean_object* x_2539; uint8_t x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; lean_object* x_2548; 
x_2539 = lean_ctor_get(x_2526, 1);
lean_inc(x_2539);
lean_dec(x_2526);
x_2540 = 1;
x_2541 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2542 = l_Lean_Name_toString(x_102, x_2540, x_2541);
lean_ctor_set_tag(x_2519, 3);
lean_ctor_set(x_2519, 0, x_2542);
x_2543 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_2544 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2544, 0, x_2543);
lean_ctor_set(x_2544, 1, x_2519);
x_2545 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2546 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2546, 0, x_2544);
lean_ctor_set(x_2546, 1, x_2545);
x_2547 = l_Lean_MessageData_ofFormat(x_2546);
x_2548 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2547, x_3, x_4, x_5, x_2539);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2548;
}
}
else
{
uint8_t x_2549; 
lean_free_object(x_2519);
x_2549 = !lean_is_exclusive(x_2526);
if (x_2549 == 0)
{
lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; uint8_t x_2556; 
x_2550 = lean_ctor_get(x_2526, 1);
x_2551 = lean_ctor_get(x_2526, 0);
lean_dec(x_2551);
x_2552 = lean_ctor_get(x_2527, 0);
lean_inc(x_2552);
lean_dec(x_2527);
x_2553 = lean_array_get_size(x_2505);
x_2554 = l_Lean_IR_Decl_params(x_2552);
lean_dec(x_2552);
x_2555 = lean_array_get_size(x_2554);
lean_dec(x_2554);
x_2556 = lean_nat_dec_lt(x_2553, x_2555);
if (x_2556 == 0)
{
uint8_t x_2557; 
x_2557 = lean_nat_dec_eq(x_2553, x_2555);
if (x_2557 == 0)
{
lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; 
x_2558 = lean_unsigned_to_nat(0u);
x_2559 = l_Array_extract___rarg(x_2505, x_2558, x_2555);
x_2560 = l_Array_extract___rarg(x_2505, x_2555, x_2553);
lean_dec(x_2553);
lean_dec(x_2505);
lean_ctor_set_tag(x_2526, 6);
lean_ctor_set(x_2526, 1, x_2559);
lean_ctor_set(x_2526, 0, x_102);
x_2561 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_2526, x_2560, x_3, x_4, x_5, x_2550);
return x_2561;
}
else
{
lean_object* x_2562; 
lean_dec(x_2555);
lean_dec(x_2553);
lean_ctor_set_tag(x_2526, 6);
lean_ctor_set(x_2526, 1, x_2505);
lean_ctor_set(x_2526, 0, x_102);
x_2562 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2526, x_3, x_4, x_5, x_2550);
return x_2562;
}
}
else
{
lean_object* x_2563; 
lean_dec(x_2555);
lean_dec(x_2553);
lean_ctor_set_tag(x_2526, 7);
lean_ctor_set(x_2526, 1, x_2505);
lean_ctor_set(x_2526, 0, x_102);
x_2563 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2526, x_3, x_4, x_5, x_2550);
return x_2563;
}
}
else
{
lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; uint8_t x_2569; 
x_2564 = lean_ctor_get(x_2526, 1);
lean_inc(x_2564);
lean_dec(x_2526);
x_2565 = lean_ctor_get(x_2527, 0);
lean_inc(x_2565);
lean_dec(x_2527);
x_2566 = lean_array_get_size(x_2505);
x_2567 = l_Lean_IR_Decl_params(x_2565);
lean_dec(x_2565);
x_2568 = lean_array_get_size(x_2567);
lean_dec(x_2567);
x_2569 = lean_nat_dec_lt(x_2566, x_2568);
if (x_2569 == 0)
{
uint8_t x_2570; 
x_2570 = lean_nat_dec_eq(x_2566, x_2568);
if (x_2570 == 0)
{
lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; 
x_2571 = lean_unsigned_to_nat(0u);
x_2572 = l_Array_extract___rarg(x_2505, x_2571, x_2568);
x_2573 = l_Array_extract___rarg(x_2505, x_2568, x_2566);
lean_dec(x_2566);
lean_dec(x_2505);
x_2574 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2574, 0, x_102);
lean_ctor_set(x_2574, 1, x_2572);
x_2575 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_2574, x_2573, x_3, x_4, x_5, x_2564);
return x_2575;
}
else
{
lean_object* x_2576; lean_object* x_2577; 
lean_dec(x_2568);
lean_dec(x_2566);
x_2576 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2576, 0, x_102);
lean_ctor_set(x_2576, 1, x_2505);
x_2577 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2576, x_3, x_4, x_5, x_2564);
return x_2577;
}
}
else
{
lean_object* x_2578; lean_object* x_2579; 
lean_dec(x_2568);
lean_dec(x_2566);
x_2578 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2578, 0, x_102);
lean_ctor_set(x_2578, 1, x_2505);
x_2579 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2578, x_3, x_4, x_5, x_2564);
return x_2579;
}
}
}
}
else
{
lean_object* x_2580; 
lean_free_object(x_2519);
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2580 = lean_box(13);
lean_ctor_set(x_2510, 0, x_2580);
return x_2510;
}
}
else
{
lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; 
lean_free_object(x_2519);
lean_free_object(x_2510);
lean_dec(x_102);
x_2581 = l_Lean_IR_instInhabitedArg;
x_2582 = lean_unsigned_to_nat(2u);
x_2583 = lean_array_get(x_2581, x_2505, x_2582);
lean_dec(x_2505);
if (lean_obj_tag(x_2583) == 0)
{
lean_object* x_2584; lean_object* x_2585; 
x_2584 = lean_ctor_get(x_2583, 0);
lean_inc(x_2584);
lean_dec(x_2583);
x_2585 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2584, x_3, x_4, x_5, x_2513);
return x_2585;
}
else
{
lean_object* x_2586; lean_object* x_2587; 
x_2586 = lean_box(0);
x_2587 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2586, x_3, x_4, x_5, x_2513);
return x_2587;
}
}
}
else
{
lean_object* x_2588; uint8_t x_2589; 
lean_dec(x_2519);
x_2588 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2589 = lean_name_eq(x_102, x_2588);
if (x_2589 == 0)
{
lean_object* x_2590; uint8_t x_2591; 
x_2590 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_2591 = lean_name_eq(x_102, x_2590);
if (x_2591 == 0)
{
lean_object* x_2592; lean_object* x_2593; 
lean_free_object(x_2510);
lean_inc(x_102);
x_2592 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_2513);
x_2593 = lean_ctor_get(x_2592, 0);
lean_inc(x_2593);
if (lean_obj_tag(x_2593) == 0)
{
lean_object* x_2594; lean_object* x_2595; uint8_t x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; 
lean_dec(x_2505);
lean_dec(x_2);
lean_dec(x_1);
x_2594 = lean_ctor_get(x_2592, 1);
lean_inc(x_2594);
if (lean_is_exclusive(x_2592)) {
 lean_ctor_release(x_2592, 0);
 lean_ctor_release(x_2592, 1);
 x_2595 = x_2592;
} else {
 lean_dec_ref(x_2592);
 x_2595 = lean_box(0);
}
x_2596 = 1;
x_2597 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2598 = l_Lean_Name_toString(x_102, x_2596, x_2597);
x_2599 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2599, 0, x_2598);
x_2600 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_2595)) {
 x_2601 = lean_alloc_ctor(5, 2, 0);
} else {
 x_2601 = x_2595;
 lean_ctor_set_tag(x_2601, 5);
}
lean_ctor_set(x_2601, 0, x_2600);
lean_ctor_set(x_2601, 1, x_2599);
x_2602 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2603 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2603, 0, x_2601);
lean_ctor_set(x_2603, 1, x_2602);
x_2604 = l_Lean_MessageData_ofFormat(x_2603);
x_2605 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2604, x_3, x_4, x_5, x_2594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2605;
}
else
{
lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; uint8_t x_2612; 
x_2606 = lean_ctor_get(x_2592, 1);
lean_inc(x_2606);
if (lean_is_exclusive(x_2592)) {
 lean_ctor_release(x_2592, 0);
 lean_ctor_release(x_2592, 1);
 x_2607 = x_2592;
} else {
 lean_dec_ref(x_2592);
 x_2607 = lean_box(0);
}
x_2608 = lean_ctor_get(x_2593, 0);
lean_inc(x_2608);
lean_dec(x_2593);
x_2609 = lean_array_get_size(x_2505);
x_2610 = l_Lean_IR_Decl_params(x_2608);
lean_dec(x_2608);
x_2611 = lean_array_get_size(x_2610);
lean_dec(x_2610);
x_2612 = lean_nat_dec_lt(x_2609, x_2611);
if (x_2612 == 0)
{
uint8_t x_2613; 
x_2613 = lean_nat_dec_eq(x_2609, x_2611);
if (x_2613 == 0)
{
lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; 
x_2614 = lean_unsigned_to_nat(0u);
x_2615 = l_Array_extract___rarg(x_2505, x_2614, x_2611);
x_2616 = l_Array_extract___rarg(x_2505, x_2611, x_2609);
lean_dec(x_2609);
lean_dec(x_2505);
if (lean_is_scalar(x_2607)) {
 x_2617 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2617 = x_2607;
 lean_ctor_set_tag(x_2617, 6);
}
lean_ctor_set(x_2617, 0, x_102);
lean_ctor_set(x_2617, 1, x_2615);
x_2618 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_2617, x_2616, x_3, x_4, x_5, x_2606);
return x_2618;
}
else
{
lean_object* x_2619; lean_object* x_2620; 
lean_dec(x_2611);
lean_dec(x_2609);
if (lean_is_scalar(x_2607)) {
 x_2619 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2619 = x_2607;
 lean_ctor_set_tag(x_2619, 6);
}
lean_ctor_set(x_2619, 0, x_102);
lean_ctor_set(x_2619, 1, x_2505);
x_2620 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2619, x_3, x_4, x_5, x_2606);
return x_2620;
}
}
else
{
lean_object* x_2621; lean_object* x_2622; 
lean_dec(x_2611);
lean_dec(x_2609);
if (lean_is_scalar(x_2607)) {
 x_2621 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2621 = x_2607;
 lean_ctor_set_tag(x_2621, 7);
}
lean_ctor_set(x_2621, 0, x_102);
lean_ctor_set(x_2621, 1, x_2505);
x_2622 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2621, x_3, x_4, x_5, x_2606);
return x_2622;
}
}
}
else
{
lean_object* x_2623; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2623 = lean_box(13);
lean_ctor_set(x_2510, 0, x_2623);
return x_2510;
}
}
else
{
lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; 
lean_free_object(x_2510);
lean_dec(x_102);
x_2624 = l_Lean_IR_instInhabitedArg;
x_2625 = lean_unsigned_to_nat(2u);
x_2626 = lean_array_get(x_2624, x_2505, x_2625);
lean_dec(x_2505);
if (lean_obj_tag(x_2626) == 0)
{
lean_object* x_2627; lean_object* x_2628; 
x_2627 = lean_ctor_get(x_2626, 0);
lean_inc(x_2627);
lean_dec(x_2626);
x_2628 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2627, x_3, x_4, x_5, x_2513);
return x_2628;
}
else
{
lean_object* x_2629; lean_object* x_2630; 
x_2629 = lean_box(0);
x_2630 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2629, x_3, x_4, x_5, x_2513);
return x_2630;
}
}
}
}
case 2:
{
lean_object* x_2631; lean_object* x_2632; 
lean_dec(x_2519);
lean_dec(x_2514);
lean_free_object(x_2510);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2631 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_2632 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2631, x_3, x_4, x_5, x_2513);
return x_2632;
}
case 4:
{
uint8_t x_2633; 
lean_dec(x_2514);
lean_free_object(x_2510);
lean_free_object(x_7);
lean_dec(x_2499);
x_2633 = !lean_is_exclusive(x_2519);
if (x_2633 == 0)
{
lean_object* x_2634; lean_object* x_2635; uint8_t x_2636; 
x_2634 = lean_ctor_get(x_2519, 0);
lean_dec(x_2634);
x_2635 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_2636 = lean_name_eq(x_102, x_2635);
if (x_2636 == 0)
{
uint8_t x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; 
lean_dec(x_2505);
lean_dec(x_2);
lean_dec(x_1);
x_2637 = 1;
x_2638 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2639 = l_Lean_Name_toString(x_102, x_2637, x_2638);
lean_ctor_set_tag(x_2519, 3);
lean_ctor_set(x_2519, 0, x_2639);
x_2640 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_2641 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2641, 0, x_2640);
lean_ctor_set(x_2641, 1, x_2519);
x_2642 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_2643 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2643, 0, x_2641);
lean_ctor_set(x_2643, 1, x_2642);
x_2644 = l_Lean_MessageData_ofFormat(x_2643);
x_2645 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2644, x_3, x_4, x_5, x_2513);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2645;
}
else
{
lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; 
lean_free_object(x_2519);
lean_dec(x_102);
x_2646 = l_Lean_IR_instInhabitedArg;
x_2647 = lean_unsigned_to_nat(2u);
x_2648 = lean_array_get(x_2646, x_2505, x_2647);
lean_dec(x_2505);
if (lean_obj_tag(x_2648) == 0)
{
lean_object* x_2649; lean_object* x_2650; 
x_2649 = lean_ctor_get(x_2648, 0);
lean_inc(x_2649);
lean_dec(x_2648);
x_2650 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2649, x_3, x_4, x_5, x_2513);
return x_2650;
}
else
{
lean_object* x_2651; lean_object* x_2652; 
x_2651 = lean_box(0);
x_2652 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2651, x_3, x_4, x_5, x_2513);
return x_2652;
}
}
}
else
{
lean_object* x_2653; uint8_t x_2654; 
lean_dec(x_2519);
x_2653 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_2654 = lean_name_eq(x_102, x_2653);
if (x_2654 == 0)
{
uint8_t x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; 
lean_dec(x_2505);
lean_dec(x_2);
lean_dec(x_1);
x_2655 = 1;
x_2656 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2657 = l_Lean_Name_toString(x_102, x_2655, x_2656);
x_2658 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2658, 0, x_2657);
x_2659 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_2660 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2660, 0, x_2659);
lean_ctor_set(x_2660, 1, x_2658);
x_2661 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_2662 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2662, 0, x_2660);
lean_ctor_set(x_2662, 1, x_2661);
x_2663 = l_Lean_MessageData_ofFormat(x_2662);
x_2664 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2663, x_3, x_4, x_5, x_2513);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2664;
}
else
{
lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; 
lean_dec(x_102);
x_2665 = l_Lean_IR_instInhabitedArg;
x_2666 = lean_unsigned_to_nat(2u);
x_2667 = lean_array_get(x_2665, x_2505, x_2666);
lean_dec(x_2505);
if (lean_obj_tag(x_2667) == 0)
{
lean_object* x_2668; lean_object* x_2669; 
x_2668 = lean_ctor_get(x_2667, 0);
lean_inc(x_2668);
lean_dec(x_2667);
x_2669 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2668, x_3, x_4, x_5, x_2513);
return x_2669;
}
else
{
lean_object* x_2670; lean_object* x_2671; 
x_2670 = lean_box(0);
x_2671 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2670, x_3, x_4, x_5, x_2513);
return x_2671;
}
}
}
}
case 5:
{
lean_object* x_2672; lean_object* x_2673; 
lean_dec(x_2519);
lean_dec(x_2514);
lean_free_object(x_2510);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2672 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_2673 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2672, x_3, x_4, x_5, x_2513);
return x_2673;
}
case 6:
{
lean_object* x_2674; uint8_t x_2675; 
lean_free_object(x_2510);
x_2674 = lean_ctor_get(x_2519, 0);
lean_inc(x_2674);
lean_dec(x_2519);
lean_inc(x_102);
x_2675 = l_Lean_isExtern(x_2514, x_102);
if (x_2675 == 0)
{
lean_object* x_2676; 
lean_dec(x_2505);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2676 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_2513);
if (lean_obj_tag(x_2676) == 0)
{
lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; 
x_2677 = lean_ctor_get(x_2676, 0);
lean_inc(x_2677);
x_2678 = lean_ctor_get(x_2676, 1);
lean_inc(x_2678);
lean_dec(x_2676);
x_2679 = lean_ctor_get(x_2677, 0);
lean_inc(x_2679);
x_2680 = lean_ctor_get(x_2677, 1);
lean_inc(x_2680);
lean_dec(x_2677);
x_2681 = lean_ctor_get(x_2674, 3);
lean_inc(x_2681);
lean_dec(x_2674);
x_2682 = lean_array_get_size(x_2499);
x_2683 = l_Array_extract___rarg(x_2499, x_2681, x_2682);
lean_dec(x_2682);
lean_dec(x_2499);
x_2684 = lean_array_get_size(x_2680);
x_2685 = lean_unsigned_to_nat(0u);
x_2686 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_2686);
lean_ctor_set(x_7, 1, x_2684);
lean_ctor_set(x_7, 0, x_2685);
x_2687 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_2688 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6(x_2680, x_2683, x_7, x_7, x_2687, x_2685, lean_box(0), lean_box(0), x_3, x_4, x_5, x_2678);
lean_dec(x_7);
x_2689 = lean_ctor_get(x_2688, 0);
lean_inc(x_2689);
x_2690 = lean_ctor_get(x_2688, 1);
lean_inc(x_2690);
lean_dec(x_2688);
x_2691 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_2679, x_2680, x_2683, x_2689, x_3, x_4, x_5, x_2690);
lean_dec(x_2683);
lean_dec(x_2680);
return x_2691;
}
else
{
uint8_t x_2692; 
lean_dec(x_2674);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2692 = !lean_is_exclusive(x_2676);
if (x_2692 == 0)
{
return x_2676;
}
else
{
lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; 
x_2693 = lean_ctor_get(x_2676, 0);
x_2694 = lean_ctor_get(x_2676, 1);
lean_inc(x_2694);
lean_inc(x_2693);
lean_dec(x_2676);
x_2695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2695, 0, x_2693);
lean_ctor_set(x_2695, 1, x_2694);
return x_2695;
}
}
}
else
{
lean_object* x_2696; 
lean_dec(x_2674);
lean_free_object(x_7);
lean_dec(x_2499);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2505);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2696 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2505, x_3, x_4, x_5, x_2513);
if (lean_obj_tag(x_2696) == 0)
{
lean_object* x_2697; 
x_2697 = lean_ctor_get(x_2696, 0);
lean_inc(x_2697);
if (lean_obj_tag(x_2697) == 0)
{
lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; 
x_2698 = lean_ctor_get(x_2696, 1);
lean_inc(x_2698);
lean_dec(x_2696);
x_2699 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2699, 0, x_102);
lean_ctor_set(x_2699, 1, x_2505);
x_2700 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2699, x_3, x_4, x_5, x_2698);
return x_2700;
}
else
{
uint8_t x_2701; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2701 = !lean_is_exclusive(x_2696);
if (x_2701 == 0)
{
lean_object* x_2702; lean_object* x_2703; 
x_2702 = lean_ctor_get(x_2696, 0);
lean_dec(x_2702);
x_2703 = lean_ctor_get(x_2697, 0);
lean_inc(x_2703);
lean_dec(x_2697);
lean_ctor_set(x_2696, 0, x_2703);
return x_2696;
}
else
{
lean_object* x_2704; lean_object* x_2705; lean_object* x_2706; 
x_2704 = lean_ctor_get(x_2696, 1);
lean_inc(x_2704);
lean_dec(x_2696);
x_2705 = lean_ctor_get(x_2697, 0);
lean_inc(x_2705);
lean_dec(x_2697);
x_2706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2706, 0, x_2705);
lean_ctor_set(x_2706, 1, x_2704);
return x_2706;
}
}
}
else
{
uint8_t x_2707; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2707 = !lean_is_exclusive(x_2696);
if (x_2707 == 0)
{
return x_2696;
}
else
{
lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; 
x_2708 = lean_ctor_get(x_2696, 0);
x_2709 = lean_ctor_get(x_2696, 1);
lean_inc(x_2709);
lean_inc(x_2708);
lean_dec(x_2696);
x_2710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2710, 0, x_2708);
lean_ctor_set(x_2710, 1, x_2709);
return x_2710;
}
}
}
}
case 7:
{
uint8_t x_2711; 
lean_dec(x_2514);
lean_free_object(x_2510);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_2);
lean_dec(x_1);
x_2711 = !lean_is_exclusive(x_2519);
if (x_2711 == 0)
{
lean_object* x_2712; uint8_t x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; 
x_2712 = lean_ctor_get(x_2519, 0);
lean_dec(x_2712);
x_2713 = 1;
x_2714 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2715 = l_Lean_Name_toString(x_102, x_2713, x_2714);
lean_ctor_set_tag(x_2519, 3);
lean_ctor_set(x_2519, 0, x_2715);
x_2716 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_2717 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2717, 0, x_2716);
lean_ctor_set(x_2717, 1, x_2519);
x_2718 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_2719 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2719, 0, x_2717);
lean_ctor_set(x_2719, 1, x_2718);
x_2720 = l_Lean_MessageData_ofFormat(x_2719);
x_2721 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2720, x_3, x_4, x_5, x_2513);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2721;
}
else
{
uint8_t x_2722; lean_object* x_2723; lean_object* x_2724; lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; 
lean_dec(x_2519);
x_2722 = 1;
x_2723 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2724 = l_Lean_Name_toString(x_102, x_2722, x_2723);
x_2725 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2725, 0, x_2724);
x_2726 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_2727 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2727, 0, x_2726);
lean_ctor_set(x_2727, 1, x_2725);
x_2728 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_2729 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2729, 0, x_2727);
lean_ctor_set(x_2729, 1, x_2728);
x_2730 = l_Lean_MessageData_ofFormat(x_2729);
x_2731 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2730, x_3, x_4, x_5, x_2513);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2731;
}
}
default: 
{
lean_object* x_2732; 
lean_dec(x_2519);
lean_dec(x_2514);
lean_free_object(x_2510);
lean_free_object(x_7);
lean_dec(x_2499);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2505);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2732 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2505, x_3, x_4, x_5, x_2513);
if (lean_obj_tag(x_2732) == 0)
{
lean_object* x_2733; 
x_2733 = lean_ctor_get(x_2732, 0);
lean_inc(x_2733);
if (lean_obj_tag(x_2733) == 0)
{
lean_object* x_2734; lean_object* x_2735; lean_object* x_2736; 
x_2734 = lean_ctor_get(x_2732, 1);
lean_inc(x_2734);
lean_dec(x_2732);
x_2735 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2735, 0, x_102);
lean_ctor_set(x_2735, 1, x_2505);
x_2736 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2735, x_3, x_4, x_5, x_2734);
return x_2736;
}
else
{
uint8_t x_2737; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2737 = !lean_is_exclusive(x_2732);
if (x_2737 == 0)
{
lean_object* x_2738; lean_object* x_2739; 
x_2738 = lean_ctor_get(x_2732, 0);
lean_dec(x_2738);
x_2739 = lean_ctor_get(x_2733, 0);
lean_inc(x_2739);
lean_dec(x_2733);
lean_ctor_set(x_2732, 0, x_2739);
return x_2732;
}
else
{
lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; 
x_2740 = lean_ctor_get(x_2732, 1);
lean_inc(x_2740);
lean_dec(x_2732);
x_2741 = lean_ctor_get(x_2733, 0);
lean_inc(x_2741);
lean_dec(x_2733);
x_2742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2742, 0, x_2741);
lean_ctor_set(x_2742, 1, x_2740);
return x_2742;
}
}
}
else
{
uint8_t x_2743; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2743 = !lean_is_exclusive(x_2732);
if (x_2743 == 0)
{
return x_2732;
}
else
{
lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; 
x_2744 = lean_ctor_get(x_2732, 0);
x_2745 = lean_ctor_get(x_2732, 1);
lean_inc(x_2745);
lean_inc(x_2744);
lean_dec(x_2732);
x_2746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2746, 0, x_2744);
lean_ctor_set(x_2746, 1, x_2745);
return x_2746;
}
}
}
}
}
}
else
{
lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; uint8_t x_2750; lean_object* x_2751; 
x_2747 = lean_ctor_get(x_2510, 0);
x_2748 = lean_ctor_get(x_2510, 1);
lean_inc(x_2748);
lean_inc(x_2747);
lean_dec(x_2510);
x_2749 = lean_ctor_get(x_2747, 0);
lean_inc(x_2749);
lean_dec(x_2747);
x_2750 = 0;
lean_inc(x_102);
lean_inc(x_2749);
x_2751 = l_Lean_Environment_find_x3f(x_2749, x_102, x_2750);
if (lean_obj_tag(x_2751) == 0)
{
lean_object* x_2752; lean_object* x_2753; 
lean_dec(x_2749);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2752 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2753 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2752, x_3, x_4, x_5, x_2748);
return x_2753;
}
else
{
lean_object* x_2754; 
x_2754 = lean_ctor_get(x_2751, 0);
lean_inc(x_2754);
lean_dec(x_2751);
switch (lean_obj_tag(x_2754)) {
case 0:
{
lean_object* x_2755; lean_object* x_2756; uint8_t x_2757; 
lean_dec(x_2749);
lean_free_object(x_7);
lean_dec(x_2499);
if (lean_is_exclusive(x_2754)) {
 lean_ctor_release(x_2754, 0);
 x_2755 = x_2754;
} else {
 lean_dec_ref(x_2754);
 x_2755 = lean_box(0);
}
x_2756 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2757 = lean_name_eq(x_102, x_2756);
if (x_2757 == 0)
{
lean_object* x_2758; uint8_t x_2759; 
x_2758 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_2759 = lean_name_eq(x_102, x_2758);
if (x_2759 == 0)
{
lean_object* x_2760; lean_object* x_2761; 
lean_inc(x_102);
x_2760 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_2748);
x_2761 = lean_ctor_get(x_2760, 0);
lean_inc(x_2761);
if (lean_obj_tag(x_2761) == 0)
{
lean_object* x_2762; lean_object* x_2763; uint8_t x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; 
lean_dec(x_2505);
lean_dec(x_2);
lean_dec(x_1);
x_2762 = lean_ctor_get(x_2760, 1);
lean_inc(x_2762);
if (lean_is_exclusive(x_2760)) {
 lean_ctor_release(x_2760, 0);
 lean_ctor_release(x_2760, 1);
 x_2763 = x_2760;
} else {
 lean_dec_ref(x_2760);
 x_2763 = lean_box(0);
}
x_2764 = 1;
x_2765 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2766 = l_Lean_Name_toString(x_102, x_2764, x_2765);
if (lean_is_scalar(x_2755)) {
 x_2767 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2767 = x_2755;
 lean_ctor_set_tag(x_2767, 3);
}
lean_ctor_set(x_2767, 0, x_2766);
x_2768 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_2763)) {
 x_2769 = lean_alloc_ctor(5, 2, 0);
} else {
 x_2769 = x_2763;
 lean_ctor_set_tag(x_2769, 5);
}
lean_ctor_set(x_2769, 0, x_2768);
lean_ctor_set(x_2769, 1, x_2767);
x_2770 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2771 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2771, 0, x_2769);
lean_ctor_set(x_2771, 1, x_2770);
x_2772 = l_Lean_MessageData_ofFormat(x_2771);
x_2773 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2772, x_3, x_4, x_5, x_2762);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2773;
}
else
{
lean_object* x_2774; lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; uint8_t x_2780; 
lean_dec(x_2755);
x_2774 = lean_ctor_get(x_2760, 1);
lean_inc(x_2774);
if (lean_is_exclusive(x_2760)) {
 lean_ctor_release(x_2760, 0);
 lean_ctor_release(x_2760, 1);
 x_2775 = x_2760;
} else {
 lean_dec_ref(x_2760);
 x_2775 = lean_box(0);
}
x_2776 = lean_ctor_get(x_2761, 0);
lean_inc(x_2776);
lean_dec(x_2761);
x_2777 = lean_array_get_size(x_2505);
x_2778 = l_Lean_IR_Decl_params(x_2776);
lean_dec(x_2776);
x_2779 = lean_array_get_size(x_2778);
lean_dec(x_2778);
x_2780 = lean_nat_dec_lt(x_2777, x_2779);
if (x_2780 == 0)
{
uint8_t x_2781; 
x_2781 = lean_nat_dec_eq(x_2777, x_2779);
if (x_2781 == 0)
{
lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; lean_object* x_2785; lean_object* x_2786; 
x_2782 = lean_unsigned_to_nat(0u);
x_2783 = l_Array_extract___rarg(x_2505, x_2782, x_2779);
x_2784 = l_Array_extract___rarg(x_2505, x_2779, x_2777);
lean_dec(x_2777);
lean_dec(x_2505);
if (lean_is_scalar(x_2775)) {
 x_2785 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2785 = x_2775;
 lean_ctor_set_tag(x_2785, 6);
}
lean_ctor_set(x_2785, 0, x_102);
lean_ctor_set(x_2785, 1, x_2783);
x_2786 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_2785, x_2784, x_3, x_4, x_5, x_2774);
return x_2786;
}
else
{
lean_object* x_2787; lean_object* x_2788; 
lean_dec(x_2779);
lean_dec(x_2777);
if (lean_is_scalar(x_2775)) {
 x_2787 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2787 = x_2775;
 lean_ctor_set_tag(x_2787, 6);
}
lean_ctor_set(x_2787, 0, x_102);
lean_ctor_set(x_2787, 1, x_2505);
x_2788 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2787, x_3, x_4, x_5, x_2774);
return x_2788;
}
}
else
{
lean_object* x_2789; lean_object* x_2790; 
lean_dec(x_2779);
lean_dec(x_2777);
if (lean_is_scalar(x_2775)) {
 x_2789 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2789 = x_2775;
 lean_ctor_set_tag(x_2789, 7);
}
lean_ctor_set(x_2789, 0, x_102);
lean_ctor_set(x_2789, 1, x_2505);
x_2790 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2789, x_3, x_4, x_5, x_2774);
return x_2790;
}
}
}
else
{
lean_object* x_2791; lean_object* x_2792; 
lean_dec(x_2755);
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2791 = lean_box(13);
x_2792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2792, 0, x_2791);
lean_ctor_set(x_2792, 1, x_2748);
return x_2792;
}
}
else
{
lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; 
lean_dec(x_2755);
lean_dec(x_102);
x_2793 = l_Lean_IR_instInhabitedArg;
x_2794 = lean_unsigned_to_nat(2u);
x_2795 = lean_array_get(x_2793, x_2505, x_2794);
lean_dec(x_2505);
if (lean_obj_tag(x_2795) == 0)
{
lean_object* x_2796; lean_object* x_2797; 
x_2796 = lean_ctor_get(x_2795, 0);
lean_inc(x_2796);
lean_dec(x_2795);
x_2797 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2796, x_3, x_4, x_5, x_2748);
return x_2797;
}
else
{
lean_object* x_2798; lean_object* x_2799; 
x_2798 = lean_box(0);
x_2799 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2798, x_3, x_4, x_5, x_2748);
return x_2799;
}
}
}
case 2:
{
lean_object* x_2800; lean_object* x_2801; 
lean_dec(x_2754);
lean_dec(x_2749);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2800 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_2801 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2800, x_3, x_4, x_5, x_2748);
return x_2801;
}
case 4:
{
lean_object* x_2802; lean_object* x_2803; uint8_t x_2804; 
lean_dec(x_2749);
lean_free_object(x_7);
lean_dec(x_2499);
if (lean_is_exclusive(x_2754)) {
 lean_ctor_release(x_2754, 0);
 x_2802 = x_2754;
} else {
 lean_dec_ref(x_2754);
 x_2802 = lean_box(0);
}
x_2803 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_2804 = lean_name_eq(x_102, x_2803);
if (x_2804 == 0)
{
uint8_t x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; 
lean_dec(x_2505);
lean_dec(x_2);
lean_dec(x_1);
x_2805 = 1;
x_2806 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2807 = l_Lean_Name_toString(x_102, x_2805, x_2806);
if (lean_is_scalar(x_2802)) {
 x_2808 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2808 = x_2802;
 lean_ctor_set_tag(x_2808, 3);
}
lean_ctor_set(x_2808, 0, x_2807);
x_2809 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_2810 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2810, 0, x_2809);
lean_ctor_set(x_2810, 1, x_2808);
x_2811 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_2812 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2812, 0, x_2810);
lean_ctor_set(x_2812, 1, x_2811);
x_2813 = l_Lean_MessageData_ofFormat(x_2812);
x_2814 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2813, x_3, x_4, x_5, x_2748);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2814;
}
else
{
lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; 
lean_dec(x_2802);
lean_dec(x_102);
x_2815 = l_Lean_IR_instInhabitedArg;
x_2816 = lean_unsigned_to_nat(2u);
x_2817 = lean_array_get(x_2815, x_2505, x_2816);
lean_dec(x_2505);
if (lean_obj_tag(x_2817) == 0)
{
lean_object* x_2818; lean_object* x_2819; 
x_2818 = lean_ctor_get(x_2817, 0);
lean_inc(x_2818);
lean_dec(x_2817);
x_2819 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2818, x_3, x_4, x_5, x_2748);
return x_2819;
}
else
{
lean_object* x_2820; lean_object* x_2821; 
x_2820 = lean_box(0);
x_2821 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2820, x_3, x_4, x_5, x_2748);
return x_2821;
}
}
}
case 5:
{
lean_object* x_2822; lean_object* x_2823; 
lean_dec(x_2754);
lean_dec(x_2749);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2822 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_2823 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2822, x_3, x_4, x_5, x_2748);
return x_2823;
}
case 6:
{
lean_object* x_2824; uint8_t x_2825; 
x_2824 = lean_ctor_get(x_2754, 0);
lean_inc(x_2824);
lean_dec(x_2754);
lean_inc(x_102);
x_2825 = l_Lean_isExtern(x_2749, x_102);
if (x_2825 == 0)
{
lean_object* x_2826; 
lean_dec(x_2505);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2826 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_2748);
if (lean_obj_tag(x_2826) == 0)
{
lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; 
x_2827 = lean_ctor_get(x_2826, 0);
lean_inc(x_2827);
x_2828 = lean_ctor_get(x_2826, 1);
lean_inc(x_2828);
lean_dec(x_2826);
x_2829 = lean_ctor_get(x_2827, 0);
lean_inc(x_2829);
x_2830 = lean_ctor_get(x_2827, 1);
lean_inc(x_2830);
lean_dec(x_2827);
x_2831 = lean_ctor_get(x_2824, 3);
lean_inc(x_2831);
lean_dec(x_2824);
x_2832 = lean_array_get_size(x_2499);
x_2833 = l_Array_extract___rarg(x_2499, x_2831, x_2832);
lean_dec(x_2832);
lean_dec(x_2499);
x_2834 = lean_array_get_size(x_2830);
x_2835 = lean_unsigned_to_nat(0u);
x_2836 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_2836);
lean_ctor_set(x_7, 1, x_2834);
lean_ctor_set(x_7, 0, x_2835);
x_2837 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_2838 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6(x_2830, x_2833, x_7, x_7, x_2837, x_2835, lean_box(0), lean_box(0), x_3, x_4, x_5, x_2828);
lean_dec(x_7);
x_2839 = lean_ctor_get(x_2838, 0);
lean_inc(x_2839);
x_2840 = lean_ctor_get(x_2838, 1);
lean_inc(x_2840);
lean_dec(x_2838);
x_2841 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_2829, x_2830, x_2833, x_2839, x_3, x_4, x_5, x_2840);
lean_dec(x_2833);
lean_dec(x_2830);
return x_2841;
}
else
{
lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; lean_object* x_2845; 
lean_dec(x_2824);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2842 = lean_ctor_get(x_2826, 0);
lean_inc(x_2842);
x_2843 = lean_ctor_get(x_2826, 1);
lean_inc(x_2843);
if (lean_is_exclusive(x_2826)) {
 lean_ctor_release(x_2826, 0);
 lean_ctor_release(x_2826, 1);
 x_2844 = x_2826;
} else {
 lean_dec_ref(x_2826);
 x_2844 = lean_box(0);
}
if (lean_is_scalar(x_2844)) {
 x_2845 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2845 = x_2844;
}
lean_ctor_set(x_2845, 0, x_2842);
lean_ctor_set(x_2845, 1, x_2843);
return x_2845;
}
}
else
{
lean_object* x_2846; 
lean_dec(x_2824);
lean_free_object(x_7);
lean_dec(x_2499);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2505);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2846 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2505, x_3, x_4, x_5, x_2748);
if (lean_obj_tag(x_2846) == 0)
{
lean_object* x_2847; 
x_2847 = lean_ctor_get(x_2846, 0);
lean_inc(x_2847);
if (lean_obj_tag(x_2847) == 0)
{
lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; 
x_2848 = lean_ctor_get(x_2846, 1);
lean_inc(x_2848);
lean_dec(x_2846);
x_2849 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2849, 0, x_102);
lean_ctor_set(x_2849, 1, x_2505);
x_2850 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2849, x_3, x_4, x_5, x_2848);
return x_2850;
}
else
{
lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2851 = lean_ctor_get(x_2846, 1);
lean_inc(x_2851);
if (lean_is_exclusive(x_2846)) {
 lean_ctor_release(x_2846, 0);
 lean_ctor_release(x_2846, 1);
 x_2852 = x_2846;
} else {
 lean_dec_ref(x_2846);
 x_2852 = lean_box(0);
}
x_2853 = lean_ctor_get(x_2847, 0);
lean_inc(x_2853);
lean_dec(x_2847);
if (lean_is_scalar(x_2852)) {
 x_2854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2854 = x_2852;
}
lean_ctor_set(x_2854, 0, x_2853);
lean_ctor_set(x_2854, 1, x_2851);
return x_2854;
}
}
else
{
lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2855 = lean_ctor_get(x_2846, 0);
lean_inc(x_2855);
x_2856 = lean_ctor_get(x_2846, 1);
lean_inc(x_2856);
if (lean_is_exclusive(x_2846)) {
 lean_ctor_release(x_2846, 0);
 lean_ctor_release(x_2846, 1);
 x_2857 = x_2846;
} else {
 lean_dec_ref(x_2846);
 x_2857 = lean_box(0);
}
if (lean_is_scalar(x_2857)) {
 x_2858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2858 = x_2857;
}
lean_ctor_set(x_2858, 0, x_2855);
lean_ctor_set(x_2858, 1, x_2856);
return x_2858;
}
}
}
case 7:
{
lean_object* x_2859; uint8_t x_2860; lean_object* x_2861; lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; 
lean_dec(x_2749);
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_2754)) {
 lean_ctor_release(x_2754, 0);
 x_2859 = x_2754;
} else {
 lean_dec_ref(x_2754);
 x_2859 = lean_box(0);
}
x_2860 = 1;
x_2861 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2862 = l_Lean_Name_toString(x_102, x_2860, x_2861);
if (lean_is_scalar(x_2859)) {
 x_2863 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2863 = x_2859;
 lean_ctor_set_tag(x_2863, 3);
}
lean_ctor_set(x_2863, 0, x_2862);
x_2864 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_2865 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2865, 0, x_2864);
lean_ctor_set(x_2865, 1, x_2863);
x_2866 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_2867 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2867, 0, x_2865);
lean_ctor_set(x_2867, 1, x_2866);
x_2868 = l_Lean_MessageData_ofFormat(x_2867);
x_2869 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2868, x_3, x_4, x_5, x_2748);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2869;
}
default: 
{
lean_object* x_2870; 
lean_dec(x_2754);
lean_dec(x_2749);
lean_free_object(x_7);
lean_dec(x_2499);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2505);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2870 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2505, x_3, x_4, x_5, x_2748);
if (lean_obj_tag(x_2870) == 0)
{
lean_object* x_2871; 
x_2871 = lean_ctor_get(x_2870, 0);
lean_inc(x_2871);
if (lean_obj_tag(x_2871) == 0)
{
lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; 
x_2872 = lean_ctor_get(x_2870, 1);
lean_inc(x_2872);
lean_dec(x_2870);
x_2873 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_2873, 0, x_102);
lean_ctor_set(x_2873, 1, x_2505);
x_2874 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2873, x_3, x_4, x_5, x_2872);
return x_2874;
}
else
{
lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2875 = lean_ctor_get(x_2870, 1);
lean_inc(x_2875);
if (lean_is_exclusive(x_2870)) {
 lean_ctor_release(x_2870, 0);
 lean_ctor_release(x_2870, 1);
 x_2876 = x_2870;
} else {
 lean_dec_ref(x_2870);
 x_2876 = lean_box(0);
}
x_2877 = lean_ctor_get(x_2871, 0);
lean_inc(x_2877);
lean_dec(x_2871);
if (lean_is_scalar(x_2876)) {
 x_2878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2878 = x_2876;
}
lean_ctor_set(x_2878, 0, x_2877);
lean_ctor_set(x_2878, 1, x_2875);
return x_2878;
}
}
else
{
lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; 
lean_dec(x_2505);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2879 = lean_ctor_get(x_2870, 0);
lean_inc(x_2879);
x_2880 = lean_ctor_get(x_2870, 1);
lean_inc(x_2880);
if (lean_is_exclusive(x_2870)) {
 lean_ctor_release(x_2870, 0);
 lean_ctor_release(x_2870, 1);
 x_2881 = x_2870;
} else {
 lean_dec_ref(x_2870);
 x_2881 = lean_box(0);
}
if (lean_is_scalar(x_2881)) {
 x_2882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2882 = x_2881;
}
lean_ctor_set(x_2882, 0, x_2879);
lean_ctor_set(x_2882, 1, x_2880);
return x_2882;
}
}
}
}
}
}
else
{
uint8_t x_2883; 
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2883 = !lean_is_exclusive(x_2507);
if (x_2883 == 0)
{
lean_object* x_2884; lean_object* x_2885; 
x_2884 = lean_ctor_get(x_2507, 0);
lean_dec(x_2884);
x_2885 = lean_ctor_get(x_2508, 0);
lean_inc(x_2885);
lean_dec(x_2508);
lean_ctor_set(x_2507, 0, x_2885);
return x_2507;
}
else
{
lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; 
x_2886 = lean_ctor_get(x_2507, 1);
lean_inc(x_2886);
lean_dec(x_2507);
x_2887 = lean_ctor_get(x_2508, 0);
lean_inc(x_2887);
lean_dec(x_2508);
x_2888 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2888, 0, x_2887);
lean_ctor_set(x_2888, 1, x_2886);
return x_2888;
}
}
}
else
{
uint8_t x_2889; 
lean_dec(x_2505);
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2889 = !lean_is_exclusive(x_2507);
if (x_2889 == 0)
{
return x_2507;
}
else
{
lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; 
x_2890 = lean_ctor_get(x_2507, 0);
x_2891 = lean_ctor_get(x_2507, 1);
lean_inc(x_2891);
lean_inc(x_2890);
lean_dec(x_2507);
x_2892 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2892, 0, x_2890);
lean_ctor_set(x_2892, 1, x_2891);
return x_2892;
}
}
}
else
{
uint8_t x_2893; 
lean_free_object(x_7);
lean_dec(x_2499);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2893 = !lean_is_exclusive(x_2504);
if (x_2893 == 0)
{
return x_2504;
}
else
{
lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; 
x_2894 = lean_ctor_get(x_2504, 0);
x_2895 = lean_ctor_get(x_2504, 1);
lean_inc(x_2895);
lean_inc(x_2894);
lean_dec(x_2504);
x_2896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2896, 0, x_2894);
lean_ctor_set(x_2896, 1, x_2895);
return x_2896;
}
}
}
else
{
lean_object* x_2897; size_t x_2898; size_t x_2899; lean_object* x_2900; 
x_2897 = lean_ctor_get(x_7, 2);
lean_inc(x_2897);
lean_dec(x_7);
x_2898 = lean_array_size(x_2897);
x_2899 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2897);
x_2900 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_2898, x_2899, x_2897, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_2900) == 0)
{
lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; 
x_2901 = lean_ctor_get(x_2900, 0);
lean_inc(x_2901);
x_2902 = lean_ctor_get(x_2900, 1);
lean_inc(x_2902);
lean_dec(x_2900);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2901);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_2903 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2901, x_3, x_4, x_5, x_2902);
if (lean_obj_tag(x_2903) == 0)
{
lean_object* x_2904; 
x_2904 = lean_ctor_get(x_2903, 0);
lean_inc(x_2904);
if (lean_obj_tag(x_2904) == 0)
{
lean_object* x_2905; lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; lean_object* x_2910; uint8_t x_2911; lean_object* x_2912; 
x_2905 = lean_ctor_get(x_2903, 1);
lean_inc(x_2905);
lean_dec(x_2903);
x_2906 = lean_st_ref_get(x_5, x_2905);
x_2907 = lean_ctor_get(x_2906, 0);
lean_inc(x_2907);
x_2908 = lean_ctor_get(x_2906, 1);
lean_inc(x_2908);
if (lean_is_exclusive(x_2906)) {
 lean_ctor_release(x_2906, 0);
 lean_ctor_release(x_2906, 1);
 x_2909 = x_2906;
} else {
 lean_dec_ref(x_2906);
 x_2909 = lean_box(0);
}
x_2910 = lean_ctor_get(x_2907, 0);
lean_inc(x_2910);
lean_dec(x_2907);
x_2911 = 0;
lean_inc(x_102);
lean_inc(x_2910);
x_2912 = l_Lean_Environment_find_x3f(x_2910, x_102, x_2911);
if (lean_obj_tag(x_2912) == 0)
{
lean_object* x_2913; lean_object* x_2914; 
lean_dec(x_2910);
lean_dec(x_2909);
lean_dec(x_2901);
lean_dec(x_2897);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2913 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2914 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2913, x_3, x_4, x_5, x_2908);
return x_2914;
}
else
{
lean_object* x_2915; 
x_2915 = lean_ctor_get(x_2912, 0);
lean_inc(x_2915);
lean_dec(x_2912);
switch (lean_obj_tag(x_2915)) {
case 0:
{
lean_object* x_2916; lean_object* x_2917; uint8_t x_2918; 
lean_dec(x_2910);
lean_dec(x_2897);
if (lean_is_exclusive(x_2915)) {
 lean_ctor_release(x_2915, 0);
 x_2916 = x_2915;
} else {
 lean_dec_ref(x_2915);
 x_2916 = lean_box(0);
}
x_2917 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_2918 = lean_name_eq(x_102, x_2917);
if (x_2918 == 0)
{
lean_object* x_2919; uint8_t x_2920; 
x_2919 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_2920 = lean_name_eq(x_102, x_2919);
if (x_2920 == 0)
{
lean_object* x_2921; lean_object* x_2922; 
lean_dec(x_2909);
lean_inc(x_102);
x_2921 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_2908);
x_2922 = lean_ctor_get(x_2921, 0);
lean_inc(x_2922);
if (lean_obj_tag(x_2922) == 0)
{
lean_object* x_2923; lean_object* x_2924; uint8_t x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; 
lean_dec(x_2901);
lean_dec(x_2);
lean_dec(x_1);
x_2923 = lean_ctor_get(x_2921, 1);
lean_inc(x_2923);
if (lean_is_exclusive(x_2921)) {
 lean_ctor_release(x_2921, 0);
 lean_ctor_release(x_2921, 1);
 x_2924 = x_2921;
} else {
 lean_dec_ref(x_2921);
 x_2924 = lean_box(0);
}
x_2925 = 1;
x_2926 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2927 = l_Lean_Name_toString(x_102, x_2925, x_2926);
if (lean_is_scalar(x_2916)) {
 x_2928 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2928 = x_2916;
 lean_ctor_set_tag(x_2928, 3);
}
lean_ctor_set(x_2928, 0, x_2927);
x_2929 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_2924)) {
 x_2930 = lean_alloc_ctor(5, 2, 0);
} else {
 x_2930 = x_2924;
 lean_ctor_set_tag(x_2930, 5);
}
lean_ctor_set(x_2930, 0, x_2929);
lean_ctor_set(x_2930, 1, x_2928);
x_2931 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_2932 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2932, 0, x_2930);
lean_ctor_set(x_2932, 1, x_2931);
x_2933 = l_Lean_MessageData_ofFormat(x_2932);
x_2934 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2933, x_3, x_4, x_5, x_2923);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2934;
}
else
{
lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; uint8_t x_2941; 
lean_dec(x_2916);
x_2935 = lean_ctor_get(x_2921, 1);
lean_inc(x_2935);
if (lean_is_exclusive(x_2921)) {
 lean_ctor_release(x_2921, 0);
 lean_ctor_release(x_2921, 1);
 x_2936 = x_2921;
} else {
 lean_dec_ref(x_2921);
 x_2936 = lean_box(0);
}
x_2937 = lean_ctor_get(x_2922, 0);
lean_inc(x_2937);
lean_dec(x_2922);
x_2938 = lean_array_get_size(x_2901);
x_2939 = l_Lean_IR_Decl_params(x_2937);
lean_dec(x_2937);
x_2940 = lean_array_get_size(x_2939);
lean_dec(x_2939);
x_2941 = lean_nat_dec_lt(x_2938, x_2940);
if (x_2941 == 0)
{
uint8_t x_2942; 
x_2942 = lean_nat_dec_eq(x_2938, x_2940);
if (x_2942 == 0)
{
lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; 
x_2943 = lean_unsigned_to_nat(0u);
x_2944 = l_Array_extract___rarg(x_2901, x_2943, x_2940);
x_2945 = l_Array_extract___rarg(x_2901, x_2940, x_2938);
lean_dec(x_2938);
lean_dec(x_2901);
if (lean_is_scalar(x_2936)) {
 x_2946 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2946 = x_2936;
 lean_ctor_set_tag(x_2946, 6);
}
lean_ctor_set(x_2946, 0, x_102);
lean_ctor_set(x_2946, 1, x_2944);
x_2947 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_2946, x_2945, x_3, x_4, x_5, x_2935);
return x_2947;
}
else
{
lean_object* x_2948; lean_object* x_2949; 
lean_dec(x_2940);
lean_dec(x_2938);
if (lean_is_scalar(x_2936)) {
 x_2948 = lean_alloc_ctor(6, 2, 0);
} else {
 x_2948 = x_2936;
 lean_ctor_set_tag(x_2948, 6);
}
lean_ctor_set(x_2948, 0, x_102);
lean_ctor_set(x_2948, 1, x_2901);
x_2949 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2948, x_3, x_4, x_5, x_2935);
return x_2949;
}
}
else
{
lean_object* x_2950; lean_object* x_2951; 
lean_dec(x_2940);
lean_dec(x_2938);
if (lean_is_scalar(x_2936)) {
 x_2950 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2950 = x_2936;
 lean_ctor_set_tag(x_2950, 7);
}
lean_ctor_set(x_2950, 0, x_102);
lean_ctor_set(x_2950, 1, x_2901);
x_2951 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_2950, x_3, x_4, x_5, x_2935);
return x_2951;
}
}
}
else
{
lean_object* x_2952; lean_object* x_2953; 
lean_dec(x_2916);
lean_dec(x_2901);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2952 = lean_box(13);
if (lean_is_scalar(x_2909)) {
 x_2953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2953 = x_2909;
}
lean_ctor_set(x_2953, 0, x_2952);
lean_ctor_set(x_2953, 1, x_2908);
return x_2953;
}
}
else
{
lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; 
lean_dec(x_2916);
lean_dec(x_2909);
lean_dec(x_102);
x_2954 = l_Lean_IR_instInhabitedArg;
x_2955 = lean_unsigned_to_nat(2u);
x_2956 = lean_array_get(x_2954, x_2901, x_2955);
lean_dec(x_2901);
if (lean_obj_tag(x_2956) == 0)
{
lean_object* x_2957; lean_object* x_2958; 
x_2957 = lean_ctor_get(x_2956, 0);
lean_inc(x_2957);
lean_dec(x_2956);
x_2958 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2957, x_3, x_4, x_5, x_2908);
return x_2958;
}
else
{
lean_object* x_2959; lean_object* x_2960; 
x_2959 = lean_box(0);
x_2960 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2959, x_3, x_4, x_5, x_2908);
return x_2960;
}
}
}
case 2:
{
lean_object* x_2961; lean_object* x_2962; 
lean_dec(x_2915);
lean_dec(x_2910);
lean_dec(x_2909);
lean_dec(x_2901);
lean_dec(x_2897);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2961 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_2962 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2961, x_3, x_4, x_5, x_2908);
return x_2962;
}
case 4:
{
lean_object* x_2963; lean_object* x_2964; uint8_t x_2965; 
lean_dec(x_2910);
lean_dec(x_2909);
lean_dec(x_2897);
if (lean_is_exclusive(x_2915)) {
 lean_ctor_release(x_2915, 0);
 x_2963 = x_2915;
} else {
 lean_dec_ref(x_2915);
 x_2963 = lean_box(0);
}
x_2964 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_2965 = lean_name_eq(x_102, x_2964);
if (x_2965 == 0)
{
uint8_t x_2966; lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; 
lean_dec(x_2901);
lean_dec(x_2);
lean_dec(x_1);
x_2966 = 1;
x_2967 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_2968 = l_Lean_Name_toString(x_102, x_2966, x_2967);
if (lean_is_scalar(x_2963)) {
 x_2969 = lean_alloc_ctor(3, 1, 0);
} else {
 x_2969 = x_2963;
 lean_ctor_set_tag(x_2969, 3);
}
lean_ctor_set(x_2969, 0, x_2968);
x_2970 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_2971 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2971, 0, x_2970);
lean_ctor_set(x_2971, 1, x_2969);
x_2972 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_2973 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_2973, 0, x_2971);
lean_ctor_set(x_2973, 1, x_2972);
x_2974 = l_Lean_MessageData_ofFormat(x_2973);
x_2975 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_2974, x_3, x_4, x_5, x_2908);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2975;
}
else
{
lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; 
lean_dec(x_2963);
lean_dec(x_102);
x_2976 = l_Lean_IR_instInhabitedArg;
x_2977 = lean_unsigned_to_nat(2u);
x_2978 = lean_array_get(x_2976, x_2901, x_2977);
lean_dec(x_2901);
if (lean_obj_tag(x_2978) == 0)
{
lean_object* x_2979; lean_object* x_2980; 
x_2979 = lean_ctor_get(x_2978, 0);
lean_inc(x_2979);
lean_dec(x_2978);
x_2980 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_2979, x_3, x_4, x_5, x_2908);
return x_2980;
}
else
{
lean_object* x_2981; lean_object* x_2982; 
x_2981 = lean_box(0);
x_2982 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_2981, x_3, x_4, x_5, x_2908);
return x_2982;
}
}
}
case 5:
{
lean_object* x_2983; lean_object* x_2984; 
lean_dec(x_2915);
lean_dec(x_2910);
lean_dec(x_2909);
lean_dec(x_2901);
lean_dec(x_2897);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_2983 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_2984 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_2983, x_3, x_4, x_5, x_2908);
return x_2984;
}
case 6:
{
lean_object* x_2985; uint8_t x_2986; 
lean_dec(x_2909);
x_2985 = lean_ctor_get(x_2915, 0);
lean_inc(x_2985);
lean_dec(x_2915);
lean_inc(x_102);
x_2986 = l_Lean_isExtern(x_2910, x_102);
if (x_2986 == 0)
{
lean_object* x_2987; 
lean_dec(x_2901);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2987 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_2908);
if (lean_obj_tag(x_2987) == 0)
{
lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; 
x_2988 = lean_ctor_get(x_2987, 0);
lean_inc(x_2988);
x_2989 = lean_ctor_get(x_2987, 1);
lean_inc(x_2989);
lean_dec(x_2987);
x_2990 = lean_ctor_get(x_2988, 0);
lean_inc(x_2990);
x_2991 = lean_ctor_get(x_2988, 1);
lean_inc(x_2991);
lean_dec(x_2988);
x_2992 = lean_ctor_get(x_2985, 3);
lean_inc(x_2992);
lean_dec(x_2985);
x_2993 = lean_array_get_size(x_2897);
x_2994 = l_Array_extract___rarg(x_2897, x_2992, x_2993);
lean_dec(x_2993);
lean_dec(x_2897);
x_2995 = lean_array_get_size(x_2991);
x_2996 = lean_unsigned_to_nat(0u);
x_2997 = lean_unsigned_to_nat(1u);
x_2998 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2998, 0, x_2996);
lean_ctor_set(x_2998, 1, x_2995);
lean_ctor_set(x_2998, 2, x_2997);
x_2999 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_3000 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6(x_2991, x_2994, x_2998, x_2998, x_2999, x_2996, lean_box(0), lean_box(0), x_3, x_4, x_5, x_2989);
lean_dec(x_2998);
x_3001 = lean_ctor_get(x_3000, 0);
lean_inc(x_3001);
x_3002 = lean_ctor_get(x_3000, 1);
lean_inc(x_3002);
lean_dec(x_3000);
x_3003 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_2990, x_2991, x_2994, x_3001, x_3, x_4, x_5, x_3002);
lean_dec(x_2994);
lean_dec(x_2991);
return x_3003;
}
else
{
lean_object* x_3004; lean_object* x_3005; lean_object* x_3006; lean_object* x_3007; 
lean_dec(x_2985);
lean_dec(x_2897);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3004 = lean_ctor_get(x_2987, 0);
lean_inc(x_3004);
x_3005 = lean_ctor_get(x_2987, 1);
lean_inc(x_3005);
if (lean_is_exclusive(x_2987)) {
 lean_ctor_release(x_2987, 0);
 lean_ctor_release(x_2987, 1);
 x_3006 = x_2987;
} else {
 lean_dec_ref(x_2987);
 x_3006 = lean_box(0);
}
if (lean_is_scalar(x_3006)) {
 x_3007 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3007 = x_3006;
}
lean_ctor_set(x_3007, 0, x_3004);
lean_ctor_set(x_3007, 1, x_3005);
return x_3007;
}
}
else
{
lean_object* x_3008; 
lean_dec(x_2985);
lean_dec(x_2897);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2901);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3008 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2901, x_3, x_4, x_5, x_2908);
if (lean_obj_tag(x_3008) == 0)
{
lean_object* x_3009; 
x_3009 = lean_ctor_get(x_3008, 0);
lean_inc(x_3009);
if (lean_obj_tag(x_3009) == 0)
{
lean_object* x_3010; lean_object* x_3011; lean_object* x_3012; 
x_3010 = lean_ctor_get(x_3008, 1);
lean_inc(x_3010);
lean_dec(x_3008);
x_3011 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3011, 0, x_102);
lean_ctor_set(x_3011, 1, x_2901);
x_3012 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3011, x_3, x_4, x_5, x_3010);
return x_3012;
}
else
{
lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; 
lean_dec(x_2901);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3013 = lean_ctor_get(x_3008, 1);
lean_inc(x_3013);
if (lean_is_exclusive(x_3008)) {
 lean_ctor_release(x_3008, 0);
 lean_ctor_release(x_3008, 1);
 x_3014 = x_3008;
} else {
 lean_dec_ref(x_3008);
 x_3014 = lean_box(0);
}
x_3015 = lean_ctor_get(x_3009, 0);
lean_inc(x_3015);
lean_dec(x_3009);
if (lean_is_scalar(x_3014)) {
 x_3016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3016 = x_3014;
}
lean_ctor_set(x_3016, 0, x_3015);
lean_ctor_set(x_3016, 1, x_3013);
return x_3016;
}
}
else
{
lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; lean_object* x_3020; 
lean_dec(x_2901);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3017 = lean_ctor_get(x_3008, 0);
lean_inc(x_3017);
x_3018 = lean_ctor_get(x_3008, 1);
lean_inc(x_3018);
if (lean_is_exclusive(x_3008)) {
 lean_ctor_release(x_3008, 0);
 lean_ctor_release(x_3008, 1);
 x_3019 = x_3008;
} else {
 lean_dec_ref(x_3008);
 x_3019 = lean_box(0);
}
if (lean_is_scalar(x_3019)) {
 x_3020 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3020 = x_3019;
}
lean_ctor_set(x_3020, 0, x_3017);
lean_ctor_set(x_3020, 1, x_3018);
return x_3020;
}
}
}
case 7:
{
lean_object* x_3021; uint8_t x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; 
lean_dec(x_2910);
lean_dec(x_2909);
lean_dec(x_2901);
lean_dec(x_2897);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_2915)) {
 lean_ctor_release(x_2915, 0);
 x_3021 = x_2915;
} else {
 lean_dec_ref(x_2915);
 x_3021 = lean_box(0);
}
x_3022 = 1;
x_3023 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3024 = l_Lean_Name_toString(x_102, x_3022, x_3023);
if (lean_is_scalar(x_3021)) {
 x_3025 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3025 = x_3021;
 lean_ctor_set_tag(x_3025, 3);
}
lean_ctor_set(x_3025, 0, x_3024);
x_3026 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3027 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3027, 0, x_3026);
lean_ctor_set(x_3027, 1, x_3025);
x_3028 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3029 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3029, 0, x_3027);
lean_ctor_set(x_3029, 1, x_3028);
x_3030 = l_Lean_MessageData_ofFormat(x_3029);
x_3031 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3030, x_3, x_4, x_5, x_2908);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3031;
}
default: 
{
lean_object* x_3032; 
lean_dec(x_2915);
lean_dec(x_2910);
lean_dec(x_2909);
lean_dec(x_2897);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2901);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3032 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_2901, x_3, x_4, x_5, x_2908);
if (lean_obj_tag(x_3032) == 0)
{
lean_object* x_3033; 
x_3033 = lean_ctor_get(x_3032, 0);
lean_inc(x_3033);
if (lean_obj_tag(x_3033) == 0)
{
lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; 
x_3034 = lean_ctor_get(x_3032, 1);
lean_inc(x_3034);
lean_dec(x_3032);
x_3035 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3035, 0, x_102);
lean_ctor_set(x_3035, 1, x_2901);
x_3036 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3035, x_3, x_4, x_5, x_3034);
return x_3036;
}
else
{
lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; 
lean_dec(x_2901);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3037 = lean_ctor_get(x_3032, 1);
lean_inc(x_3037);
if (lean_is_exclusive(x_3032)) {
 lean_ctor_release(x_3032, 0);
 lean_ctor_release(x_3032, 1);
 x_3038 = x_3032;
} else {
 lean_dec_ref(x_3032);
 x_3038 = lean_box(0);
}
x_3039 = lean_ctor_get(x_3033, 0);
lean_inc(x_3039);
lean_dec(x_3033);
if (lean_is_scalar(x_3038)) {
 x_3040 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3040 = x_3038;
}
lean_ctor_set(x_3040, 0, x_3039);
lean_ctor_set(x_3040, 1, x_3037);
return x_3040;
}
}
else
{
lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; 
lean_dec(x_2901);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3041 = lean_ctor_get(x_3032, 0);
lean_inc(x_3041);
x_3042 = lean_ctor_get(x_3032, 1);
lean_inc(x_3042);
if (lean_is_exclusive(x_3032)) {
 lean_ctor_release(x_3032, 0);
 lean_ctor_release(x_3032, 1);
 x_3043 = x_3032;
} else {
 lean_dec_ref(x_3032);
 x_3043 = lean_box(0);
}
if (lean_is_scalar(x_3043)) {
 x_3044 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3044 = x_3043;
}
lean_ctor_set(x_3044, 0, x_3041);
lean_ctor_set(x_3044, 1, x_3042);
return x_3044;
}
}
}
}
}
else
{
lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; 
lean_dec(x_2901);
lean_dec(x_2897);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3045 = lean_ctor_get(x_2903, 1);
lean_inc(x_3045);
if (lean_is_exclusive(x_2903)) {
 lean_ctor_release(x_2903, 0);
 lean_ctor_release(x_2903, 1);
 x_3046 = x_2903;
} else {
 lean_dec_ref(x_2903);
 x_3046 = lean_box(0);
}
x_3047 = lean_ctor_get(x_2904, 0);
lean_inc(x_3047);
lean_dec(x_2904);
if (lean_is_scalar(x_3046)) {
 x_3048 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3048 = x_3046;
}
lean_ctor_set(x_3048, 0, x_3047);
lean_ctor_set(x_3048, 1, x_3045);
return x_3048;
}
}
else
{
lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; 
lean_dec(x_2901);
lean_dec(x_2897);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3049 = lean_ctor_get(x_2903, 0);
lean_inc(x_3049);
x_3050 = lean_ctor_get(x_2903, 1);
lean_inc(x_3050);
if (lean_is_exclusive(x_2903)) {
 lean_ctor_release(x_2903, 0);
 lean_ctor_release(x_2903, 1);
 x_3051 = x_2903;
} else {
 lean_dec_ref(x_2903);
 x_3051 = lean_box(0);
}
if (lean_is_scalar(x_3051)) {
 x_3052 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3052 = x_3051;
}
lean_ctor_set(x_3052, 0, x_3049);
lean_ctor_set(x_3052, 1, x_3050);
return x_3052;
}
}
else
{
lean_object* x_3053; lean_object* x_3054; lean_object* x_3055; lean_object* x_3056; 
lean_dec(x_2897);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3053 = lean_ctor_get(x_2900, 0);
lean_inc(x_3053);
x_3054 = lean_ctor_get(x_2900, 1);
lean_inc(x_3054);
if (lean_is_exclusive(x_2900)) {
 lean_ctor_release(x_2900, 0);
 lean_ctor_release(x_2900, 1);
 x_3055 = x_2900;
} else {
 lean_dec_ref(x_2900);
 x_3055 = lean_box(0);
}
if (lean_is_scalar(x_3055)) {
 x_3056 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3056 = x_3055;
}
lean_ctor_set(x_3056, 0, x_3053);
lean_ctor_set(x_3056, 1, x_3054);
return x_3056;
}
}
}
default: 
{
uint8_t x_3057; 
lean_dec(x_1222);
lean_dec(x_662);
x_3057 = !lean_is_exclusive(x_7);
if (x_3057 == 0)
{
lean_object* x_3058; lean_object* x_3059; lean_object* x_3060; size_t x_3061; size_t x_3062; lean_object* x_3063; 
x_3058 = lean_ctor_get(x_7, 2);
x_3059 = lean_ctor_get(x_7, 1);
lean_dec(x_3059);
x_3060 = lean_ctor_get(x_7, 0);
lean_dec(x_3060);
x_3061 = lean_array_size(x_3058);
x_3062 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3058);
x_3063 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_3061, x_3062, x_3058, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_3063) == 0)
{
lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; 
x_3064 = lean_ctor_get(x_3063, 0);
lean_inc(x_3064);
x_3065 = lean_ctor_get(x_3063, 1);
lean_inc(x_3065);
lean_dec(x_3063);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3064);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3066 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3064, x_3, x_4, x_5, x_3065);
if (lean_obj_tag(x_3066) == 0)
{
lean_object* x_3067; 
x_3067 = lean_ctor_get(x_3066, 0);
lean_inc(x_3067);
if (lean_obj_tag(x_3067) == 0)
{
lean_object* x_3068; lean_object* x_3069; uint8_t x_3070; 
x_3068 = lean_ctor_get(x_3066, 1);
lean_inc(x_3068);
lean_dec(x_3066);
x_3069 = lean_st_ref_get(x_5, x_3068);
x_3070 = !lean_is_exclusive(x_3069);
if (x_3070 == 0)
{
lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; uint8_t x_3074; lean_object* x_3075; 
x_3071 = lean_ctor_get(x_3069, 0);
x_3072 = lean_ctor_get(x_3069, 1);
x_3073 = lean_ctor_get(x_3071, 0);
lean_inc(x_3073);
lean_dec(x_3071);
x_3074 = 0;
lean_inc(x_102);
lean_inc(x_3073);
x_3075 = l_Lean_Environment_find_x3f(x_3073, x_102, x_3074);
if (lean_obj_tag(x_3075) == 0)
{
lean_object* x_3076; lean_object* x_3077; 
lean_dec(x_3073);
lean_free_object(x_3069);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3076 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_3077 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3076, x_3, x_4, x_5, x_3072);
return x_3077;
}
else
{
lean_object* x_3078; 
x_3078 = lean_ctor_get(x_3075, 0);
lean_inc(x_3078);
lean_dec(x_3075);
switch (lean_obj_tag(x_3078)) {
case 0:
{
uint8_t x_3079; 
lean_dec(x_3073);
lean_free_object(x_7);
lean_dec(x_3058);
x_3079 = !lean_is_exclusive(x_3078);
if (x_3079 == 0)
{
lean_object* x_3080; lean_object* x_3081; uint8_t x_3082; 
x_3080 = lean_ctor_get(x_3078, 0);
lean_dec(x_3080);
x_3081 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_3082 = lean_name_eq(x_102, x_3081);
if (x_3082 == 0)
{
lean_object* x_3083; uint8_t x_3084; 
x_3083 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_3084 = lean_name_eq(x_102, x_3083);
if (x_3084 == 0)
{
lean_object* x_3085; lean_object* x_3086; 
lean_free_object(x_3069);
lean_inc(x_102);
x_3085 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_3072);
x_3086 = lean_ctor_get(x_3085, 0);
lean_inc(x_3086);
if (lean_obj_tag(x_3086) == 0)
{
uint8_t x_3087; 
lean_dec(x_3064);
lean_dec(x_2);
lean_dec(x_1);
x_3087 = !lean_is_exclusive(x_3085);
if (x_3087 == 0)
{
lean_object* x_3088; lean_object* x_3089; uint8_t x_3090; lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; lean_object* x_3096; lean_object* x_3097; 
x_3088 = lean_ctor_get(x_3085, 1);
x_3089 = lean_ctor_get(x_3085, 0);
lean_dec(x_3089);
x_3090 = 1;
x_3091 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3092 = l_Lean_Name_toString(x_102, x_3090, x_3091);
lean_ctor_set_tag(x_3078, 3);
lean_ctor_set(x_3078, 0, x_3092);
x_3093 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_3085, 5);
lean_ctor_set(x_3085, 1, x_3078);
lean_ctor_set(x_3085, 0, x_3093);
x_3094 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3095 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3095, 0, x_3085);
lean_ctor_set(x_3095, 1, x_3094);
x_3096 = l_Lean_MessageData_ofFormat(x_3095);
x_3097 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3096, x_3, x_4, x_5, x_3088);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3097;
}
else
{
lean_object* x_3098; uint8_t x_3099; lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; lean_object* x_3107; 
x_3098 = lean_ctor_get(x_3085, 1);
lean_inc(x_3098);
lean_dec(x_3085);
x_3099 = 1;
x_3100 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3101 = l_Lean_Name_toString(x_102, x_3099, x_3100);
lean_ctor_set_tag(x_3078, 3);
lean_ctor_set(x_3078, 0, x_3101);
x_3102 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_3103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3103, 0, x_3102);
lean_ctor_set(x_3103, 1, x_3078);
x_3104 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3105, 0, x_3103);
lean_ctor_set(x_3105, 1, x_3104);
x_3106 = l_Lean_MessageData_ofFormat(x_3105);
x_3107 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3106, x_3, x_4, x_5, x_3098);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3107;
}
}
else
{
uint8_t x_3108; 
lean_free_object(x_3078);
x_3108 = !lean_is_exclusive(x_3085);
if (x_3108 == 0)
{
lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; uint8_t x_3115; 
x_3109 = lean_ctor_get(x_3085, 1);
x_3110 = lean_ctor_get(x_3085, 0);
lean_dec(x_3110);
x_3111 = lean_ctor_get(x_3086, 0);
lean_inc(x_3111);
lean_dec(x_3086);
x_3112 = lean_array_get_size(x_3064);
x_3113 = l_Lean_IR_Decl_params(x_3111);
lean_dec(x_3111);
x_3114 = lean_array_get_size(x_3113);
lean_dec(x_3113);
x_3115 = lean_nat_dec_lt(x_3112, x_3114);
if (x_3115 == 0)
{
uint8_t x_3116; 
x_3116 = lean_nat_dec_eq(x_3112, x_3114);
if (x_3116 == 0)
{
lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; 
x_3117 = lean_unsigned_to_nat(0u);
x_3118 = l_Array_extract___rarg(x_3064, x_3117, x_3114);
x_3119 = l_Array_extract___rarg(x_3064, x_3114, x_3112);
lean_dec(x_3112);
lean_dec(x_3064);
lean_ctor_set_tag(x_3085, 6);
lean_ctor_set(x_3085, 1, x_3118);
lean_ctor_set(x_3085, 0, x_102);
x_3120 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3085, x_3119, x_3, x_4, x_5, x_3109);
return x_3120;
}
else
{
lean_object* x_3121; 
lean_dec(x_3114);
lean_dec(x_3112);
lean_ctor_set_tag(x_3085, 6);
lean_ctor_set(x_3085, 1, x_3064);
lean_ctor_set(x_3085, 0, x_102);
x_3121 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3085, x_3, x_4, x_5, x_3109);
return x_3121;
}
}
else
{
lean_object* x_3122; 
lean_dec(x_3114);
lean_dec(x_3112);
lean_ctor_set_tag(x_3085, 7);
lean_ctor_set(x_3085, 1, x_3064);
lean_ctor_set(x_3085, 0, x_102);
x_3122 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3085, x_3, x_4, x_5, x_3109);
return x_3122;
}
}
else
{
lean_object* x_3123; lean_object* x_3124; lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; uint8_t x_3128; 
x_3123 = lean_ctor_get(x_3085, 1);
lean_inc(x_3123);
lean_dec(x_3085);
x_3124 = lean_ctor_get(x_3086, 0);
lean_inc(x_3124);
lean_dec(x_3086);
x_3125 = lean_array_get_size(x_3064);
x_3126 = l_Lean_IR_Decl_params(x_3124);
lean_dec(x_3124);
x_3127 = lean_array_get_size(x_3126);
lean_dec(x_3126);
x_3128 = lean_nat_dec_lt(x_3125, x_3127);
if (x_3128 == 0)
{
uint8_t x_3129; 
x_3129 = lean_nat_dec_eq(x_3125, x_3127);
if (x_3129 == 0)
{
lean_object* x_3130; lean_object* x_3131; lean_object* x_3132; lean_object* x_3133; lean_object* x_3134; 
x_3130 = lean_unsigned_to_nat(0u);
x_3131 = l_Array_extract___rarg(x_3064, x_3130, x_3127);
x_3132 = l_Array_extract___rarg(x_3064, x_3127, x_3125);
lean_dec(x_3125);
lean_dec(x_3064);
x_3133 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3133, 0, x_102);
lean_ctor_set(x_3133, 1, x_3131);
x_3134 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3133, x_3132, x_3, x_4, x_5, x_3123);
return x_3134;
}
else
{
lean_object* x_3135; lean_object* x_3136; 
lean_dec(x_3127);
lean_dec(x_3125);
x_3135 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3135, 0, x_102);
lean_ctor_set(x_3135, 1, x_3064);
x_3136 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3135, x_3, x_4, x_5, x_3123);
return x_3136;
}
}
else
{
lean_object* x_3137; lean_object* x_3138; 
lean_dec(x_3127);
lean_dec(x_3125);
x_3137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3137, 0, x_102);
lean_ctor_set(x_3137, 1, x_3064);
x_3138 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3137, x_3, x_4, x_5, x_3123);
return x_3138;
}
}
}
}
else
{
lean_object* x_3139; 
lean_free_object(x_3078);
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3139 = lean_box(13);
lean_ctor_set(x_3069, 0, x_3139);
return x_3069;
}
}
else
{
lean_object* x_3140; lean_object* x_3141; lean_object* x_3142; 
lean_free_object(x_3078);
lean_free_object(x_3069);
lean_dec(x_102);
x_3140 = l_Lean_IR_instInhabitedArg;
x_3141 = lean_unsigned_to_nat(2u);
x_3142 = lean_array_get(x_3140, x_3064, x_3141);
lean_dec(x_3064);
if (lean_obj_tag(x_3142) == 0)
{
lean_object* x_3143; lean_object* x_3144; 
x_3143 = lean_ctor_get(x_3142, 0);
lean_inc(x_3143);
lean_dec(x_3142);
x_3144 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3143, x_3, x_4, x_5, x_3072);
return x_3144;
}
else
{
lean_object* x_3145; lean_object* x_3146; 
x_3145 = lean_box(0);
x_3146 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3145, x_3, x_4, x_5, x_3072);
return x_3146;
}
}
}
else
{
lean_object* x_3147; uint8_t x_3148; 
lean_dec(x_3078);
x_3147 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_3148 = lean_name_eq(x_102, x_3147);
if (x_3148 == 0)
{
lean_object* x_3149; uint8_t x_3150; 
x_3149 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_3150 = lean_name_eq(x_102, x_3149);
if (x_3150 == 0)
{
lean_object* x_3151; lean_object* x_3152; 
lean_free_object(x_3069);
lean_inc(x_102);
x_3151 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_3072);
x_3152 = lean_ctor_get(x_3151, 0);
lean_inc(x_3152);
if (lean_obj_tag(x_3152) == 0)
{
lean_object* x_3153; lean_object* x_3154; uint8_t x_3155; lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; 
lean_dec(x_3064);
lean_dec(x_2);
lean_dec(x_1);
x_3153 = lean_ctor_get(x_3151, 1);
lean_inc(x_3153);
if (lean_is_exclusive(x_3151)) {
 lean_ctor_release(x_3151, 0);
 lean_ctor_release(x_3151, 1);
 x_3154 = x_3151;
} else {
 lean_dec_ref(x_3151);
 x_3154 = lean_box(0);
}
x_3155 = 1;
x_3156 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3157 = l_Lean_Name_toString(x_102, x_3155, x_3156);
x_3158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3158, 0, x_3157);
x_3159 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_3154)) {
 x_3160 = lean_alloc_ctor(5, 2, 0);
} else {
 x_3160 = x_3154;
 lean_ctor_set_tag(x_3160, 5);
}
lean_ctor_set(x_3160, 0, x_3159);
lean_ctor_set(x_3160, 1, x_3158);
x_3161 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3162 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3162, 0, x_3160);
lean_ctor_set(x_3162, 1, x_3161);
x_3163 = l_Lean_MessageData_ofFormat(x_3162);
x_3164 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3163, x_3, x_4, x_5, x_3153);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3164;
}
else
{
lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; lean_object* x_3170; uint8_t x_3171; 
x_3165 = lean_ctor_get(x_3151, 1);
lean_inc(x_3165);
if (lean_is_exclusive(x_3151)) {
 lean_ctor_release(x_3151, 0);
 lean_ctor_release(x_3151, 1);
 x_3166 = x_3151;
} else {
 lean_dec_ref(x_3151);
 x_3166 = lean_box(0);
}
x_3167 = lean_ctor_get(x_3152, 0);
lean_inc(x_3167);
lean_dec(x_3152);
x_3168 = lean_array_get_size(x_3064);
x_3169 = l_Lean_IR_Decl_params(x_3167);
lean_dec(x_3167);
x_3170 = lean_array_get_size(x_3169);
lean_dec(x_3169);
x_3171 = lean_nat_dec_lt(x_3168, x_3170);
if (x_3171 == 0)
{
uint8_t x_3172; 
x_3172 = lean_nat_dec_eq(x_3168, x_3170);
if (x_3172 == 0)
{
lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; 
x_3173 = lean_unsigned_to_nat(0u);
x_3174 = l_Array_extract___rarg(x_3064, x_3173, x_3170);
x_3175 = l_Array_extract___rarg(x_3064, x_3170, x_3168);
lean_dec(x_3168);
lean_dec(x_3064);
if (lean_is_scalar(x_3166)) {
 x_3176 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3176 = x_3166;
 lean_ctor_set_tag(x_3176, 6);
}
lean_ctor_set(x_3176, 0, x_102);
lean_ctor_set(x_3176, 1, x_3174);
x_3177 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3176, x_3175, x_3, x_4, x_5, x_3165);
return x_3177;
}
else
{
lean_object* x_3178; lean_object* x_3179; 
lean_dec(x_3170);
lean_dec(x_3168);
if (lean_is_scalar(x_3166)) {
 x_3178 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3178 = x_3166;
 lean_ctor_set_tag(x_3178, 6);
}
lean_ctor_set(x_3178, 0, x_102);
lean_ctor_set(x_3178, 1, x_3064);
x_3179 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3178, x_3, x_4, x_5, x_3165);
return x_3179;
}
}
else
{
lean_object* x_3180; lean_object* x_3181; 
lean_dec(x_3170);
lean_dec(x_3168);
if (lean_is_scalar(x_3166)) {
 x_3180 = lean_alloc_ctor(7, 2, 0);
} else {
 x_3180 = x_3166;
 lean_ctor_set_tag(x_3180, 7);
}
lean_ctor_set(x_3180, 0, x_102);
lean_ctor_set(x_3180, 1, x_3064);
x_3181 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3180, x_3, x_4, x_5, x_3165);
return x_3181;
}
}
}
else
{
lean_object* x_3182; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3182 = lean_box(13);
lean_ctor_set(x_3069, 0, x_3182);
return x_3069;
}
}
else
{
lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; 
lean_free_object(x_3069);
lean_dec(x_102);
x_3183 = l_Lean_IR_instInhabitedArg;
x_3184 = lean_unsigned_to_nat(2u);
x_3185 = lean_array_get(x_3183, x_3064, x_3184);
lean_dec(x_3064);
if (lean_obj_tag(x_3185) == 0)
{
lean_object* x_3186; lean_object* x_3187; 
x_3186 = lean_ctor_get(x_3185, 0);
lean_inc(x_3186);
lean_dec(x_3185);
x_3187 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3186, x_3, x_4, x_5, x_3072);
return x_3187;
}
else
{
lean_object* x_3188; lean_object* x_3189; 
x_3188 = lean_box(0);
x_3189 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3188, x_3, x_4, x_5, x_3072);
return x_3189;
}
}
}
}
case 2:
{
lean_object* x_3190; lean_object* x_3191; 
lean_dec(x_3078);
lean_dec(x_3073);
lean_free_object(x_3069);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3190 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_3191 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3190, x_3, x_4, x_5, x_3072);
return x_3191;
}
case 4:
{
uint8_t x_3192; 
lean_dec(x_3073);
lean_free_object(x_3069);
lean_free_object(x_7);
lean_dec(x_3058);
x_3192 = !lean_is_exclusive(x_3078);
if (x_3192 == 0)
{
lean_object* x_3193; lean_object* x_3194; uint8_t x_3195; 
x_3193 = lean_ctor_get(x_3078, 0);
lean_dec(x_3193);
x_3194 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_3195 = lean_name_eq(x_102, x_3194);
if (x_3195 == 0)
{
uint8_t x_3196; lean_object* x_3197; lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; 
lean_dec(x_3064);
lean_dec(x_2);
lean_dec(x_1);
x_3196 = 1;
x_3197 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3198 = l_Lean_Name_toString(x_102, x_3196, x_3197);
lean_ctor_set_tag(x_3078, 3);
lean_ctor_set(x_3078, 0, x_3198);
x_3199 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_3200 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3200, 0, x_3199);
lean_ctor_set(x_3200, 1, x_3078);
x_3201 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_3202 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3202, 0, x_3200);
lean_ctor_set(x_3202, 1, x_3201);
x_3203 = l_Lean_MessageData_ofFormat(x_3202);
x_3204 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3203, x_3, x_4, x_5, x_3072);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3204;
}
else
{
lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; 
lean_free_object(x_3078);
lean_dec(x_102);
x_3205 = l_Lean_IR_instInhabitedArg;
x_3206 = lean_unsigned_to_nat(2u);
x_3207 = lean_array_get(x_3205, x_3064, x_3206);
lean_dec(x_3064);
if (lean_obj_tag(x_3207) == 0)
{
lean_object* x_3208; lean_object* x_3209; 
x_3208 = lean_ctor_get(x_3207, 0);
lean_inc(x_3208);
lean_dec(x_3207);
x_3209 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3208, x_3, x_4, x_5, x_3072);
return x_3209;
}
else
{
lean_object* x_3210; lean_object* x_3211; 
x_3210 = lean_box(0);
x_3211 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3210, x_3, x_4, x_5, x_3072);
return x_3211;
}
}
}
else
{
lean_object* x_3212; uint8_t x_3213; 
lean_dec(x_3078);
x_3212 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_3213 = lean_name_eq(x_102, x_3212);
if (x_3213 == 0)
{
uint8_t x_3214; lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; 
lean_dec(x_3064);
lean_dec(x_2);
lean_dec(x_1);
x_3214 = 1;
x_3215 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3216 = l_Lean_Name_toString(x_102, x_3214, x_3215);
x_3217 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3217, 0, x_3216);
x_3218 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_3219 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3219, 0, x_3218);
lean_ctor_set(x_3219, 1, x_3217);
x_3220 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_3221 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3221, 0, x_3219);
lean_ctor_set(x_3221, 1, x_3220);
x_3222 = l_Lean_MessageData_ofFormat(x_3221);
x_3223 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3222, x_3, x_4, x_5, x_3072);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3223;
}
else
{
lean_object* x_3224; lean_object* x_3225; lean_object* x_3226; 
lean_dec(x_102);
x_3224 = l_Lean_IR_instInhabitedArg;
x_3225 = lean_unsigned_to_nat(2u);
x_3226 = lean_array_get(x_3224, x_3064, x_3225);
lean_dec(x_3064);
if (lean_obj_tag(x_3226) == 0)
{
lean_object* x_3227; lean_object* x_3228; 
x_3227 = lean_ctor_get(x_3226, 0);
lean_inc(x_3227);
lean_dec(x_3226);
x_3228 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3227, x_3, x_4, x_5, x_3072);
return x_3228;
}
else
{
lean_object* x_3229; lean_object* x_3230; 
x_3229 = lean_box(0);
x_3230 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3229, x_3, x_4, x_5, x_3072);
return x_3230;
}
}
}
}
case 5:
{
lean_object* x_3231; lean_object* x_3232; 
lean_dec(x_3078);
lean_dec(x_3073);
lean_free_object(x_3069);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3231 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_3232 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3231, x_3, x_4, x_5, x_3072);
return x_3232;
}
case 6:
{
lean_object* x_3233; uint8_t x_3234; 
lean_free_object(x_3069);
x_3233 = lean_ctor_get(x_3078, 0);
lean_inc(x_3233);
lean_dec(x_3078);
lean_inc(x_102);
x_3234 = l_Lean_isExtern(x_3073, x_102);
if (x_3234 == 0)
{
lean_object* x_3235; 
lean_dec(x_3064);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3235 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_3072);
if (lean_obj_tag(x_3235) == 0)
{
lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; lean_object* x_3241; lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; lean_object* x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; lean_object* x_3250; 
x_3236 = lean_ctor_get(x_3235, 0);
lean_inc(x_3236);
x_3237 = lean_ctor_get(x_3235, 1);
lean_inc(x_3237);
lean_dec(x_3235);
x_3238 = lean_ctor_get(x_3236, 0);
lean_inc(x_3238);
x_3239 = lean_ctor_get(x_3236, 1);
lean_inc(x_3239);
lean_dec(x_3236);
x_3240 = lean_ctor_get(x_3233, 3);
lean_inc(x_3240);
lean_dec(x_3233);
x_3241 = lean_array_get_size(x_3058);
x_3242 = l_Array_extract___rarg(x_3058, x_3240, x_3241);
lean_dec(x_3241);
lean_dec(x_3058);
x_3243 = lean_array_get_size(x_3239);
x_3244 = lean_unsigned_to_nat(0u);
x_3245 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_3245);
lean_ctor_set(x_7, 1, x_3243);
lean_ctor_set(x_7, 0, x_3244);
x_3246 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_3247 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7(x_3239, x_3242, x_7, x_7, x_3246, x_3244, lean_box(0), lean_box(0), x_3, x_4, x_5, x_3237);
lean_dec(x_7);
x_3248 = lean_ctor_get(x_3247, 0);
lean_inc(x_3248);
x_3249 = lean_ctor_get(x_3247, 1);
lean_inc(x_3249);
lean_dec(x_3247);
x_3250 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_3238, x_3239, x_3242, x_3248, x_3, x_4, x_5, x_3249);
lean_dec(x_3242);
lean_dec(x_3239);
return x_3250;
}
else
{
uint8_t x_3251; 
lean_dec(x_3233);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3251 = !lean_is_exclusive(x_3235);
if (x_3251 == 0)
{
return x_3235;
}
else
{
lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; 
x_3252 = lean_ctor_get(x_3235, 0);
x_3253 = lean_ctor_get(x_3235, 1);
lean_inc(x_3253);
lean_inc(x_3252);
lean_dec(x_3235);
x_3254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3254, 0, x_3252);
lean_ctor_set(x_3254, 1, x_3253);
return x_3254;
}
}
}
else
{
lean_object* x_3255; 
lean_dec(x_3233);
lean_free_object(x_7);
lean_dec(x_3058);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3064);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3255 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3064, x_3, x_4, x_5, x_3072);
if (lean_obj_tag(x_3255) == 0)
{
lean_object* x_3256; 
x_3256 = lean_ctor_get(x_3255, 0);
lean_inc(x_3256);
if (lean_obj_tag(x_3256) == 0)
{
lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; 
x_3257 = lean_ctor_get(x_3255, 1);
lean_inc(x_3257);
lean_dec(x_3255);
x_3258 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3258, 0, x_102);
lean_ctor_set(x_3258, 1, x_3064);
x_3259 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3258, x_3, x_4, x_5, x_3257);
return x_3259;
}
else
{
uint8_t x_3260; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3260 = !lean_is_exclusive(x_3255);
if (x_3260 == 0)
{
lean_object* x_3261; lean_object* x_3262; 
x_3261 = lean_ctor_get(x_3255, 0);
lean_dec(x_3261);
x_3262 = lean_ctor_get(x_3256, 0);
lean_inc(x_3262);
lean_dec(x_3256);
lean_ctor_set(x_3255, 0, x_3262);
return x_3255;
}
else
{
lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; 
x_3263 = lean_ctor_get(x_3255, 1);
lean_inc(x_3263);
lean_dec(x_3255);
x_3264 = lean_ctor_get(x_3256, 0);
lean_inc(x_3264);
lean_dec(x_3256);
x_3265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3265, 0, x_3264);
lean_ctor_set(x_3265, 1, x_3263);
return x_3265;
}
}
}
else
{
uint8_t x_3266; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3266 = !lean_is_exclusive(x_3255);
if (x_3266 == 0)
{
return x_3255;
}
else
{
lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; 
x_3267 = lean_ctor_get(x_3255, 0);
x_3268 = lean_ctor_get(x_3255, 1);
lean_inc(x_3268);
lean_inc(x_3267);
lean_dec(x_3255);
x_3269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3269, 0, x_3267);
lean_ctor_set(x_3269, 1, x_3268);
return x_3269;
}
}
}
}
case 7:
{
uint8_t x_3270; 
lean_dec(x_3073);
lean_free_object(x_3069);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_2);
lean_dec(x_1);
x_3270 = !lean_is_exclusive(x_3078);
if (x_3270 == 0)
{
lean_object* x_3271; uint8_t x_3272; lean_object* x_3273; lean_object* x_3274; lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; 
x_3271 = lean_ctor_get(x_3078, 0);
lean_dec(x_3271);
x_3272 = 1;
x_3273 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3274 = l_Lean_Name_toString(x_102, x_3272, x_3273);
lean_ctor_set_tag(x_3078, 3);
lean_ctor_set(x_3078, 0, x_3274);
x_3275 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3276 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3276, 0, x_3275);
lean_ctor_set(x_3276, 1, x_3078);
x_3277 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3278 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3278, 0, x_3276);
lean_ctor_set(x_3278, 1, x_3277);
x_3279 = l_Lean_MessageData_ofFormat(x_3278);
x_3280 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3279, x_3, x_4, x_5, x_3072);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3280;
}
else
{
uint8_t x_3281; lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; 
lean_dec(x_3078);
x_3281 = 1;
x_3282 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3283 = l_Lean_Name_toString(x_102, x_3281, x_3282);
x_3284 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3284, 0, x_3283);
x_3285 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3286 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3286, 0, x_3285);
lean_ctor_set(x_3286, 1, x_3284);
x_3287 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3288 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3288, 0, x_3286);
lean_ctor_set(x_3288, 1, x_3287);
x_3289 = l_Lean_MessageData_ofFormat(x_3288);
x_3290 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3289, x_3, x_4, x_5, x_3072);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3290;
}
}
default: 
{
lean_object* x_3291; 
lean_dec(x_3078);
lean_dec(x_3073);
lean_free_object(x_3069);
lean_free_object(x_7);
lean_dec(x_3058);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3064);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3291 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3064, x_3, x_4, x_5, x_3072);
if (lean_obj_tag(x_3291) == 0)
{
lean_object* x_3292; 
x_3292 = lean_ctor_get(x_3291, 0);
lean_inc(x_3292);
if (lean_obj_tag(x_3292) == 0)
{
lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; 
x_3293 = lean_ctor_get(x_3291, 1);
lean_inc(x_3293);
lean_dec(x_3291);
x_3294 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3294, 0, x_102);
lean_ctor_set(x_3294, 1, x_3064);
x_3295 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3294, x_3, x_4, x_5, x_3293);
return x_3295;
}
else
{
uint8_t x_3296; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3296 = !lean_is_exclusive(x_3291);
if (x_3296 == 0)
{
lean_object* x_3297; lean_object* x_3298; 
x_3297 = lean_ctor_get(x_3291, 0);
lean_dec(x_3297);
x_3298 = lean_ctor_get(x_3292, 0);
lean_inc(x_3298);
lean_dec(x_3292);
lean_ctor_set(x_3291, 0, x_3298);
return x_3291;
}
else
{
lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; 
x_3299 = lean_ctor_get(x_3291, 1);
lean_inc(x_3299);
lean_dec(x_3291);
x_3300 = lean_ctor_get(x_3292, 0);
lean_inc(x_3300);
lean_dec(x_3292);
x_3301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3301, 0, x_3300);
lean_ctor_set(x_3301, 1, x_3299);
return x_3301;
}
}
}
else
{
uint8_t x_3302; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3302 = !lean_is_exclusive(x_3291);
if (x_3302 == 0)
{
return x_3291;
}
else
{
lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; 
x_3303 = lean_ctor_get(x_3291, 0);
x_3304 = lean_ctor_get(x_3291, 1);
lean_inc(x_3304);
lean_inc(x_3303);
lean_dec(x_3291);
x_3305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3305, 0, x_3303);
lean_ctor_set(x_3305, 1, x_3304);
return x_3305;
}
}
}
}
}
}
else
{
lean_object* x_3306; lean_object* x_3307; lean_object* x_3308; uint8_t x_3309; lean_object* x_3310; 
x_3306 = lean_ctor_get(x_3069, 0);
x_3307 = lean_ctor_get(x_3069, 1);
lean_inc(x_3307);
lean_inc(x_3306);
lean_dec(x_3069);
x_3308 = lean_ctor_get(x_3306, 0);
lean_inc(x_3308);
lean_dec(x_3306);
x_3309 = 0;
lean_inc(x_102);
lean_inc(x_3308);
x_3310 = l_Lean_Environment_find_x3f(x_3308, x_102, x_3309);
if (lean_obj_tag(x_3310) == 0)
{
lean_object* x_3311; lean_object* x_3312; 
lean_dec(x_3308);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3311 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_3312 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3311, x_3, x_4, x_5, x_3307);
return x_3312;
}
else
{
lean_object* x_3313; 
x_3313 = lean_ctor_get(x_3310, 0);
lean_inc(x_3313);
lean_dec(x_3310);
switch (lean_obj_tag(x_3313)) {
case 0:
{
lean_object* x_3314; lean_object* x_3315; uint8_t x_3316; 
lean_dec(x_3308);
lean_free_object(x_7);
lean_dec(x_3058);
if (lean_is_exclusive(x_3313)) {
 lean_ctor_release(x_3313, 0);
 x_3314 = x_3313;
} else {
 lean_dec_ref(x_3313);
 x_3314 = lean_box(0);
}
x_3315 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_3316 = lean_name_eq(x_102, x_3315);
if (x_3316 == 0)
{
lean_object* x_3317; uint8_t x_3318; 
x_3317 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_3318 = lean_name_eq(x_102, x_3317);
if (x_3318 == 0)
{
lean_object* x_3319; lean_object* x_3320; 
lean_inc(x_102);
x_3319 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_3307);
x_3320 = lean_ctor_get(x_3319, 0);
lean_inc(x_3320);
if (lean_obj_tag(x_3320) == 0)
{
lean_object* x_3321; lean_object* x_3322; uint8_t x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; 
lean_dec(x_3064);
lean_dec(x_2);
lean_dec(x_1);
x_3321 = lean_ctor_get(x_3319, 1);
lean_inc(x_3321);
if (lean_is_exclusive(x_3319)) {
 lean_ctor_release(x_3319, 0);
 lean_ctor_release(x_3319, 1);
 x_3322 = x_3319;
} else {
 lean_dec_ref(x_3319);
 x_3322 = lean_box(0);
}
x_3323 = 1;
x_3324 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3325 = l_Lean_Name_toString(x_102, x_3323, x_3324);
if (lean_is_scalar(x_3314)) {
 x_3326 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3326 = x_3314;
 lean_ctor_set_tag(x_3326, 3);
}
lean_ctor_set(x_3326, 0, x_3325);
x_3327 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_3322)) {
 x_3328 = lean_alloc_ctor(5, 2, 0);
} else {
 x_3328 = x_3322;
 lean_ctor_set_tag(x_3328, 5);
}
lean_ctor_set(x_3328, 0, x_3327);
lean_ctor_set(x_3328, 1, x_3326);
x_3329 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3330 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3330, 0, x_3328);
lean_ctor_set(x_3330, 1, x_3329);
x_3331 = l_Lean_MessageData_ofFormat(x_3330);
x_3332 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3331, x_3, x_4, x_5, x_3321);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3332;
}
else
{
lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; uint8_t x_3339; 
lean_dec(x_3314);
x_3333 = lean_ctor_get(x_3319, 1);
lean_inc(x_3333);
if (lean_is_exclusive(x_3319)) {
 lean_ctor_release(x_3319, 0);
 lean_ctor_release(x_3319, 1);
 x_3334 = x_3319;
} else {
 lean_dec_ref(x_3319);
 x_3334 = lean_box(0);
}
x_3335 = lean_ctor_get(x_3320, 0);
lean_inc(x_3335);
lean_dec(x_3320);
x_3336 = lean_array_get_size(x_3064);
x_3337 = l_Lean_IR_Decl_params(x_3335);
lean_dec(x_3335);
x_3338 = lean_array_get_size(x_3337);
lean_dec(x_3337);
x_3339 = lean_nat_dec_lt(x_3336, x_3338);
if (x_3339 == 0)
{
uint8_t x_3340; 
x_3340 = lean_nat_dec_eq(x_3336, x_3338);
if (x_3340 == 0)
{
lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; 
x_3341 = lean_unsigned_to_nat(0u);
x_3342 = l_Array_extract___rarg(x_3064, x_3341, x_3338);
x_3343 = l_Array_extract___rarg(x_3064, x_3338, x_3336);
lean_dec(x_3336);
lean_dec(x_3064);
if (lean_is_scalar(x_3334)) {
 x_3344 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3344 = x_3334;
 lean_ctor_set_tag(x_3344, 6);
}
lean_ctor_set(x_3344, 0, x_102);
lean_ctor_set(x_3344, 1, x_3342);
x_3345 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3344, x_3343, x_3, x_4, x_5, x_3333);
return x_3345;
}
else
{
lean_object* x_3346; lean_object* x_3347; 
lean_dec(x_3338);
lean_dec(x_3336);
if (lean_is_scalar(x_3334)) {
 x_3346 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3346 = x_3334;
 lean_ctor_set_tag(x_3346, 6);
}
lean_ctor_set(x_3346, 0, x_102);
lean_ctor_set(x_3346, 1, x_3064);
x_3347 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3346, x_3, x_4, x_5, x_3333);
return x_3347;
}
}
else
{
lean_object* x_3348; lean_object* x_3349; 
lean_dec(x_3338);
lean_dec(x_3336);
if (lean_is_scalar(x_3334)) {
 x_3348 = lean_alloc_ctor(7, 2, 0);
} else {
 x_3348 = x_3334;
 lean_ctor_set_tag(x_3348, 7);
}
lean_ctor_set(x_3348, 0, x_102);
lean_ctor_set(x_3348, 1, x_3064);
x_3349 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3348, x_3, x_4, x_5, x_3333);
return x_3349;
}
}
}
else
{
lean_object* x_3350; lean_object* x_3351; 
lean_dec(x_3314);
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3350 = lean_box(13);
x_3351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3351, 0, x_3350);
lean_ctor_set(x_3351, 1, x_3307);
return x_3351;
}
}
else
{
lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; 
lean_dec(x_3314);
lean_dec(x_102);
x_3352 = l_Lean_IR_instInhabitedArg;
x_3353 = lean_unsigned_to_nat(2u);
x_3354 = lean_array_get(x_3352, x_3064, x_3353);
lean_dec(x_3064);
if (lean_obj_tag(x_3354) == 0)
{
lean_object* x_3355; lean_object* x_3356; 
x_3355 = lean_ctor_get(x_3354, 0);
lean_inc(x_3355);
lean_dec(x_3354);
x_3356 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3355, x_3, x_4, x_5, x_3307);
return x_3356;
}
else
{
lean_object* x_3357; lean_object* x_3358; 
x_3357 = lean_box(0);
x_3358 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3357, x_3, x_4, x_5, x_3307);
return x_3358;
}
}
}
case 2:
{
lean_object* x_3359; lean_object* x_3360; 
lean_dec(x_3313);
lean_dec(x_3308);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3359 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_3360 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3359, x_3, x_4, x_5, x_3307);
return x_3360;
}
case 4:
{
lean_object* x_3361; lean_object* x_3362; uint8_t x_3363; 
lean_dec(x_3308);
lean_free_object(x_7);
lean_dec(x_3058);
if (lean_is_exclusive(x_3313)) {
 lean_ctor_release(x_3313, 0);
 x_3361 = x_3313;
} else {
 lean_dec_ref(x_3313);
 x_3361 = lean_box(0);
}
x_3362 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_3363 = lean_name_eq(x_102, x_3362);
if (x_3363 == 0)
{
uint8_t x_3364; lean_object* x_3365; lean_object* x_3366; lean_object* x_3367; lean_object* x_3368; lean_object* x_3369; lean_object* x_3370; lean_object* x_3371; lean_object* x_3372; lean_object* x_3373; 
lean_dec(x_3064);
lean_dec(x_2);
lean_dec(x_1);
x_3364 = 1;
x_3365 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3366 = l_Lean_Name_toString(x_102, x_3364, x_3365);
if (lean_is_scalar(x_3361)) {
 x_3367 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3367 = x_3361;
 lean_ctor_set_tag(x_3367, 3);
}
lean_ctor_set(x_3367, 0, x_3366);
x_3368 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_3369 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3369, 0, x_3368);
lean_ctor_set(x_3369, 1, x_3367);
x_3370 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_3371 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3371, 0, x_3369);
lean_ctor_set(x_3371, 1, x_3370);
x_3372 = l_Lean_MessageData_ofFormat(x_3371);
x_3373 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3372, x_3, x_4, x_5, x_3307);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3373;
}
else
{
lean_object* x_3374; lean_object* x_3375; lean_object* x_3376; 
lean_dec(x_3361);
lean_dec(x_102);
x_3374 = l_Lean_IR_instInhabitedArg;
x_3375 = lean_unsigned_to_nat(2u);
x_3376 = lean_array_get(x_3374, x_3064, x_3375);
lean_dec(x_3064);
if (lean_obj_tag(x_3376) == 0)
{
lean_object* x_3377; lean_object* x_3378; 
x_3377 = lean_ctor_get(x_3376, 0);
lean_inc(x_3377);
lean_dec(x_3376);
x_3378 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3377, x_3, x_4, x_5, x_3307);
return x_3378;
}
else
{
lean_object* x_3379; lean_object* x_3380; 
x_3379 = lean_box(0);
x_3380 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3379, x_3, x_4, x_5, x_3307);
return x_3380;
}
}
}
case 5:
{
lean_object* x_3381; lean_object* x_3382; 
lean_dec(x_3313);
lean_dec(x_3308);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3381 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_3382 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3381, x_3, x_4, x_5, x_3307);
return x_3382;
}
case 6:
{
lean_object* x_3383; uint8_t x_3384; 
x_3383 = lean_ctor_get(x_3313, 0);
lean_inc(x_3383);
lean_dec(x_3313);
lean_inc(x_102);
x_3384 = l_Lean_isExtern(x_3308, x_102);
if (x_3384 == 0)
{
lean_object* x_3385; 
lean_dec(x_3064);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3385 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_3307);
if (lean_obj_tag(x_3385) == 0)
{
lean_object* x_3386; lean_object* x_3387; lean_object* x_3388; lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; 
x_3386 = lean_ctor_get(x_3385, 0);
lean_inc(x_3386);
x_3387 = lean_ctor_get(x_3385, 1);
lean_inc(x_3387);
lean_dec(x_3385);
x_3388 = lean_ctor_get(x_3386, 0);
lean_inc(x_3388);
x_3389 = lean_ctor_get(x_3386, 1);
lean_inc(x_3389);
lean_dec(x_3386);
x_3390 = lean_ctor_get(x_3383, 3);
lean_inc(x_3390);
lean_dec(x_3383);
x_3391 = lean_array_get_size(x_3058);
x_3392 = l_Array_extract___rarg(x_3058, x_3390, x_3391);
lean_dec(x_3391);
lean_dec(x_3058);
x_3393 = lean_array_get_size(x_3389);
x_3394 = lean_unsigned_to_nat(0u);
x_3395 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_3395);
lean_ctor_set(x_7, 1, x_3393);
lean_ctor_set(x_7, 0, x_3394);
x_3396 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_3397 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7(x_3389, x_3392, x_7, x_7, x_3396, x_3394, lean_box(0), lean_box(0), x_3, x_4, x_5, x_3387);
lean_dec(x_7);
x_3398 = lean_ctor_get(x_3397, 0);
lean_inc(x_3398);
x_3399 = lean_ctor_get(x_3397, 1);
lean_inc(x_3399);
lean_dec(x_3397);
x_3400 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_3388, x_3389, x_3392, x_3398, x_3, x_4, x_5, x_3399);
lean_dec(x_3392);
lean_dec(x_3389);
return x_3400;
}
else
{
lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; 
lean_dec(x_3383);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3401 = lean_ctor_get(x_3385, 0);
lean_inc(x_3401);
x_3402 = lean_ctor_get(x_3385, 1);
lean_inc(x_3402);
if (lean_is_exclusive(x_3385)) {
 lean_ctor_release(x_3385, 0);
 lean_ctor_release(x_3385, 1);
 x_3403 = x_3385;
} else {
 lean_dec_ref(x_3385);
 x_3403 = lean_box(0);
}
if (lean_is_scalar(x_3403)) {
 x_3404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3404 = x_3403;
}
lean_ctor_set(x_3404, 0, x_3401);
lean_ctor_set(x_3404, 1, x_3402);
return x_3404;
}
}
else
{
lean_object* x_3405; 
lean_dec(x_3383);
lean_free_object(x_7);
lean_dec(x_3058);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3064);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3405 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3064, x_3, x_4, x_5, x_3307);
if (lean_obj_tag(x_3405) == 0)
{
lean_object* x_3406; 
x_3406 = lean_ctor_get(x_3405, 0);
lean_inc(x_3406);
if (lean_obj_tag(x_3406) == 0)
{
lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; 
x_3407 = lean_ctor_get(x_3405, 1);
lean_inc(x_3407);
lean_dec(x_3405);
x_3408 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3408, 0, x_102);
lean_ctor_set(x_3408, 1, x_3064);
x_3409 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3408, x_3, x_4, x_5, x_3407);
return x_3409;
}
else
{
lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3410 = lean_ctor_get(x_3405, 1);
lean_inc(x_3410);
if (lean_is_exclusive(x_3405)) {
 lean_ctor_release(x_3405, 0);
 lean_ctor_release(x_3405, 1);
 x_3411 = x_3405;
} else {
 lean_dec_ref(x_3405);
 x_3411 = lean_box(0);
}
x_3412 = lean_ctor_get(x_3406, 0);
lean_inc(x_3412);
lean_dec(x_3406);
if (lean_is_scalar(x_3411)) {
 x_3413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3413 = x_3411;
}
lean_ctor_set(x_3413, 0, x_3412);
lean_ctor_set(x_3413, 1, x_3410);
return x_3413;
}
}
else
{
lean_object* x_3414; lean_object* x_3415; lean_object* x_3416; lean_object* x_3417; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3414 = lean_ctor_get(x_3405, 0);
lean_inc(x_3414);
x_3415 = lean_ctor_get(x_3405, 1);
lean_inc(x_3415);
if (lean_is_exclusive(x_3405)) {
 lean_ctor_release(x_3405, 0);
 lean_ctor_release(x_3405, 1);
 x_3416 = x_3405;
} else {
 lean_dec_ref(x_3405);
 x_3416 = lean_box(0);
}
if (lean_is_scalar(x_3416)) {
 x_3417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3417 = x_3416;
}
lean_ctor_set(x_3417, 0, x_3414);
lean_ctor_set(x_3417, 1, x_3415);
return x_3417;
}
}
}
case 7:
{
lean_object* x_3418; uint8_t x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; lean_object* x_3427; lean_object* x_3428; 
lean_dec(x_3308);
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_3313)) {
 lean_ctor_release(x_3313, 0);
 x_3418 = x_3313;
} else {
 lean_dec_ref(x_3313);
 x_3418 = lean_box(0);
}
x_3419 = 1;
x_3420 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3421 = l_Lean_Name_toString(x_102, x_3419, x_3420);
if (lean_is_scalar(x_3418)) {
 x_3422 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3422 = x_3418;
 lean_ctor_set_tag(x_3422, 3);
}
lean_ctor_set(x_3422, 0, x_3421);
x_3423 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3424 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3424, 0, x_3423);
lean_ctor_set(x_3424, 1, x_3422);
x_3425 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3426 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3426, 0, x_3424);
lean_ctor_set(x_3426, 1, x_3425);
x_3427 = l_Lean_MessageData_ofFormat(x_3426);
x_3428 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3427, x_3, x_4, x_5, x_3307);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3428;
}
default: 
{
lean_object* x_3429; 
lean_dec(x_3313);
lean_dec(x_3308);
lean_free_object(x_7);
lean_dec(x_3058);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3064);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3429 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3064, x_3, x_4, x_5, x_3307);
if (lean_obj_tag(x_3429) == 0)
{
lean_object* x_3430; 
x_3430 = lean_ctor_get(x_3429, 0);
lean_inc(x_3430);
if (lean_obj_tag(x_3430) == 0)
{
lean_object* x_3431; lean_object* x_3432; lean_object* x_3433; 
x_3431 = lean_ctor_get(x_3429, 1);
lean_inc(x_3431);
lean_dec(x_3429);
x_3432 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3432, 0, x_102);
lean_ctor_set(x_3432, 1, x_3064);
x_3433 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3432, x_3, x_4, x_5, x_3431);
return x_3433;
}
else
{
lean_object* x_3434; lean_object* x_3435; lean_object* x_3436; lean_object* x_3437; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3434 = lean_ctor_get(x_3429, 1);
lean_inc(x_3434);
if (lean_is_exclusive(x_3429)) {
 lean_ctor_release(x_3429, 0);
 lean_ctor_release(x_3429, 1);
 x_3435 = x_3429;
} else {
 lean_dec_ref(x_3429);
 x_3435 = lean_box(0);
}
x_3436 = lean_ctor_get(x_3430, 0);
lean_inc(x_3436);
lean_dec(x_3430);
if (lean_is_scalar(x_3435)) {
 x_3437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3437 = x_3435;
}
lean_ctor_set(x_3437, 0, x_3436);
lean_ctor_set(x_3437, 1, x_3434);
return x_3437;
}
}
else
{
lean_object* x_3438; lean_object* x_3439; lean_object* x_3440; lean_object* x_3441; 
lean_dec(x_3064);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3438 = lean_ctor_get(x_3429, 0);
lean_inc(x_3438);
x_3439 = lean_ctor_get(x_3429, 1);
lean_inc(x_3439);
if (lean_is_exclusive(x_3429)) {
 lean_ctor_release(x_3429, 0);
 lean_ctor_release(x_3429, 1);
 x_3440 = x_3429;
} else {
 lean_dec_ref(x_3429);
 x_3440 = lean_box(0);
}
if (lean_is_scalar(x_3440)) {
 x_3441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3441 = x_3440;
}
lean_ctor_set(x_3441, 0, x_3438);
lean_ctor_set(x_3441, 1, x_3439);
return x_3441;
}
}
}
}
}
}
else
{
uint8_t x_3442; 
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3442 = !lean_is_exclusive(x_3066);
if (x_3442 == 0)
{
lean_object* x_3443; lean_object* x_3444; 
x_3443 = lean_ctor_get(x_3066, 0);
lean_dec(x_3443);
x_3444 = lean_ctor_get(x_3067, 0);
lean_inc(x_3444);
lean_dec(x_3067);
lean_ctor_set(x_3066, 0, x_3444);
return x_3066;
}
else
{
lean_object* x_3445; lean_object* x_3446; lean_object* x_3447; 
x_3445 = lean_ctor_get(x_3066, 1);
lean_inc(x_3445);
lean_dec(x_3066);
x_3446 = lean_ctor_get(x_3067, 0);
lean_inc(x_3446);
lean_dec(x_3067);
x_3447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3447, 0, x_3446);
lean_ctor_set(x_3447, 1, x_3445);
return x_3447;
}
}
}
else
{
uint8_t x_3448; 
lean_dec(x_3064);
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3448 = !lean_is_exclusive(x_3066);
if (x_3448 == 0)
{
return x_3066;
}
else
{
lean_object* x_3449; lean_object* x_3450; lean_object* x_3451; 
x_3449 = lean_ctor_get(x_3066, 0);
x_3450 = lean_ctor_get(x_3066, 1);
lean_inc(x_3450);
lean_inc(x_3449);
lean_dec(x_3066);
x_3451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3451, 0, x_3449);
lean_ctor_set(x_3451, 1, x_3450);
return x_3451;
}
}
}
else
{
uint8_t x_3452; 
lean_free_object(x_7);
lean_dec(x_3058);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3452 = !lean_is_exclusive(x_3063);
if (x_3452 == 0)
{
return x_3063;
}
else
{
lean_object* x_3453; lean_object* x_3454; lean_object* x_3455; 
x_3453 = lean_ctor_get(x_3063, 0);
x_3454 = lean_ctor_get(x_3063, 1);
lean_inc(x_3454);
lean_inc(x_3453);
lean_dec(x_3063);
x_3455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3455, 0, x_3453);
lean_ctor_set(x_3455, 1, x_3454);
return x_3455;
}
}
}
else
{
lean_object* x_3456; size_t x_3457; size_t x_3458; lean_object* x_3459; 
x_3456 = lean_ctor_get(x_7, 2);
lean_inc(x_3456);
lean_dec(x_7);
x_3457 = lean_array_size(x_3456);
x_3458 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3456);
x_3459 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_3457, x_3458, x_3456, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_3459) == 0)
{
lean_object* x_3460; lean_object* x_3461; lean_object* x_3462; 
x_3460 = lean_ctor_get(x_3459, 0);
lean_inc(x_3460);
x_3461 = lean_ctor_get(x_3459, 1);
lean_inc(x_3461);
lean_dec(x_3459);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3460);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3462 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3460, x_3, x_4, x_5, x_3461);
if (lean_obj_tag(x_3462) == 0)
{
lean_object* x_3463; 
x_3463 = lean_ctor_get(x_3462, 0);
lean_inc(x_3463);
if (lean_obj_tag(x_3463) == 0)
{
lean_object* x_3464; lean_object* x_3465; lean_object* x_3466; lean_object* x_3467; lean_object* x_3468; lean_object* x_3469; uint8_t x_3470; lean_object* x_3471; 
x_3464 = lean_ctor_get(x_3462, 1);
lean_inc(x_3464);
lean_dec(x_3462);
x_3465 = lean_st_ref_get(x_5, x_3464);
x_3466 = lean_ctor_get(x_3465, 0);
lean_inc(x_3466);
x_3467 = lean_ctor_get(x_3465, 1);
lean_inc(x_3467);
if (lean_is_exclusive(x_3465)) {
 lean_ctor_release(x_3465, 0);
 lean_ctor_release(x_3465, 1);
 x_3468 = x_3465;
} else {
 lean_dec_ref(x_3465);
 x_3468 = lean_box(0);
}
x_3469 = lean_ctor_get(x_3466, 0);
lean_inc(x_3469);
lean_dec(x_3466);
x_3470 = 0;
lean_inc(x_102);
lean_inc(x_3469);
x_3471 = l_Lean_Environment_find_x3f(x_3469, x_102, x_3470);
if (lean_obj_tag(x_3471) == 0)
{
lean_object* x_3472; lean_object* x_3473; 
lean_dec(x_3469);
lean_dec(x_3468);
lean_dec(x_3460);
lean_dec(x_3456);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3472 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_3473 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3472, x_3, x_4, x_5, x_3467);
return x_3473;
}
else
{
lean_object* x_3474; 
x_3474 = lean_ctor_get(x_3471, 0);
lean_inc(x_3474);
lean_dec(x_3471);
switch (lean_obj_tag(x_3474)) {
case 0:
{
lean_object* x_3475; lean_object* x_3476; uint8_t x_3477; 
lean_dec(x_3469);
lean_dec(x_3456);
if (lean_is_exclusive(x_3474)) {
 lean_ctor_release(x_3474, 0);
 x_3475 = x_3474;
} else {
 lean_dec_ref(x_3474);
 x_3475 = lean_box(0);
}
x_3476 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_3477 = lean_name_eq(x_102, x_3476);
if (x_3477 == 0)
{
lean_object* x_3478; uint8_t x_3479; 
x_3478 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_3479 = lean_name_eq(x_102, x_3478);
if (x_3479 == 0)
{
lean_object* x_3480; lean_object* x_3481; 
lean_dec(x_3468);
lean_inc(x_102);
x_3480 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_3467);
x_3481 = lean_ctor_get(x_3480, 0);
lean_inc(x_3481);
if (lean_obj_tag(x_3481) == 0)
{
lean_object* x_3482; lean_object* x_3483; uint8_t x_3484; lean_object* x_3485; lean_object* x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; lean_object* x_3490; lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; 
lean_dec(x_3460);
lean_dec(x_2);
lean_dec(x_1);
x_3482 = lean_ctor_get(x_3480, 1);
lean_inc(x_3482);
if (lean_is_exclusive(x_3480)) {
 lean_ctor_release(x_3480, 0);
 lean_ctor_release(x_3480, 1);
 x_3483 = x_3480;
} else {
 lean_dec_ref(x_3480);
 x_3483 = lean_box(0);
}
x_3484 = 1;
x_3485 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3486 = l_Lean_Name_toString(x_102, x_3484, x_3485);
if (lean_is_scalar(x_3475)) {
 x_3487 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3487 = x_3475;
 lean_ctor_set_tag(x_3487, 3);
}
lean_ctor_set(x_3487, 0, x_3486);
x_3488 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_3483)) {
 x_3489 = lean_alloc_ctor(5, 2, 0);
} else {
 x_3489 = x_3483;
 lean_ctor_set_tag(x_3489, 5);
}
lean_ctor_set(x_3489, 0, x_3488);
lean_ctor_set(x_3489, 1, x_3487);
x_3490 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3491 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3491, 0, x_3489);
lean_ctor_set(x_3491, 1, x_3490);
x_3492 = l_Lean_MessageData_ofFormat(x_3491);
x_3493 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3492, x_3, x_4, x_5, x_3482);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3493;
}
else
{
lean_object* x_3494; lean_object* x_3495; lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; lean_object* x_3499; uint8_t x_3500; 
lean_dec(x_3475);
x_3494 = lean_ctor_get(x_3480, 1);
lean_inc(x_3494);
if (lean_is_exclusive(x_3480)) {
 lean_ctor_release(x_3480, 0);
 lean_ctor_release(x_3480, 1);
 x_3495 = x_3480;
} else {
 lean_dec_ref(x_3480);
 x_3495 = lean_box(0);
}
x_3496 = lean_ctor_get(x_3481, 0);
lean_inc(x_3496);
lean_dec(x_3481);
x_3497 = lean_array_get_size(x_3460);
x_3498 = l_Lean_IR_Decl_params(x_3496);
lean_dec(x_3496);
x_3499 = lean_array_get_size(x_3498);
lean_dec(x_3498);
x_3500 = lean_nat_dec_lt(x_3497, x_3499);
if (x_3500 == 0)
{
uint8_t x_3501; 
x_3501 = lean_nat_dec_eq(x_3497, x_3499);
if (x_3501 == 0)
{
lean_object* x_3502; lean_object* x_3503; lean_object* x_3504; lean_object* x_3505; lean_object* x_3506; 
x_3502 = lean_unsigned_to_nat(0u);
x_3503 = l_Array_extract___rarg(x_3460, x_3502, x_3499);
x_3504 = l_Array_extract___rarg(x_3460, x_3499, x_3497);
lean_dec(x_3497);
lean_dec(x_3460);
if (lean_is_scalar(x_3495)) {
 x_3505 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3505 = x_3495;
 lean_ctor_set_tag(x_3505, 6);
}
lean_ctor_set(x_3505, 0, x_102);
lean_ctor_set(x_3505, 1, x_3503);
x_3506 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3505, x_3504, x_3, x_4, x_5, x_3494);
return x_3506;
}
else
{
lean_object* x_3507; lean_object* x_3508; 
lean_dec(x_3499);
lean_dec(x_3497);
if (lean_is_scalar(x_3495)) {
 x_3507 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3507 = x_3495;
 lean_ctor_set_tag(x_3507, 6);
}
lean_ctor_set(x_3507, 0, x_102);
lean_ctor_set(x_3507, 1, x_3460);
x_3508 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3507, x_3, x_4, x_5, x_3494);
return x_3508;
}
}
else
{
lean_object* x_3509; lean_object* x_3510; 
lean_dec(x_3499);
lean_dec(x_3497);
if (lean_is_scalar(x_3495)) {
 x_3509 = lean_alloc_ctor(7, 2, 0);
} else {
 x_3509 = x_3495;
 lean_ctor_set_tag(x_3509, 7);
}
lean_ctor_set(x_3509, 0, x_102);
lean_ctor_set(x_3509, 1, x_3460);
x_3510 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3509, x_3, x_4, x_5, x_3494);
return x_3510;
}
}
}
else
{
lean_object* x_3511; lean_object* x_3512; 
lean_dec(x_3475);
lean_dec(x_3460);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3511 = lean_box(13);
if (lean_is_scalar(x_3468)) {
 x_3512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3512 = x_3468;
}
lean_ctor_set(x_3512, 0, x_3511);
lean_ctor_set(x_3512, 1, x_3467);
return x_3512;
}
}
else
{
lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; 
lean_dec(x_3475);
lean_dec(x_3468);
lean_dec(x_102);
x_3513 = l_Lean_IR_instInhabitedArg;
x_3514 = lean_unsigned_to_nat(2u);
x_3515 = lean_array_get(x_3513, x_3460, x_3514);
lean_dec(x_3460);
if (lean_obj_tag(x_3515) == 0)
{
lean_object* x_3516; lean_object* x_3517; 
x_3516 = lean_ctor_get(x_3515, 0);
lean_inc(x_3516);
lean_dec(x_3515);
x_3517 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3516, x_3, x_4, x_5, x_3467);
return x_3517;
}
else
{
lean_object* x_3518; lean_object* x_3519; 
x_3518 = lean_box(0);
x_3519 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3518, x_3, x_4, x_5, x_3467);
return x_3519;
}
}
}
case 2:
{
lean_object* x_3520; lean_object* x_3521; 
lean_dec(x_3474);
lean_dec(x_3469);
lean_dec(x_3468);
lean_dec(x_3460);
lean_dec(x_3456);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3520 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_3521 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3520, x_3, x_4, x_5, x_3467);
return x_3521;
}
case 4:
{
lean_object* x_3522; lean_object* x_3523; uint8_t x_3524; 
lean_dec(x_3469);
lean_dec(x_3468);
lean_dec(x_3456);
if (lean_is_exclusive(x_3474)) {
 lean_ctor_release(x_3474, 0);
 x_3522 = x_3474;
} else {
 lean_dec_ref(x_3474);
 x_3522 = lean_box(0);
}
x_3523 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_3524 = lean_name_eq(x_102, x_3523);
if (x_3524 == 0)
{
uint8_t x_3525; lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; lean_object* x_3529; lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; lean_object* x_3534; 
lean_dec(x_3460);
lean_dec(x_2);
lean_dec(x_1);
x_3525 = 1;
x_3526 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3527 = l_Lean_Name_toString(x_102, x_3525, x_3526);
if (lean_is_scalar(x_3522)) {
 x_3528 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3528 = x_3522;
 lean_ctor_set_tag(x_3528, 3);
}
lean_ctor_set(x_3528, 0, x_3527);
x_3529 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_3530 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3530, 0, x_3529);
lean_ctor_set(x_3530, 1, x_3528);
x_3531 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_3532 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3532, 0, x_3530);
lean_ctor_set(x_3532, 1, x_3531);
x_3533 = l_Lean_MessageData_ofFormat(x_3532);
x_3534 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3533, x_3, x_4, x_5, x_3467);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3534;
}
else
{
lean_object* x_3535; lean_object* x_3536; lean_object* x_3537; 
lean_dec(x_3522);
lean_dec(x_102);
x_3535 = l_Lean_IR_instInhabitedArg;
x_3536 = lean_unsigned_to_nat(2u);
x_3537 = lean_array_get(x_3535, x_3460, x_3536);
lean_dec(x_3460);
if (lean_obj_tag(x_3537) == 0)
{
lean_object* x_3538; lean_object* x_3539; 
x_3538 = lean_ctor_get(x_3537, 0);
lean_inc(x_3538);
lean_dec(x_3537);
x_3539 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3538, x_3, x_4, x_5, x_3467);
return x_3539;
}
else
{
lean_object* x_3540; lean_object* x_3541; 
x_3540 = lean_box(0);
x_3541 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3540, x_3, x_4, x_5, x_3467);
return x_3541;
}
}
}
case 5:
{
lean_object* x_3542; lean_object* x_3543; 
lean_dec(x_3474);
lean_dec(x_3469);
lean_dec(x_3468);
lean_dec(x_3460);
lean_dec(x_3456);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3542 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_3543 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3542, x_3, x_4, x_5, x_3467);
return x_3543;
}
case 6:
{
lean_object* x_3544; uint8_t x_3545; 
lean_dec(x_3468);
x_3544 = lean_ctor_get(x_3474, 0);
lean_inc(x_3544);
lean_dec(x_3474);
lean_inc(x_102);
x_3545 = l_Lean_isExtern(x_3469, x_102);
if (x_3545 == 0)
{
lean_object* x_3546; 
lean_dec(x_3460);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3546 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_3467);
if (lean_obj_tag(x_3546) == 0)
{
lean_object* x_3547; lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; lean_object* x_3553; lean_object* x_3554; lean_object* x_3555; lean_object* x_3556; lean_object* x_3557; lean_object* x_3558; lean_object* x_3559; lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; 
x_3547 = lean_ctor_get(x_3546, 0);
lean_inc(x_3547);
x_3548 = lean_ctor_get(x_3546, 1);
lean_inc(x_3548);
lean_dec(x_3546);
x_3549 = lean_ctor_get(x_3547, 0);
lean_inc(x_3549);
x_3550 = lean_ctor_get(x_3547, 1);
lean_inc(x_3550);
lean_dec(x_3547);
x_3551 = lean_ctor_get(x_3544, 3);
lean_inc(x_3551);
lean_dec(x_3544);
x_3552 = lean_array_get_size(x_3456);
x_3553 = l_Array_extract___rarg(x_3456, x_3551, x_3552);
lean_dec(x_3552);
lean_dec(x_3456);
x_3554 = lean_array_get_size(x_3550);
x_3555 = lean_unsigned_to_nat(0u);
x_3556 = lean_unsigned_to_nat(1u);
x_3557 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3557, 0, x_3555);
lean_ctor_set(x_3557, 1, x_3554);
lean_ctor_set(x_3557, 2, x_3556);
x_3558 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_3559 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7(x_3550, x_3553, x_3557, x_3557, x_3558, x_3555, lean_box(0), lean_box(0), x_3, x_4, x_5, x_3548);
lean_dec(x_3557);
x_3560 = lean_ctor_get(x_3559, 0);
lean_inc(x_3560);
x_3561 = lean_ctor_get(x_3559, 1);
lean_inc(x_3561);
lean_dec(x_3559);
x_3562 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_3549, x_3550, x_3553, x_3560, x_3, x_4, x_5, x_3561);
lean_dec(x_3553);
lean_dec(x_3550);
return x_3562;
}
else
{
lean_object* x_3563; lean_object* x_3564; lean_object* x_3565; lean_object* x_3566; 
lean_dec(x_3544);
lean_dec(x_3456);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3563 = lean_ctor_get(x_3546, 0);
lean_inc(x_3563);
x_3564 = lean_ctor_get(x_3546, 1);
lean_inc(x_3564);
if (lean_is_exclusive(x_3546)) {
 lean_ctor_release(x_3546, 0);
 lean_ctor_release(x_3546, 1);
 x_3565 = x_3546;
} else {
 lean_dec_ref(x_3546);
 x_3565 = lean_box(0);
}
if (lean_is_scalar(x_3565)) {
 x_3566 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3566 = x_3565;
}
lean_ctor_set(x_3566, 0, x_3563);
lean_ctor_set(x_3566, 1, x_3564);
return x_3566;
}
}
else
{
lean_object* x_3567; 
lean_dec(x_3544);
lean_dec(x_3456);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3460);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3567 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3460, x_3, x_4, x_5, x_3467);
if (lean_obj_tag(x_3567) == 0)
{
lean_object* x_3568; 
x_3568 = lean_ctor_get(x_3567, 0);
lean_inc(x_3568);
if (lean_obj_tag(x_3568) == 0)
{
lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; 
x_3569 = lean_ctor_get(x_3567, 1);
lean_inc(x_3569);
lean_dec(x_3567);
x_3570 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3570, 0, x_102);
lean_ctor_set(x_3570, 1, x_3460);
x_3571 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3570, x_3, x_4, x_5, x_3569);
return x_3571;
}
else
{
lean_object* x_3572; lean_object* x_3573; lean_object* x_3574; lean_object* x_3575; 
lean_dec(x_3460);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3572 = lean_ctor_get(x_3567, 1);
lean_inc(x_3572);
if (lean_is_exclusive(x_3567)) {
 lean_ctor_release(x_3567, 0);
 lean_ctor_release(x_3567, 1);
 x_3573 = x_3567;
} else {
 lean_dec_ref(x_3567);
 x_3573 = lean_box(0);
}
x_3574 = lean_ctor_get(x_3568, 0);
lean_inc(x_3574);
lean_dec(x_3568);
if (lean_is_scalar(x_3573)) {
 x_3575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3575 = x_3573;
}
lean_ctor_set(x_3575, 0, x_3574);
lean_ctor_set(x_3575, 1, x_3572);
return x_3575;
}
}
else
{
lean_object* x_3576; lean_object* x_3577; lean_object* x_3578; lean_object* x_3579; 
lean_dec(x_3460);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3576 = lean_ctor_get(x_3567, 0);
lean_inc(x_3576);
x_3577 = lean_ctor_get(x_3567, 1);
lean_inc(x_3577);
if (lean_is_exclusive(x_3567)) {
 lean_ctor_release(x_3567, 0);
 lean_ctor_release(x_3567, 1);
 x_3578 = x_3567;
} else {
 lean_dec_ref(x_3567);
 x_3578 = lean_box(0);
}
if (lean_is_scalar(x_3578)) {
 x_3579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3579 = x_3578;
}
lean_ctor_set(x_3579, 0, x_3576);
lean_ctor_set(x_3579, 1, x_3577);
return x_3579;
}
}
}
case 7:
{
lean_object* x_3580; uint8_t x_3581; lean_object* x_3582; lean_object* x_3583; lean_object* x_3584; lean_object* x_3585; lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; lean_object* x_3589; lean_object* x_3590; 
lean_dec(x_3469);
lean_dec(x_3468);
lean_dec(x_3460);
lean_dec(x_3456);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_3474)) {
 lean_ctor_release(x_3474, 0);
 x_3580 = x_3474;
} else {
 lean_dec_ref(x_3474);
 x_3580 = lean_box(0);
}
x_3581 = 1;
x_3582 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3583 = l_Lean_Name_toString(x_102, x_3581, x_3582);
if (lean_is_scalar(x_3580)) {
 x_3584 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3584 = x_3580;
 lean_ctor_set_tag(x_3584, 3);
}
lean_ctor_set(x_3584, 0, x_3583);
x_3585 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3586 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3586, 0, x_3585);
lean_ctor_set(x_3586, 1, x_3584);
x_3587 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3588 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3588, 0, x_3586);
lean_ctor_set(x_3588, 1, x_3587);
x_3589 = l_Lean_MessageData_ofFormat(x_3588);
x_3590 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3589, x_3, x_4, x_5, x_3467);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3590;
}
default: 
{
lean_object* x_3591; 
lean_dec(x_3474);
lean_dec(x_3469);
lean_dec(x_3468);
lean_dec(x_3456);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3460);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3591 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3460, x_3, x_4, x_5, x_3467);
if (lean_obj_tag(x_3591) == 0)
{
lean_object* x_3592; 
x_3592 = lean_ctor_get(x_3591, 0);
lean_inc(x_3592);
if (lean_obj_tag(x_3592) == 0)
{
lean_object* x_3593; lean_object* x_3594; lean_object* x_3595; 
x_3593 = lean_ctor_get(x_3591, 1);
lean_inc(x_3593);
lean_dec(x_3591);
x_3594 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3594, 0, x_102);
lean_ctor_set(x_3594, 1, x_3460);
x_3595 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3594, x_3, x_4, x_5, x_3593);
return x_3595;
}
else
{
lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; lean_object* x_3599; 
lean_dec(x_3460);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3596 = lean_ctor_get(x_3591, 1);
lean_inc(x_3596);
if (lean_is_exclusive(x_3591)) {
 lean_ctor_release(x_3591, 0);
 lean_ctor_release(x_3591, 1);
 x_3597 = x_3591;
} else {
 lean_dec_ref(x_3591);
 x_3597 = lean_box(0);
}
x_3598 = lean_ctor_get(x_3592, 0);
lean_inc(x_3598);
lean_dec(x_3592);
if (lean_is_scalar(x_3597)) {
 x_3599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3599 = x_3597;
}
lean_ctor_set(x_3599, 0, x_3598);
lean_ctor_set(x_3599, 1, x_3596);
return x_3599;
}
}
else
{
lean_object* x_3600; lean_object* x_3601; lean_object* x_3602; lean_object* x_3603; 
lean_dec(x_3460);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3600 = lean_ctor_get(x_3591, 0);
lean_inc(x_3600);
x_3601 = lean_ctor_get(x_3591, 1);
lean_inc(x_3601);
if (lean_is_exclusive(x_3591)) {
 lean_ctor_release(x_3591, 0);
 lean_ctor_release(x_3591, 1);
 x_3602 = x_3591;
} else {
 lean_dec_ref(x_3591);
 x_3602 = lean_box(0);
}
if (lean_is_scalar(x_3602)) {
 x_3603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3603 = x_3602;
}
lean_ctor_set(x_3603, 0, x_3600);
lean_ctor_set(x_3603, 1, x_3601);
return x_3603;
}
}
}
}
}
else
{
lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; lean_object* x_3607; 
lean_dec(x_3460);
lean_dec(x_3456);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3604 = lean_ctor_get(x_3462, 1);
lean_inc(x_3604);
if (lean_is_exclusive(x_3462)) {
 lean_ctor_release(x_3462, 0);
 lean_ctor_release(x_3462, 1);
 x_3605 = x_3462;
} else {
 lean_dec_ref(x_3462);
 x_3605 = lean_box(0);
}
x_3606 = lean_ctor_get(x_3463, 0);
lean_inc(x_3606);
lean_dec(x_3463);
if (lean_is_scalar(x_3605)) {
 x_3607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3607 = x_3605;
}
lean_ctor_set(x_3607, 0, x_3606);
lean_ctor_set(x_3607, 1, x_3604);
return x_3607;
}
}
else
{
lean_object* x_3608; lean_object* x_3609; lean_object* x_3610; lean_object* x_3611; 
lean_dec(x_3460);
lean_dec(x_3456);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3608 = lean_ctor_get(x_3462, 0);
lean_inc(x_3608);
x_3609 = lean_ctor_get(x_3462, 1);
lean_inc(x_3609);
if (lean_is_exclusive(x_3462)) {
 lean_ctor_release(x_3462, 0);
 lean_ctor_release(x_3462, 1);
 x_3610 = x_3462;
} else {
 lean_dec_ref(x_3462);
 x_3610 = lean_box(0);
}
if (lean_is_scalar(x_3610)) {
 x_3611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3611 = x_3610;
}
lean_ctor_set(x_3611, 0, x_3608);
lean_ctor_set(x_3611, 1, x_3609);
return x_3611;
}
}
else
{
lean_object* x_3612; lean_object* x_3613; lean_object* x_3614; lean_object* x_3615; 
lean_dec(x_3456);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3612 = lean_ctor_get(x_3459, 0);
lean_inc(x_3612);
x_3613 = lean_ctor_get(x_3459, 1);
lean_inc(x_3613);
if (lean_is_exclusive(x_3459)) {
 lean_ctor_release(x_3459, 0);
 lean_ctor_release(x_3459, 1);
 x_3614 = x_3459;
} else {
 lean_dec_ref(x_3459);
 x_3614 = lean_box(0);
}
if (lean_is_scalar(x_3614)) {
 x_3615 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3615 = x_3614;
}
lean_ctor_set(x_3615, 0, x_3612);
lean_ctor_set(x_3615, 1, x_3613);
return x_3615;
}
}
}
}
}
default: 
{
uint8_t x_3616; 
lean_dec(x_662);
x_3616 = !lean_is_exclusive(x_7);
if (x_3616 == 0)
{
lean_object* x_3617; lean_object* x_3618; lean_object* x_3619; size_t x_3620; size_t x_3621; lean_object* x_3622; 
x_3617 = lean_ctor_get(x_7, 2);
x_3618 = lean_ctor_get(x_7, 1);
lean_dec(x_3618);
x_3619 = lean_ctor_get(x_7, 0);
lean_dec(x_3619);
x_3620 = lean_array_size(x_3617);
x_3621 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3617);
x_3622 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_3620, x_3621, x_3617, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_3622) == 0)
{
lean_object* x_3623; lean_object* x_3624; lean_object* x_3625; 
x_3623 = lean_ctor_get(x_3622, 0);
lean_inc(x_3623);
x_3624 = lean_ctor_get(x_3622, 1);
lean_inc(x_3624);
lean_dec(x_3622);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3623);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3625 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3623, x_3, x_4, x_5, x_3624);
if (lean_obj_tag(x_3625) == 0)
{
lean_object* x_3626; 
x_3626 = lean_ctor_get(x_3625, 0);
lean_inc(x_3626);
if (lean_obj_tag(x_3626) == 0)
{
lean_object* x_3627; lean_object* x_3628; uint8_t x_3629; 
x_3627 = lean_ctor_get(x_3625, 1);
lean_inc(x_3627);
lean_dec(x_3625);
x_3628 = lean_st_ref_get(x_5, x_3627);
x_3629 = !lean_is_exclusive(x_3628);
if (x_3629 == 0)
{
lean_object* x_3630; lean_object* x_3631; lean_object* x_3632; uint8_t x_3633; lean_object* x_3634; 
x_3630 = lean_ctor_get(x_3628, 0);
x_3631 = lean_ctor_get(x_3628, 1);
x_3632 = lean_ctor_get(x_3630, 0);
lean_inc(x_3632);
lean_dec(x_3630);
x_3633 = 0;
lean_inc(x_102);
lean_inc(x_3632);
x_3634 = l_Lean_Environment_find_x3f(x_3632, x_102, x_3633);
if (lean_obj_tag(x_3634) == 0)
{
lean_object* x_3635; lean_object* x_3636; 
lean_dec(x_3632);
lean_free_object(x_3628);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3635 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_3636 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3635, x_3, x_4, x_5, x_3631);
return x_3636;
}
else
{
lean_object* x_3637; 
x_3637 = lean_ctor_get(x_3634, 0);
lean_inc(x_3637);
lean_dec(x_3634);
switch (lean_obj_tag(x_3637)) {
case 0:
{
uint8_t x_3638; 
lean_dec(x_3632);
lean_free_object(x_7);
lean_dec(x_3617);
x_3638 = !lean_is_exclusive(x_3637);
if (x_3638 == 0)
{
lean_object* x_3639; lean_object* x_3640; uint8_t x_3641; 
x_3639 = lean_ctor_get(x_3637, 0);
lean_dec(x_3639);
x_3640 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_3641 = lean_name_eq(x_102, x_3640);
if (x_3641 == 0)
{
lean_object* x_3642; uint8_t x_3643; 
x_3642 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_3643 = lean_name_eq(x_102, x_3642);
if (x_3643 == 0)
{
lean_object* x_3644; lean_object* x_3645; 
lean_free_object(x_3628);
lean_inc(x_102);
x_3644 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_3631);
x_3645 = lean_ctor_get(x_3644, 0);
lean_inc(x_3645);
if (lean_obj_tag(x_3645) == 0)
{
uint8_t x_3646; 
lean_dec(x_3623);
lean_dec(x_2);
lean_dec(x_1);
x_3646 = !lean_is_exclusive(x_3644);
if (x_3646 == 0)
{
lean_object* x_3647; lean_object* x_3648; uint8_t x_3649; lean_object* x_3650; lean_object* x_3651; lean_object* x_3652; lean_object* x_3653; lean_object* x_3654; lean_object* x_3655; lean_object* x_3656; 
x_3647 = lean_ctor_get(x_3644, 1);
x_3648 = lean_ctor_get(x_3644, 0);
lean_dec(x_3648);
x_3649 = 1;
x_3650 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3651 = l_Lean_Name_toString(x_102, x_3649, x_3650);
lean_ctor_set_tag(x_3637, 3);
lean_ctor_set(x_3637, 0, x_3651);
x_3652 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_3644, 5);
lean_ctor_set(x_3644, 1, x_3637);
lean_ctor_set(x_3644, 0, x_3652);
x_3653 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3654 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3654, 0, x_3644);
lean_ctor_set(x_3654, 1, x_3653);
x_3655 = l_Lean_MessageData_ofFormat(x_3654);
x_3656 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3655, x_3, x_4, x_5, x_3647);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3656;
}
else
{
lean_object* x_3657; uint8_t x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; lean_object* x_3662; lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; lean_object* x_3666; 
x_3657 = lean_ctor_get(x_3644, 1);
lean_inc(x_3657);
lean_dec(x_3644);
x_3658 = 1;
x_3659 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3660 = l_Lean_Name_toString(x_102, x_3658, x_3659);
lean_ctor_set_tag(x_3637, 3);
lean_ctor_set(x_3637, 0, x_3660);
x_3661 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_3662 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3662, 0, x_3661);
lean_ctor_set(x_3662, 1, x_3637);
x_3663 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3664 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3664, 0, x_3662);
lean_ctor_set(x_3664, 1, x_3663);
x_3665 = l_Lean_MessageData_ofFormat(x_3664);
x_3666 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3665, x_3, x_4, x_5, x_3657);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3666;
}
}
else
{
uint8_t x_3667; 
lean_free_object(x_3637);
x_3667 = !lean_is_exclusive(x_3644);
if (x_3667 == 0)
{
lean_object* x_3668; lean_object* x_3669; lean_object* x_3670; lean_object* x_3671; lean_object* x_3672; lean_object* x_3673; uint8_t x_3674; 
x_3668 = lean_ctor_get(x_3644, 1);
x_3669 = lean_ctor_get(x_3644, 0);
lean_dec(x_3669);
x_3670 = lean_ctor_get(x_3645, 0);
lean_inc(x_3670);
lean_dec(x_3645);
x_3671 = lean_array_get_size(x_3623);
x_3672 = l_Lean_IR_Decl_params(x_3670);
lean_dec(x_3670);
x_3673 = lean_array_get_size(x_3672);
lean_dec(x_3672);
x_3674 = lean_nat_dec_lt(x_3671, x_3673);
if (x_3674 == 0)
{
uint8_t x_3675; 
x_3675 = lean_nat_dec_eq(x_3671, x_3673);
if (x_3675 == 0)
{
lean_object* x_3676; lean_object* x_3677; lean_object* x_3678; lean_object* x_3679; 
x_3676 = lean_unsigned_to_nat(0u);
x_3677 = l_Array_extract___rarg(x_3623, x_3676, x_3673);
x_3678 = l_Array_extract___rarg(x_3623, x_3673, x_3671);
lean_dec(x_3671);
lean_dec(x_3623);
lean_ctor_set_tag(x_3644, 6);
lean_ctor_set(x_3644, 1, x_3677);
lean_ctor_set(x_3644, 0, x_102);
x_3679 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3644, x_3678, x_3, x_4, x_5, x_3668);
return x_3679;
}
else
{
lean_object* x_3680; 
lean_dec(x_3673);
lean_dec(x_3671);
lean_ctor_set_tag(x_3644, 6);
lean_ctor_set(x_3644, 1, x_3623);
lean_ctor_set(x_3644, 0, x_102);
x_3680 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3644, x_3, x_4, x_5, x_3668);
return x_3680;
}
}
else
{
lean_object* x_3681; 
lean_dec(x_3673);
lean_dec(x_3671);
lean_ctor_set_tag(x_3644, 7);
lean_ctor_set(x_3644, 1, x_3623);
lean_ctor_set(x_3644, 0, x_102);
x_3681 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3644, x_3, x_4, x_5, x_3668);
return x_3681;
}
}
else
{
lean_object* x_3682; lean_object* x_3683; lean_object* x_3684; lean_object* x_3685; lean_object* x_3686; uint8_t x_3687; 
x_3682 = lean_ctor_get(x_3644, 1);
lean_inc(x_3682);
lean_dec(x_3644);
x_3683 = lean_ctor_get(x_3645, 0);
lean_inc(x_3683);
lean_dec(x_3645);
x_3684 = lean_array_get_size(x_3623);
x_3685 = l_Lean_IR_Decl_params(x_3683);
lean_dec(x_3683);
x_3686 = lean_array_get_size(x_3685);
lean_dec(x_3685);
x_3687 = lean_nat_dec_lt(x_3684, x_3686);
if (x_3687 == 0)
{
uint8_t x_3688; 
x_3688 = lean_nat_dec_eq(x_3684, x_3686);
if (x_3688 == 0)
{
lean_object* x_3689; lean_object* x_3690; lean_object* x_3691; lean_object* x_3692; lean_object* x_3693; 
x_3689 = lean_unsigned_to_nat(0u);
x_3690 = l_Array_extract___rarg(x_3623, x_3689, x_3686);
x_3691 = l_Array_extract___rarg(x_3623, x_3686, x_3684);
lean_dec(x_3684);
lean_dec(x_3623);
x_3692 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3692, 0, x_102);
lean_ctor_set(x_3692, 1, x_3690);
x_3693 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3692, x_3691, x_3, x_4, x_5, x_3682);
return x_3693;
}
else
{
lean_object* x_3694; lean_object* x_3695; 
lean_dec(x_3686);
lean_dec(x_3684);
x_3694 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3694, 0, x_102);
lean_ctor_set(x_3694, 1, x_3623);
x_3695 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3694, x_3, x_4, x_5, x_3682);
return x_3695;
}
}
else
{
lean_object* x_3696; lean_object* x_3697; 
lean_dec(x_3686);
lean_dec(x_3684);
x_3696 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3696, 0, x_102);
lean_ctor_set(x_3696, 1, x_3623);
x_3697 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3696, x_3, x_4, x_5, x_3682);
return x_3697;
}
}
}
}
else
{
lean_object* x_3698; 
lean_free_object(x_3637);
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3698 = lean_box(13);
lean_ctor_set(x_3628, 0, x_3698);
return x_3628;
}
}
else
{
lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; 
lean_free_object(x_3637);
lean_free_object(x_3628);
lean_dec(x_102);
x_3699 = l_Lean_IR_instInhabitedArg;
x_3700 = lean_unsigned_to_nat(2u);
x_3701 = lean_array_get(x_3699, x_3623, x_3700);
lean_dec(x_3623);
if (lean_obj_tag(x_3701) == 0)
{
lean_object* x_3702; lean_object* x_3703; 
x_3702 = lean_ctor_get(x_3701, 0);
lean_inc(x_3702);
lean_dec(x_3701);
x_3703 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3702, x_3, x_4, x_5, x_3631);
return x_3703;
}
else
{
lean_object* x_3704; lean_object* x_3705; 
x_3704 = lean_box(0);
x_3705 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3704, x_3, x_4, x_5, x_3631);
return x_3705;
}
}
}
else
{
lean_object* x_3706; uint8_t x_3707; 
lean_dec(x_3637);
x_3706 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_3707 = lean_name_eq(x_102, x_3706);
if (x_3707 == 0)
{
lean_object* x_3708; uint8_t x_3709; 
x_3708 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_3709 = lean_name_eq(x_102, x_3708);
if (x_3709 == 0)
{
lean_object* x_3710; lean_object* x_3711; 
lean_free_object(x_3628);
lean_inc(x_102);
x_3710 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_3631);
x_3711 = lean_ctor_get(x_3710, 0);
lean_inc(x_3711);
if (lean_obj_tag(x_3711) == 0)
{
lean_object* x_3712; lean_object* x_3713; uint8_t x_3714; lean_object* x_3715; lean_object* x_3716; lean_object* x_3717; lean_object* x_3718; lean_object* x_3719; lean_object* x_3720; lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; 
lean_dec(x_3623);
lean_dec(x_2);
lean_dec(x_1);
x_3712 = lean_ctor_get(x_3710, 1);
lean_inc(x_3712);
if (lean_is_exclusive(x_3710)) {
 lean_ctor_release(x_3710, 0);
 lean_ctor_release(x_3710, 1);
 x_3713 = x_3710;
} else {
 lean_dec_ref(x_3710);
 x_3713 = lean_box(0);
}
x_3714 = 1;
x_3715 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3716 = l_Lean_Name_toString(x_102, x_3714, x_3715);
x_3717 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3717, 0, x_3716);
x_3718 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_3713)) {
 x_3719 = lean_alloc_ctor(5, 2, 0);
} else {
 x_3719 = x_3713;
 lean_ctor_set_tag(x_3719, 5);
}
lean_ctor_set(x_3719, 0, x_3718);
lean_ctor_set(x_3719, 1, x_3717);
x_3720 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3721 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3721, 0, x_3719);
lean_ctor_set(x_3721, 1, x_3720);
x_3722 = l_Lean_MessageData_ofFormat(x_3721);
x_3723 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3722, x_3, x_4, x_5, x_3712);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3723;
}
else
{
lean_object* x_3724; lean_object* x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; lean_object* x_3729; uint8_t x_3730; 
x_3724 = lean_ctor_get(x_3710, 1);
lean_inc(x_3724);
if (lean_is_exclusive(x_3710)) {
 lean_ctor_release(x_3710, 0);
 lean_ctor_release(x_3710, 1);
 x_3725 = x_3710;
} else {
 lean_dec_ref(x_3710);
 x_3725 = lean_box(0);
}
x_3726 = lean_ctor_get(x_3711, 0);
lean_inc(x_3726);
lean_dec(x_3711);
x_3727 = lean_array_get_size(x_3623);
x_3728 = l_Lean_IR_Decl_params(x_3726);
lean_dec(x_3726);
x_3729 = lean_array_get_size(x_3728);
lean_dec(x_3728);
x_3730 = lean_nat_dec_lt(x_3727, x_3729);
if (x_3730 == 0)
{
uint8_t x_3731; 
x_3731 = lean_nat_dec_eq(x_3727, x_3729);
if (x_3731 == 0)
{
lean_object* x_3732; lean_object* x_3733; lean_object* x_3734; lean_object* x_3735; lean_object* x_3736; 
x_3732 = lean_unsigned_to_nat(0u);
x_3733 = l_Array_extract___rarg(x_3623, x_3732, x_3729);
x_3734 = l_Array_extract___rarg(x_3623, x_3729, x_3727);
lean_dec(x_3727);
lean_dec(x_3623);
if (lean_is_scalar(x_3725)) {
 x_3735 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3735 = x_3725;
 lean_ctor_set_tag(x_3735, 6);
}
lean_ctor_set(x_3735, 0, x_102);
lean_ctor_set(x_3735, 1, x_3733);
x_3736 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3735, x_3734, x_3, x_4, x_5, x_3724);
return x_3736;
}
else
{
lean_object* x_3737; lean_object* x_3738; 
lean_dec(x_3729);
lean_dec(x_3727);
if (lean_is_scalar(x_3725)) {
 x_3737 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3737 = x_3725;
 lean_ctor_set_tag(x_3737, 6);
}
lean_ctor_set(x_3737, 0, x_102);
lean_ctor_set(x_3737, 1, x_3623);
x_3738 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3737, x_3, x_4, x_5, x_3724);
return x_3738;
}
}
else
{
lean_object* x_3739; lean_object* x_3740; 
lean_dec(x_3729);
lean_dec(x_3727);
if (lean_is_scalar(x_3725)) {
 x_3739 = lean_alloc_ctor(7, 2, 0);
} else {
 x_3739 = x_3725;
 lean_ctor_set_tag(x_3739, 7);
}
lean_ctor_set(x_3739, 0, x_102);
lean_ctor_set(x_3739, 1, x_3623);
x_3740 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3739, x_3, x_4, x_5, x_3724);
return x_3740;
}
}
}
else
{
lean_object* x_3741; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3741 = lean_box(13);
lean_ctor_set(x_3628, 0, x_3741);
return x_3628;
}
}
else
{
lean_object* x_3742; lean_object* x_3743; lean_object* x_3744; 
lean_free_object(x_3628);
lean_dec(x_102);
x_3742 = l_Lean_IR_instInhabitedArg;
x_3743 = lean_unsigned_to_nat(2u);
x_3744 = lean_array_get(x_3742, x_3623, x_3743);
lean_dec(x_3623);
if (lean_obj_tag(x_3744) == 0)
{
lean_object* x_3745; lean_object* x_3746; 
x_3745 = lean_ctor_get(x_3744, 0);
lean_inc(x_3745);
lean_dec(x_3744);
x_3746 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3745, x_3, x_4, x_5, x_3631);
return x_3746;
}
else
{
lean_object* x_3747; lean_object* x_3748; 
x_3747 = lean_box(0);
x_3748 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3747, x_3, x_4, x_5, x_3631);
return x_3748;
}
}
}
}
case 2:
{
lean_object* x_3749; lean_object* x_3750; 
lean_dec(x_3637);
lean_dec(x_3632);
lean_free_object(x_3628);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3749 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_3750 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3749, x_3, x_4, x_5, x_3631);
return x_3750;
}
case 4:
{
uint8_t x_3751; 
lean_dec(x_3632);
lean_free_object(x_3628);
lean_free_object(x_7);
lean_dec(x_3617);
x_3751 = !lean_is_exclusive(x_3637);
if (x_3751 == 0)
{
lean_object* x_3752; lean_object* x_3753; uint8_t x_3754; 
x_3752 = lean_ctor_get(x_3637, 0);
lean_dec(x_3752);
x_3753 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_3754 = lean_name_eq(x_102, x_3753);
if (x_3754 == 0)
{
uint8_t x_3755; lean_object* x_3756; lean_object* x_3757; lean_object* x_3758; lean_object* x_3759; lean_object* x_3760; lean_object* x_3761; lean_object* x_3762; lean_object* x_3763; 
lean_dec(x_3623);
lean_dec(x_2);
lean_dec(x_1);
x_3755 = 1;
x_3756 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3757 = l_Lean_Name_toString(x_102, x_3755, x_3756);
lean_ctor_set_tag(x_3637, 3);
lean_ctor_set(x_3637, 0, x_3757);
x_3758 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_3759 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3759, 0, x_3758);
lean_ctor_set(x_3759, 1, x_3637);
x_3760 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_3761 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3761, 0, x_3759);
lean_ctor_set(x_3761, 1, x_3760);
x_3762 = l_Lean_MessageData_ofFormat(x_3761);
x_3763 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3762, x_3, x_4, x_5, x_3631);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3763;
}
else
{
lean_object* x_3764; lean_object* x_3765; lean_object* x_3766; 
lean_free_object(x_3637);
lean_dec(x_102);
x_3764 = l_Lean_IR_instInhabitedArg;
x_3765 = lean_unsigned_to_nat(2u);
x_3766 = lean_array_get(x_3764, x_3623, x_3765);
lean_dec(x_3623);
if (lean_obj_tag(x_3766) == 0)
{
lean_object* x_3767; lean_object* x_3768; 
x_3767 = lean_ctor_get(x_3766, 0);
lean_inc(x_3767);
lean_dec(x_3766);
x_3768 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3767, x_3, x_4, x_5, x_3631);
return x_3768;
}
else
{
lean_object* x_3769; lean_object* x_3770; 
x_3769 = lean_box(0);
x_3770 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3769, x_3, x_4, x_5, x_3631);
return x_3770;
}
}
}
else
{
lean_object* x_3771; uint8_t x_3772; 
lean_dec(x_3637);
x_3771 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_3772 = lean_name_eq(x_102, x_3771);
if (x_3772 == 0)
{
uint8_t x_3773; lean_object* x_3774; lean_object* x_3775; lean_object* x_3776; lean_object* x_3777; lean_object* x_3778; lean_object* x_3779; lean_object* x_3780; lean_object* x_3781; lean_object* x_3782; 
lean_dec(x_3623);
lean_dec(x_2);
lean_dec(x_1);
x_3773 = 1;
x_3774 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3775 = l_Lean_Name_toString(x_102, x_3773, x_3774);
x_3776 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3776, 0, x_3775);
x_3777 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_3778 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3778, 0, x_3777);
lean_ctor_set(x_3778, 1, x_3776);
x_3779 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_3780 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3780, 0, x_3778);
lean_ctor_set(x_3780, 1, x_3779);
x_3781 = l_Lean_MessageData_ofFormat(x_3780);
x_3782 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3781, x_3, x_4, x_5, x_3631);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3782;
}
else
{
lean_object* x_3783; lean_object* x_3784; lean_object* x_3785; 
lean_dec(x_102);
x_3783 = l_Lean_IR_instInhabitedArg;
x_3784 = lean_unsigned_to_nat(2u);
x_3785 = lean_array_get(x_3783, x_3623, x_3784);
lean_dec(x_3623);
if (lean_obj_tag(x_3785) == 0)
{
lean_object* x_3786; lean_object* x_3787; 
x_3786 = lean_ctor_get(x_3785, 0);
lean_inc(x_3786);
lean_dec(x_3785);
x_3787 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3786, x_3, x_4, x_5, x_3631);
return x_3787;
}
else
{
lean_object* x_3788; lean_object* x_3789; 
x_3788 = lean_box(0);
x_3789 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3788, x_3, x_4, x_5, x_3631);
return x_3789;
}
}
}
}
case 5:
{
lean_object* x_3790; lean_object* x_3791; 
lean_dec(x_3637);
lean_dec(x_3632);
lean_free_object(x_3628);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3790 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_3791 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3790, x_3, x_4, x_5, x_3631);
return x_3791;
}
case 6:
{
lean_object* x_3792; uint8_t x_3793; 
lean_free_object(x_3628);
x_3792 = lean_ctor_get(x_3637, 0);
lean_inc(x_3792);
lean_dec(x_3637);
lean_inc(x_102);
x_3793 = l_Lean_isExtern(x_3632, x_102);
if (x_3793 == 0)
{
lean_object* x_3794; 
lean_dec(x_3623);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3794 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_3631);
if (lean_obj_tag(x_3794) == 0)
{
lean_object* x_3795; lean_object* x_3796; lean_object* x_3797; lean_object* x_3798; lean_object* x_3799; lean_object* x_3800; lean_object* x_3801; lean_object* x_3802; lean_object* x_3803; lean_object* x_3804; lean_object* x_3805; lean_object* x_3806; lean_object* x_3807; lean_object* x_3808; lean_object* x_3809; 
x_3795 = lean_ctor_get(x_3794, 0);
lean_inc(x_3795);
x_3796 = lean_ctor_get(x_3794, 1);
lean_inc(x_3796);
lean_dec(x_3794);
x_3797 = lean_ctor_get(x_3795, 0);
lean_inc(x_3797);
x_3798 = lean_ctor_get(x_3795, 1);
lean_inc(x_3798);
lean_dec(x_3795);
x_3799 = lean_ctor_get(x_3792, 3);
lean_inc(x_3799);
lean_dec(x_3792);
x_3800 = lean_array_get_size(x_3617);
x_3801 = l_Array_extract___rarg(x_3617, x_3799, x_3800);
lean_dec(x_3800);
lean_dec(x_3617);
x_3802 = lean_array_get_size(x_3798);
x_3803 = lean_unsigned_to_nat(0u);
x_3804 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_3804);
lean_ctor_set(x_7, 1, x_3802);
lean_ctor_set(x_7, 0, x_3803);
x_3805 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_3806 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8(x_3798, x_3801, x_7, x_7, x_3805, x_3803, lean_box(0), lean_box(0), x_3, x_4, x_5, x_3796);
lean_dec(x_7);
x_3807 = lean_ctor_get(x_3806, 0);
lean_inc(x_3807);
x_3808 = lean_ctor_get(x_3806, 1);
lean_inc(x_3808);
lean_dec(x_3806);
x_3809 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_3797, x_3798, x_3801, x_3807, x_3, x_4, x_5, x_3808);
lean_dec(x_3801);
lean_dec(x_3798);
return x_3809;
}
else
{
uint8_t x_3810; 
lean_dec(x_3792);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3810 = !lean_is_exclusive(x_3794);
if (x_3810 == 0)
{
return x_3794;
}
else
{
lean_object* x_3811; lean_object* x_3812; lean_object* x_3813; 
x_3811 = lean_ctor_get(x_3794, 0);
x_3812 = lean_ctor_get(x_3794, 1);
lean_inc(x_3812);
lean_inc(x_3811);
lean_dec(x_3794);
x_3813 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3813, 0, x_3811);
lean_ctor_set(x_3813, 1, x_3812);
return x_3813;
}
}
}
else
{
lean_object* x_3814; 
lean_dec(x_3792);
lean_free_object(x_7);
lean_dec(x_3617);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3623);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3814 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3623, x_3, x_4, x_5, x_3631);
if (lean_obj_tag(x_3814) == 0)
{
lean_object* x_3815; 
x_3815 = lean_ctor_get(x_3814, 0);
lean_inc(x_3815);
if (lean_obj_tag(x_3815) == 0)
{
lean_object* x_3816; lean_object* x_3817; lean_object* x_3818; 
x_3816 = lean_ctor_get(x_3814, 1);
lean_inc(x_3816);
lean_dec(x_3814);
x_3817 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3817, 0, x_102);
lean_ctor_set(x_3817, 1, x_3623);
x_3818 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3817, x_3, x_4, x_5, x_3816);
return x_3818;
}
else
{
uint8_t x_3819; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3819 = !lean_is_exclusive(x_3814);
if (x_3819 == 0)
{
lean_object* x_3820; lean_object* x_3821; 
x_3820 = lean_ctor_get(x_3814, 0);
lean_dec(x_3820);
x_3821 = lean_ctor_get(x_3815, 0);
lean_inc(x_3821);
lean_dec(x_3815);
lean_ctor_set(x_3814, 0, x_3821);
return x_3814;
}
else
{
lean_object* x_3822; lean_object* x_3823; lean_object* x_3824; 
x_3822 = lean_ctor_get(x_3814, 1);
lean_inc(x_3822);
lean_dec(x_3814);
x_3823 = lean_ctor_get(x_3815, 0);
lean_inc(x_3823);
lean_dec(x_3815);
x_3824 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3824, 0, x_3823);
lean_ctor_set(x_3824, 1, x_3822);
return x_3824;
}
}
}
else
{
uint8_t x_3825; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3825 = !lean_is_exclusive(x_3814);
if (x_3825 == 0)
{
return x_3814;
}
else
{
lean_object* x_3826; lean_object* x_3827; lean_object* x_3828; 
x_3826 = lean_ctor_get(x_3814, 0);
x_3827 = lean_ctor_get(x_3814, 1);
lean_inc(x_3827);
lean_inc(x_3826);
lean_dec(x_3814);
x_3828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3828, 0, x_3826);
lean_ctor_set(x_3828, 1, x_3827);
return x_3828;
}
}
}
}
case 7:
{
uint8_t x_3829; 
lean_dec(x_3632);
lean_free_object(x_3628);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_2);
lean_dec(x_1);
x_3829 = !lean_is_exclusive(x_3637);
if (x_3829 == 0)
{
lean_object* x_3830; uint8_t x_3831; lean_object* x_3832; lean_object* x_3833; lean_object* x_3834; lean_object* x_3835; lean_object* x_3836; lean_object* x_3837; lean_object* x_3838; lean_object* x_3839; 
x_3830 = lean_ctor_get(x_3637, 0);
lean_dec(x_3830);
x_3831 = 1;
x_3832 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3833 = l_Lean_Name_toString(x_102, x_3831, x_3832);
lean_ctor_set_tag(x_3637, 3);
lean_ctor_set(x_3637, 0, x_3833);
x_3834 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3835 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3835, 0, x_3834);
lean_ctor_set(x_3835, 1, x_3637);
x_3836 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3837 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3837, 0, x_3835);
lean_ctor_set(x_3837, 1, x_3836);
x_3838 = l_Lean_MessageData_ofFormat(x_3837);
x_3839 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3838, x_3, x_4, x_5, x_3631);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3839;
}
else
{
uint8_t x_3840; lean_object* x_3841; lean_object* x_3842; lean_object* x_3843; lean_object* x_3844; lean_object* x_3845; lean_object* x_3846; lean_object* x_3847; lean_object* x_3848; lean_object* x_3849; 
lean_dec(x_3637);
x_3840 = 1;
x_3841 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3842 = l_Lean_Name_toString(x_102, x_3840, x_3841);
x_3843 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3843, 0, x_3842);
x_3844 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3845 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3845, 0, x_3844);
lean_ctor_set(x_3845, 1, x_3843);
x_3846 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3847 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3847, 0, x_3845);
lean_ctor_set(x_3847, 1, x_3846);
x_3848 = l_Lean_MessageData_ofFormat(x_3847);
x_3849 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3848, x_3, x_4, x_5, x_3631);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3849;
}
}
default: 
{
lean_object* x_3850; 
lean_dec(x_3637);
lean_dec(x_3632);
lean_free_object(x_3628);
lean_free_object(x_7);
lean_dec(x_3617);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3623);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3850 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3623, x_3, x_4, x_5, x_3631);
if (lean_obj_tag(x_3850) == 0)
{
lean_object* x_3851; 
x_3851 = lean_ctor_get(x_3850, 0);
lean_inc(x_3851);
if (lean_obj_tag(x_3851) == 0)
{
lean_object* x_3852; lean_object* x_3853; lean_object* x_3854; 
x_3852 = lean_ctor_get(x_3850, 1);
lean_inc(x_3852);
lean_dec(x_3850);
x_3853 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3853, 0, x_102);
lean_ctor_set(x_3853, 1, x_3623);
x_3854 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3853, x_3, x_4, x_5, x_3852);
return x_3854;
}
else
{
uint8_t x_3855; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3855 = !lean_is_exclusive(x_3850);
if (x_3855 == 0)
{
lean_object* x_3856; lean_object* x_3857; 
x_3856 = lean_ctor_get(x_3850, 0);
lean_dec(x_3856);
x_3857 = lean_ctor_get(x_3851, 0);
lean_inc(x_3857);
lean_dec(x_3851);
lean_ctor_set(x_3850, 0, x_3857);
return x_3850;
}
else
{
lean_object* x_3858; lean_object* x_3859; lean_object* x_3860; 
x_3858 = lean_ctor_get(x_3850, 1);
lean_inc(x_3858);
lean_dec(x_3850);
x_3859 = lean_ctor_get(x_3851, 0);
lean_inc(x_3859);
lean_dec(x_3851);
x_3860 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3860, 0, x_3859);
lean_ctor_set(x_3860, 1, x_3858);
return x_3860;
}
}
}
else
{
uint8_t x_3861; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3861 = !lean_is_exclusive(x_3850);
if (x_3861 == 0)
{
return x_3850;
}
else
{
lean_object* x_3862; lean_object* x_3863; lean_object* x_3864; 
x_3862 = lean_ctor_get(x_3850, 0);
x_3863 = lean_ctor_get(x_3850, 1);
lean_inc(x_3863);
lean_inc(x_3862);
lean_dec(x_3850);
x_3864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3864, 0, x_3862);
lean_ctor_set(x_3864, 1, x_3863);
return x_3864;
}
}
}
}
}
}
else
{
lean_object* x_3865; lean_object* x_3866; lean_object* x_3867; uint8_t x_3868; lean_object* x_3869; 
x_3865 = lean_ctor_get(x_3628, 0);
x_3866 = lean_ctor_get(x_3628, 1);
lean_inc(x_3866);
lean_inc(x_3865);
lean_dec(x_3628);
x_3867 = lean_ctor_get(x_3865, 0);
lean_inc(x_3867);
lean_dec(x_3865);
x_3868 = 0;
lean_inc(x_102);
lean_inc(x_3867);
x_3869 = l_Lean_Environment_find_x3f(x_3867, x_102, x_3868);
if (lean_obj_tag(x_3869) == 0)
{
lean_object* x_3870; lean_object* x_3871; 
lean_dec(x_3867);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3870 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_3871 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3870, x_3, x_4, x_5, x_3866);
return x_3871;
}
else
{
lean_object* x_3872; 
x_3872 = lean_ctor_get(x_3869, 0);
lean_inc(x_3872);
lean_dec(x_3869);
switch (lean_obj_tag(x_3872)) {
case 0:
{
lean_object* x_3873; lean_object* x_3874; uint8_t x_3875; 
lean_dec(x_3867);
lean_free_object(x_7);
lean_dec(x_3617);
if (lean_is_exclusive(x_3872)) {
 lean_ctor_release(x_3872, 0);
 x_3873 = x_3872;
} else {
 lean_dec_ref(x_3872);
 x_3873 = lean_box(0);
}
x_3874 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_3875 = lean_name_eq(x_102, x_3874);
if (x_3875 == 0)
{
lean_object* x_3876; uint8_t x_3877; 
x_3876 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_3877 = lean_name_eq(x_102, x_3876);
if (x_3877 == 0)
{
lean_object* x_3878; lean_object* x_3879; 
lean_inc(x_102);
x_3878 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_3866);
x_3879 = lean_ctor_get(x_3878, 0);
lean_inc(x_3879);
if (lean_obj_tag(x_3879) == 0)
{
lean_object* x_3880; lean_object* x_3881; uint8_t x_3882; lean_object* x_3883; lean_object* x_3884; lean_object* x_3885; lean_object* x_3886; lean_object* x_3887; lean_object* x_3888; lean_object* x_3889; lean_object* x_3890; lean_object* x_3891; 
lean_dec(x_3623);
lean_dec(x_2);
lean_dec(x_1);
x_3880 = lean_ctor_get(x_3878, 1);
lean_inc(x_3880);
if (lean_is_exclusive(x_3878)) {
 lean_ctor_release(x_3878, 0);
 lean_ctor_release(x_3878, 1);
 x_3881 = x_3878;
} else {
 lean_dec_ref(x_3878);
 x_3881 = lean_box(0);
}
x_3882 = 1;
x_3883 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3884 = l_Lean_Name_toString(x_102, x_3882, x_3883);
if (lean_is_scalar(x_3873)) {
 x_3885 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3885 = x_3873;
 lean_ctor_set_tag(x_3885, 3);
}
lean_ctor_set(x_3885, 0, x_3884);
x_3886 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_3881)) {
 x_3887 = lean_alloc_ctor(5, 2, 0);
} else {
 x_3887 = x_3881;
 lean_ctor_set_tag(x_3887, 5);
}
lean_ctor_set(x_3887, 0, x_3886);
lean_ctor_set(x_3887, 1, x_3885);
x_3888 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_3889 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3889, 0, x_3887);
lean_ctor_set(x_3889, 1, x_3888);
x_3890 = l_Lean_MessageData_ofFormat(x_3889);
x_3891 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3890, x_3, x_4, x_5, x_3880);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3891;
}
else
{
lean_object* x_3892; lean_object* x_3893; lean_object* x_3894; lean_object* x_3895; lean_object* x_3896; lean_object* x_3897; uint8_t x_3898; 
lean_dec(x_3873);
x_3892 = lean_ctor_get(x_3878, 1);
lean_inc(x_3892);
if (lean_is_exclusive(x_3878)) {
 lean_ctor_release(x_3878, 0);
 lean_ctor_release(x_3878, 1);
 x_3893 = x_3878;
} else {
 lean_dec_ref(x_3878);
 x_3893 = lean_box(0);
}
x_3894 = lean_ctor_get(x_3879, 0);
lean_inc(x_3894);
lean_dec(x_3879);
x_3895 = lean_array_get_size(x_3623);
x_3896 = l_Lean_IR_Decl_params(x_3894);
lean_dec(x_3894);
x_3897 = lean_array_get_size(x_3896);
lean_dec(x_3896);
x_3898 = lean_nat_dec_lt(x_3895, x_3897);
if (x_3898 == 0)
{
uint8_t x_3899; 
x_3899 = lean_nat_dec_eq(x_3895, x_3897);
if (x_3899 == 0)
{
lean_object* x_3900; lean_object* x_3901; lean_object* x_3902; lean_object* x_3903; lean_object* x_3904; 
x_3900 = lean_unsigned_to_nat(0u);
x_3901 = l_Array_extract___rarg(x_3623, x_3900, x_3897);
x_3902 = l_Array_extract___rarg(x_3623, x_3897, x_3895);
lean_dec(x_3895);
lean_dec(x_3623);
if (lean_is_scalar(x_3893)) {
 x_3903 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3903 = x_3893;
 lean_ctor_set_tag(x_3903, 6);
}
lean_ctor_set(x_3903, 0, x_102);
lean_ctor_set(x_3903, 1, x_3901);
x_3904 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_3903, x_3902, x_3, x_4, x_5, x_3892);
return x_3904;
}
else
{
lean_object* x_3905; lean_object* x_3906; 
lean_dec(x_3897);
lean_dec(x_3895);
if (lean_is_scalar(x_3893)) {
 x_3905 = lean_alloc_ctor(6, 2, 0);
} else {
 x_3905 = x_3893;
 lean_ctor_set_tag(x_3905, 6);
}
lean_ctor_set(x_3905, 0, x_102);
lean_ctor_set(x_3905, 1, x_3623);
x_3906 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3905, x_3, x_4, x_5, x_3892);
return x_3906;
}
}
else
{
lean_object* x_3907; lean_object* x_3908; 
lean_dec(x_3897);
lean_dec(x_3895);
if (lean_is_scalar(x_3893)) {
 x_3907 = lean_alloc_ctor(7, 2, 0);
} else {
 x_3907 = x_3893;
 lean_ctor_set_tag(x_3907, 7);
}
lean_ctor_set(x_3907, 0, x_102);
lean_ctor_set(x_3907, 1, x_3623);
x_3908 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3907, x_3, x_4, x_5, x_3892);
return x_3908;
}
}
}
else
{
lean_object* x_3909; lean_object* x_3910; 
lean_dec(x_3873);
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3909 = lean_box(13);
x_3910 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3910, 0, x_3909);
lean_ctor_set(x_3910, 1, x_3866);
return x_3910;
}
}
else
{
lean_object* x_3911; lean_object* x_3912; lean_object* x_3913; 
lean_dec(x_3873);
lean_dec(x_102);
x_3911 = l_Lean_IR_instInhabitedArg;
x_3912 = lean_unsigned_to_nat(2u);
x_3913 = lean_array_get(x_3911, x_3623, x_3912);
lean_dec(x_3623);
if (lean_obj_tag(x_3913) == 0)
{
lean_object* x_3914; lean_object* x_3915; 
x_3914 = lean_ctor_get(x_3913, 0);
lean_inc(x_3914);
lean_dec(x_3913);
x_3915 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3914, x_3, x_4, x_5, x_3866);
return x_3915;
}
else
{
lean_object* x_3916; lean_object* x_3917; 
x_3916 = lean_box(0);
x_3917 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3916, x_3, x_4, x_5, x_3866);
return x_3917;
}
}
}
case 2:
{
lean_object* x_3918; lean_object* x_3919; 
lean_dec(x_3872);
lean_dec(x_3867);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3918 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_3919 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3918, x_3, x_4, x_5, x_3866);
return x_3919;
}
case 4:
{
lean_object* x_3920; lean_object* x_3921; uint8_t x_3922; 
lean_dec(x_3867);
lean_free_object(x_7);
lean_dec(x_3617);
if (lean_is_exclusive(x_3872)) {
 lean_ctor_release(x_3872, 0);
 x_3920 = x_3872;
} else {
 lean_dec_ref(x_3872);
 x_3920 = lean_box(0);
}
x_3921 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_3922 = lean_name_eq(x_102, x_3921);
if (x_3922 == 0)
{
uint8_t x_3923; lean_object* x_3924; lean_object* x_3925; lean_object* x_3926; lean_object* x_3927; lean_object* x_3928; lean_object* x_3929; lean_object* x_3930; lean_object* x_3931; lean_object* x_3932; 
lean_dec(x_3623);
lean_dec(x_2);
lean_dec(x_1);
x_3923 = 1;
x_3924 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3925 = l_Lean_Name_toString(x_102, x_3923, x_3924);
if (lean_is_scalar(x_3920)) {
 x_3926 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3926 = x_3920;
 lean_ctor_set_tag(x_3926, 3);
}
lean_ctor_set(x_3926, 0, x_3925);
x_3927 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_3928 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3928, 0, x_3927);
lean_ctor_set(x_3928, 1, x_3926);
x_3929 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_3930 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3930, 0, x_3928);
lean_ctor_set(x_3930, 1, x_3929);
x_3931 = l_Lean_MessageData_ofFormat(x_3930);
x_3932 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3931, x_3, x_4, x_5, x_3866);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3932;
}
else
{
lean_object* x_3933; lean_object* x_3934; lean_object* x_3935; 
lean_dec(x_3920);
lean_dec(x_102);
x_3933 = l_Lean_IR_instInhabitedArg;
x_3934 = lean_unsigned_to_nat(2u);
x_3935 = lean_array_get(x_3933, x_3623, x_3934);
lean_dec(x_3623);
if (lean_obj_tag(x_3935) == 0)
{
lean_object* x_3936; lean_object* x_3937; 
x_3936 = lean_ctor_get(x_3935, 0);
lean_inc(x_3936);
lean_dec(x_3935);
x_3937 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3936, x_3, x_4, x_5, x_3866);
return x_3937;
}
else
{
lean_object* x_3938; lean_object* x_3939; 
x_3938 = lean_box(0);
x_3939 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3938, x_3, x_4, x_5, x_3866);
return x_3939;
}
}
}
case 5:
{
lean_object* x_3940; lean_object* x_3941; 
lean_dec(x_3872);
lean_dec(x_3867);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_3940 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_3941 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_3940, x_3, x_4, x_5, x_3866);
return x_3941;
}
case 6:
{
lean_object* x_3942; uint8_t x_3943; 
x_3942 = lean_ctor_get(x_3872, 0);
lean_inc(x_3942);
lean_dec(x_3872);
lean_inc(x_102);
x_3943 = l_Lean_isExtern(x_3867, x_102);
if (x_3943 == 0)
{
lean_object* x_3944; 
lean_dec(x_3623);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3944 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_3866);
if (lean_obj_tag(x_3944) == 0)
{
lean_object* x_3945; lean_object* x_3946; lean_object* x_3947; lean_object* x_3948; lean_object* x_3949; lean_object* x_3950; lean_object* x_3951; lean_object* x_3952; lean_object* x_3953; lean_object* x_3954; lean_object* x_3955; lean_object* x_3956; lean_object* x_3957; lean_object* x_3958; lean_object* x_3959; 
x_3945 = lean_ctor_get(x_3944, 0);
lean_inc(x_3945);
x_3946 = lean_ctor_get(x_3944, 1);
lean_inc(x_3946);
lean_dec(x_3944);
x_3947 = lean_ctor_get(x_3945, 0);
lean_inc(x_3947);
x_3948 = lean_ctor_get(x_3945, 1);
lean_inc(x_3948);
lean_dec(x_3945);
x_3949 = lean_ctor_get(x_3942, 3);
lean_inc(x_3949);
lean_dec(x_3942);
x_3950 = lean_array_get_size(x_3617);
x_3951 = l_Array_extract___rarg(x_3617, x_3949, x_3950);
lean_dec(x_3950);
lean_dec(x_3617);
x_3952 = lean_array_get_size(x_3948);
x_3953 = lean_unsigned_to_nat(0u);
x_3954 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_3954);
lean_ctor_set(x_7, 1, x_3952);
lean_ctor_set(x_7, 0, x_3953);
x_3955 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_3956 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8(x_3948, x_3951, x_7, x_7, x_3955, x_3953, lean_box(0), lean_box(0), x_3, x_4, x_5, x_3946);
lean_dec(x_7);
x_3957 = lean_ctor_get(x_3956, 0);
lean_inc(x_3957);
x_3958 = lean_ctor_get(x_3956, 1);
lean_inc(x_3958);
lean_dec(x_3956);
x_3959 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_3947, x_3948, x_3951, x_3957, x_3, x_4, x_5, x_3958);
lean_dec(x_3951);
lean_dec(x_3948);
return x_3959;
}
else
{
lean_object* x_3960; lean_object* x_3961; lean_object* x_3962; lean_object* x_3963; 
lean_dec(x_3942);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3960 = lean_ctor_get(x_3944, 0);
lean_inc(x_3960);
x_3961 = lean_ctor_get(x_3944, 1);
lean_inc(x_3961);
if (lean_is_exclusive(x_3944)) {
 lean_ctor_release(x_3944, 0);
 lean_ctor_release(x_3944, 1);
 x_3962 = x_3944;
} else {
 lean_dec_ref(x_3944);
 x_3962 = lean_box(0);
}
if (lean_is_scalar(x_3962)) {
 x_3963 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3963 = x_3962;
}
lean_ctor_set(x_3963, 0, x_3960);
lean_ctor_set(x_3963, 1, x_3961);
return x_3963;
}
}
else
{
lean_object* x_3964; 
lean_dec(x_3942);
lean_free_object(x_7);
lean_dec(x_3617);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3623);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3964 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3623, x_3, x_4, x_5, x_3866);
if (lean_obj_tag(x_3964) == 0)
{
lean_object* x_3965; 
x_3965 = lean_ctor_get(x_3964, 0);
lean_inc(x_3965);
if (lean_obj_tag(x_3965) == 0)
{
lean_object* x_3966; lean_object* x_3967; lean_object* x_3968; 
x_3966 = lean_ctor_get(x_3964, 1);
lean_inc(x_3966);
lean_dec(x_3964);
x_3967 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3967, 0, x_102);
lean_ctor_set(x_3967, 1, x_3623);
x_3968 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3967, x_3, x_4, x_5, x_3966);
return x_3968;
}
else
{
lean_object* x_3969; lean_object* x_3970; lean_object* x_3971; lean_object* x_3972; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3969 = lean_ctor_get(x_3964, 1);
lean_inc(x_3969);
if (lean_is_exclusive(x_3964)) {
 lean_ctor_release(x_3964, 0);
 lean_ctor_release(x_3964, 1);
 x_3970 = x_3964;
} else {
 lean_dec_ref(x_3964);
 x_3970 = lean_box(0);
}
x_3971 = lean_ctor_get(x_3965, 0);
lean_inc(x_3971);
lean_dec(x_3965);
if (lean_is_scalar(x_3970)) {
 x_3972 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3972 = x_3970;
}
lean_ctor_set(x_3972, 0, x_3971);
lean_ctor_set(x_3972, 1, x_3969);
return x_3972;
}
}
else
{
lean_object* x_3973; lean_object* x_3974; lean_object* x_3975; lean_object* x_3976; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3973 = lean_ctor_get(x_3964, 0);
lean_inc(x_3973);
x_3974 = lean_ctor_get(x_3964, 1);
lean_inc(x_3974);
if (lean_is_exclusive(x_3964)) {
 lean_ctor_release(x_3964, 0);
 lean_ctor_release(x_3964, 1);
 x_3975 = x_3964;
} else {
 lean_dec_ref(x_3964);
 x_3975 = lean_box(0);
}
if (lean_is_scalar(x_3975)) {
 x_3976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3976 = x_3975;
}
lean_ctor_set(x_3976, 0, x_3973);
lean_ctor_set(x_3976, 1, x_3974);
return x_3976;
}
}
}
case 7:
{
lean_object* x_3977; uint8_t x_3978; lean_object* x_3979; lean_object* x_3980; lean_object* x_3981; lean_object* x_3982; lean_object* x_3983; lean_object* x_3984; lean_object* x_3985; lean_object* x_3986; lean_object* x_3987; 
lean_dec(x_3867);
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_3872)) {
 lean_ctor_release(x_3872, 0);
 x_3977 = x_3872;
} else {
 lean_dec_ref(x_3872);
 x_3977 = lean_box(0);
}
x_3978 = 1;
x_3979 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_3980 = l_Lean_Name_toString(x_102, x_3978, x_3979);
if (lean_is_scalar(x_3977)) {
 x_3981 = lean_alloc_ctor(3, 1, 0);
} else {
 x_3981 = x_3977;
 lean_ctor_set_tag(x_3981, 3);
}
lean_ctor_set(x_3981, 0, x_3980);
x_3982 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_3983 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3983, 0, x_3982);
lean_ctor_set(x_3983, 1, x_3981);
x_3984 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_3985 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3985, 0, x_3983);
lean_ctor_set(x_3985, 1, x_3984);
x_3986 = l_Lean_MessageData_ofFormat(x_3985);
x_3987 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_3986, x_3, x_4, x_5, x_3866);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_3987;
}
default: 
{
lean_object* x_3988; 
lean_dec(x_3872);
lean_dec(x_3867);
lean_free_object(x_7);
lean_dec(x_3617);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3623);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_3988 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_3623, x_3, x_4, x_5, x_3866);
if (lean_obj_tag(x_3988) == 0)
{
lean_object* x_3989; 
x_3989 = lean_ctor_get(x_3988, 0);
lean_inc(x_3989);
if (lean_obj_tag(x_3989) == 0)
{
lean_object* x_3990; lean_object* x_3991; lean_object* x_3992; 
x_3990 = lean_ctor_get(x_3988, 1);
lean_inc(x_3990);
lean_dec(x_3988);
x_3991 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3991, 0, x_102);
lean_ctor_set(x_3991, 1, x_3623);
x_3992 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_3991, x_3, x_4, x_5, x_3990);
return x_3992;
}
else
{
lean_object* x_3993; lean_object* x_3994; lean_object* x_3995; lean_object* x_3996; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3993 = lean_ctor_get(x_3988, 1);
lean_inc(x_3993);
if (lean_is_exclusive(x_3988)) {
 lean_ctor_release(x_3988, 0);
 lean_ctor_release(x_3988, 1);
 x_3994 = x_3988;
} else {
 lean_dec_ref(x_3988);
 x_3994 = lean_box(0);
}
x_3995 = lean_ctor_get(x_3989, 0);
lean_inc(x_3995);
lean_dec(x_3989);
if (lean_is_scalar(x_3994)) {
 x_3996 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3996 = x_3994;
}
lean_ctor_set(x_3996, 0, x_3995);
lean_ctor_set(x_3996, 1, x_3993);
return x_3996;
}
}
else
{
lean_object* x_3997; lean_object* x_3998; lean_object* x_3999; lean_object* x_4000; 
lean_dec(x_3623);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3997 = lean_ctor_get(x_3988, 0);
lean_inc(x_3997);
x_3998 = lean_ctor_get(x_3988, 1);
lean_inc(x_3998);
if (lean_is_exclusive(x_3988)) {
 lean_ctor_release(x_3988, 0);
 lean_ctor_release(x_3988, 1);
 x_3999 = x_3988;
} else {
 lean_dec_ref(x_3988);
 x_3999 = lean_box(0);
}
if (lean_is_scalar(x_3999)) {
 x_4000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4000 = x_3999;
}
lean_ctor_set(x_4000, 0, x_3997);
lean_ctor_set(x_4000, 1, x_3998);
return x_4000;
}
}
}
}
}
}
else
{
uint8_t x_4001; 
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4001 = !lean_is_exclusive(x_3625);
if (x_4001 == 0)
{
lean_object* x_4002; lean_object* x_4003; 
x_4002 = lean_ctor_get(x_3625, 0);
lean_dec(x_4002);
x_4003 = lean_ctor_get(x_3626, 0);
lean_inc(x_4003);
lean_dec(x_3626);
lean_ctor_set(x_3625, 0, x_4003);
return x_3625;
}
else
{
lean_object* x_4004; lean_object* x_4005; lean_object* x_4006; 
x_4004 = lean_ctor_get(x_3625, 1);
lean_inc(x_4004);
lean_dec(x_3625);
x_4005 = lean_ctor_get(x_3626, 0);
lean_inc(x_4005);
lean_dec(x_3626);
x_4006 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4006, 0, x_4005);
lean_ctor_set(x_4006, 1, x_4004);
return x_4006;
}
}
}
else
{
uint8_t x_4007; 
lean_dec(x_3623);
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4007 = !lean_is_exclusive(x_3625);
if (x_4007 == 0)
{
return x_3625;
}
else
{
lean_object* x_4008; lean_object* x_4009; lean_object* x_4010; 
x_4008 = lean_ctor_get(x_3625, 0);
x_4009 = lean_ctor_get(x_3625, 1);
lean_inc(x_4009);
lean_inc(x_4008);
lean_dec(x_3625);
x_4010 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4010, 0, x_4008);
lean_ctor_set(x_4010, 1, x_4009);
return x_4010;
}
}
}
else
{
uint8_t x_4011; 
lean_free_object(x_7);
lean_dec(x_3617);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4011 = !lean_is_exclusive(x_3622);
if (x_4011 == 0)
{
return x_3622;
}
else
{
lean_object* x_4012; lean_object* x_4013; lean_object* x_4014; 
x_4012 = lean_ctor_get(x_3622, 0);
x_4013 = lean_ctor_get(x_3622, 1);
lean_inc(x_4013);
lean_inc(x_4012);
lean_dec(x_3622);
x_4014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4014, 0, x_4012);
lean_ctor_set(x_4014, 1, x_4013);
return x_4014;
}
}
}
else
{
lean_object* x_4015; size_t x_4016; size_t x_4017; lean_object* x_4018; 
x_4015 = lean_ctor_get(x_7, 2);
lean_inc(x_4015);
lean_dec(x_7);
x_4016 = lean_array_size(x_4015);
x_4017 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4015);
x_4018 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_4016, x_4017, x_4015, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_4018) == 0)
{
lean_object* x_4019; lean_object* x_4020; lean_object* x_4021; 
x_4019 = lean_ctor_get(x_4018, 0);
lean_inc(x_4019);
x_4020 = lean_ctor_get(x_4018, 1);
lean_inc(x_4020);
lean_dec(x_4018);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4019);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4021 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4019, x_3, x_4, x_5, x_4020);
if (lean_obj_tag(x_4021) == 0)
{
lean_object* x_4022; 
x_4022 = lean_ctor_get(x_4021, 0);
lean_inc(x_4022);
if (lean_obj_tag(x_4022) == 0)
{
lean_object* x_4023; lean_object* x_4024; lean_object* x_4025; lean_object* x_4026; lean_object* x_4027; lean_object* x_4028; uint8_t x_4029; lean_object* x_4030; 
x_4023 = lean_ctor_get(x_4021, 1);
lean_inc(x_4023);
lean_dec(x_4021);
x_4024 = lean_st_ref_get(x_5, x_4023);
x_4025 = lean_ctor_get(x_4024, 0);
lean_inc(x_4025);
x_4026 = lean_ctor_get(x_4024, 1);
lean_inc(x_4026);
if (lean_is_exclusive(x_4024)) {
 lean_ctor_release(x_4024, 0);
 lean_ctor_release(x_4024, 1);
 x_4027 = x_4024;
} else {
 lean_dec_ref(x_4024);
 x_4027 = lean_box(0);
}
x_4028 = lean_ctor_get(x_4025, 0);
lean_inc(x_4028);
lean_dec(x_4025);
x_4029 = 0;
lean_inc(x_102);
lean_inc(x_4028);
x_4030 = l_Lean_Environment_find_x3f(x_4028, x_102, x_4029);
if (lean_obj_tag(x_4030) == 0)
{
lean_object* x_4031; lean_object* x_4032; 
lean_dec(x_4028);
lean_dec(x_4027);
lean_dec(x_4019);
lean_dec(x_4015);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4031 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_4032 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4031, x_3, x_4, x_5, x_4026);
return x_4032;
}
else
{
lean_object* x_4033; 
x_4033 = lean_ctor_get(x_4030, 0);
lean_inc(x_4033);
lean_dec(x_4030);
switch (lean_obj_tag(x_4033)) {
case 0:
{
lean_object* x_4034; lean_object* x_4035; uint8_t x_4036; 
lean_dec(x_4028);
lean_dec(x_4015);
if (lean_is_exclusive(x_4033)) {
 lean_ctor_release(x_4033, 0);
 x_4034 = x_4033;
} else {
 lean_dec_ref(x_4033);
 x_4034 = lean_box(0);
}
x_4035 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_4036 = lean_name_eq(x_102, x_4035);
if (x_4036 == 0)
{
lean_object* x_4037; uint8_t x_4038; 
x_4037 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_4038 = lean_name_eq(x_102, x_4037);
if (x_4038 == 0)
{
lean_object* x_4039; lean_object* x_4040; 
lean_dec(x_4027);
lean_inc(x_102);
x_4039 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_4026);
x_4040 = lean_ctor_get(x_4039, 0);
lean_inc(x_4040);
if (lean_obj_tag(x_4040) == 0)
{
lean_object* x_4041; lean_object* x_4042; uint8_t x_4043; lean_object* x_4044; lean_object* x_4045; lean_object* x_4046; lean_object* x_4047; lean_object* x_4048; lean_object* x_4049; lean_object* x_4050; lean_object* x_4051; lean_object* x_4052; 
lean_dec(x_4019);
lean_dec(x_2);
lean_dec(x_1);
x_4041 = lean_ctor_get(x_4039, 1);
lean_inc(x_4041);
if (lean_is_exclusive(x_4039)) {
 lean_ctor_release(x_4039, 0);
 lean_ctor_release(x_4039, 1);
 x_4042 = x_4039;
} else {
 lean_dec_ref(x_4039);
 x_4042 = lean_box(0);
}
x_4043 = 1;
x_4044 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4045 = l_Lean_Name_toString(x_102, x_4043, x_4044);
if (lean_is_scalar(x_4034)) {
 x_4046 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4046 = x_4034;
 lean_ctor_set_tag(x_4046, 3);
}
lean_ctor_set(x_4046, 0, x_4045);
x_4047 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_4042)) {
 x_4048 = lean_alloc_ctor(5, 2, 0);
} else {
 x_4048 = x_4042;
 lean_ctor_set_tag(x_4048, 5);
}
lean_ctor_set(x_4048, 0, x_4047);
lean_ctor_set(x_4048, 1, x_4046);
x_4049 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_4050 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4050, 0, x_4048);
lean_ctor_set(x_4050, 1, x_4049);
x_4051 = l_Lean_MessageData_ofFormat(x_4050);
x_4052 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4051, x_3, x_4, x_5, x_4041);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4052;
}
else
{
lean_object* x_4053; lean_object* x_4054; lean_object* x_4055; lean_object* x_4056; lean_object* x_4057; lean_object* x_4058; uint8_t x_4059; 
lean_dec(x_4034);
x_4053 = lean_ctor_get(x_4039, 1);
lean_inc(x_4053);
if (lean_is_exclusive(x_4039)) {
 lean_ctor_release(x_4039, 0);
 lean_ctor_release(x_4039, 1);
 x_4054 = x_4039;
} else {
 lean_dec_ref(x_4039);
 x_4054 = lean_box(0);
}
x_4055 = lean_ctor_get(x_4040, 0);
lean_inc(x_4055);
lean_dec(x_4040);
x_4056 = lean_array_get_size(x_4019);
x_4057 = l_Lean_IR_Decl_params(x_4055);
lean_dec(x_4055);
x_4058 = lean_array_get_size(x_4057);
lean_dec(x_4057);
x_4059 = lean_nat_dec_lt(x_4056, x_4058);
if (x_4059 == 0)
{
uint8_t x_4060; 
x_4060 = lean_nat_dec_eq(x_4056, x_4058);
if (x_4060 == 0)
{
lean_object* x_4061; lean_object* x_4062; lean_object* x_4063; lean_object* x_4064; lean_object* x_4065; 
x_4061 = lean_unsigned_to_nat(0u);
x_4062 = l_Array_extract___rarg(x_4019, x_4061, x_4058);
x_4063 = l_Array_extract___rarg(x_4019, x_4058, x_4056);
lean_dec(x_4056);
lean_dec(x_4019);
if (lean_is_scalar(x_4054)) {
 x_4064 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4064 = x_4054;
 lean_ctor_set_tag(x_4064, 6);
}
lean_ctor_set(x_4064, 0, x_102);
lean_ctor_set(x_4064, 1, x_4062);
x_4065 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_4064, x_4063, x_3, x_4, x_5, x_4053);
return x_4065;
}
else
{
lean_object* x_4066; lean_object* x_4067; 
lean_dec(x_4058);
lean_dec(x_4056);
if (lean_is_scalar(x_4054)) {
 x_4066 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4066 = x_4054;
 lean_ctor_set_tag(x_4066, 6);
}
lean_ctor_set(x_4066, 0, x_102);
lean_ctor_set(x_4066, 1, x_4019);
x_4067 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4066, x_3, x_4, x_5, x_4053);
return x_4067;
}
}
else
{
lean_object* x_4068; lean_object* x_4069; 
lean_dec(x_4058);
lean_dec(x_4056);
if (lean_is_scalar(x_4054)) {
 x_4068 = lean_alloc_ctor(7, 2, 0);
} else {
 x_4068 = x_4054;
 lean_ctor_set_tag(x_4068, 7);
}
lean_ctor_set(x_4068, 0, x_102);
lean_ctor_set(x_4068, 1, x_4019);
x_4069 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4068, x_3, x_4, x_5, x_4053);
return x_4069;
}
}
}
else
{
lean_object* x_4070; lean_object* x_4071; 
lean_dec(x_4034);
lean_dec(x_4019);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4070 = lean_box(13);
if (lean_is_scalar(x_4027)) {
 x_4071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4071 = x_4027;
}
lean_ctor_set(x_4071, 0, x_4070);
lean_ctor_set(x_4071, 1, x_4026);
return x_4071;
}
}
else
{
lean_object* x_4072; lean_object* x_4073; lean_object* x_4074; 
lean_dec(x_4034);
lean_dec(x_4027);
lean_dec(x_102);
x_4072 = l_Lean_IR_instInhabitedArg;
x_4073 = lean_unsigned_to_nat(2u);
x_4074 = lean_array_get(x_4072, x_4019, x_4073);
lean_dec(x_4019);
if (lean_obj_tag(x_4074) == 0)
{
lean_object* x_4075; lean_object* x_4076; 
x_4075 = lean_ctor_get(x_4074, 0);
lean_inc(x_4075);
lean_dec(x_4074);
x_4076 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4075, x_3, x_4, x_5, x_4026);
return x_4076;
}
else
{
lean_object* x_4077; lean_object* x_4078; 
x_4077 = lean_box(0);
x_4078 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4077, x_3, x_4, x_5, x_4026);
return x_4078;
}
}
}
case 2:
{
lean_object* x_4079; lean_object* x_4080; 
lean_dec(x_4033);
lean_dec(x_4028);
lean_dec(x_4027);
lean_dec(x_4019);
lean_dec(x_4015);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4079 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_4080 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4079, x_3, x_4, x_5, x_4026);
return x_4080;
}
case 4:
{
lean_object* x_4081; lean_object* x_4082; uint8_t x_4083; 
lean_dec(x_4028);
lean_dec(x_4027);
lean_dec(x_4015);
if (lean_is_exclusive(x_4033)) {
 lean_ctor_release(x_4033, 0);
 x_4081 = x_4033;
} else {
 lean_dec_ref(x_4033);
 x_4081 = lean_box(0);
}
x_4082 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_4083 = lean_name_eq(x_102, x_4082);
if (x_4083 == 0)
{
uint8_t x_4084; lean_object* x_4085; lean_object* x_4086; lean_object* x_4087; lean_object* x_4088; lean_object* x_4089; lean_object* x_4090; lean_object* x_4091; lean_object* x_4092; lean_object* x_4093; 
lean_dec(x_4019);
lean_dec(x_2);
lean_dec(x_1);
x_4084 = 1;
x_4085 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4086 = l_Lean_Name_toString(x_102, x_4084, x_4085);
if (lean_is_scalar(x_4081)) {
 x_4087 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4087 = x_4081;
 lean_ctor_set_tag(x_4087, 3);
}
lean_ctor_set(x_4087, 0, x_4086);
x_4088 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_4089 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4089, 0, x_4088);
lean_ctor_set(x_4089, 1, x_4087);
x_4090 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_4091 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4091, 0, x_4089);
lean_ctor_set(x_4091, 1, x_4090);
x_4092 = l_Lean_MessageData_ofFormat(x_4091);
x_4093 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4092, x_3, x_4, x_5, x_4026);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4093;
}
else
{
lean_object* x_4094; lean_object* x_4095; lean_object* x_4096; 
lean_dec(x_4081);
lean_dec(x_102);
x_4094 = l_Lean_IR_instInhabitedArg;
x_4095 = lean_unsigned_to_nat(2u);
x_4096 = lean_array_get(x_4094, x_4019, x_4095);
lean_dec(x_4019);
if (lean_obj_tag(x_4096) == 0)
{
lean_object* x_4097; lean_object* x_4098; 
x_4097 = lean_ctor_get(x_4096, 0);
lean_inc(x_4097);
lean_dec(x_4096);
x_4098 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4097, x_3, x_4, x_5, x_4026);
return x_4098;
}
else
{
lean_object* x_4099; lean_object* x_4100; 
x_4099 = lean_box(0);
x_4100 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4099, x_3, x_4, x_5, x_4026);
return x_4100;
}
}
}
case 5:
{
lean_object* x_4101; lean_object* x_4102; 
lean_dec(x_4033);
lean_dec(x_4028);
lean_dec(x_4027);
lean_dec(x_4019);
lean_dec(x_4015);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4101 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_4102 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4101, x_3, x_4, x_5, x_4026);
return x_4102;
}
case 6:
{
lean_object* x_4103; uint8_t x_4104; 
lean_dec(x_4027);
x_4103 = lean_ctor_get(x_4033, 0);
lean_inc(x_4103);
lean_dec(x_4033);
lean_inc(x_102);
x_4104 = l_Lean_isExtern(x_4028, x_102);
if (x_4104 == 0)
{
lean_object* x_4105; 
lean_dec(x_4019);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4105 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_4026);
if (lean_obj_tag(x_4105) == 0)
{
lean_object* x_4106; lean_object* x_4107; lean_object* x_4108; lean_object* x_4109; lean_object* x_4110; lean_object* x_4111; lean_object* x_4112; lean_object* x_4113; lean_object* x_4114; lean_object* x_4115; lean_object* x_4116; lean_object* x_4117; lean_object* x_4118; lean_object* x_4119; lean_object* x_4120; lean_object* x_4121; 
x_4106 = lean_ctor_get(x_4105, 0);
lean_inc(x_4106);
x_4107 = lean_ctor_get(x_4105, 1);
lean_inc(x_4107);
lean_dec(x_4105);
x_4108 = lean_ctor_get(x_4106, 0);
lean_inc(x_4108);
x_4109 = lean_ctor_get(x_4106, 1);
lean_inc(x_4109);
lean_dec(x_4106);
x_4110 = lean_ctor_get(x_4103, 3);
lean_inc(x_4110);
lean_dec(x_4103);
x_4111 = lean_array_get_size(x_4015);
x_4112 = l_Array_extract___rarg(x_4015, x_4110, x_4111);
lean_dec(x_4111);
lean_dec(x_4015);
x_4113 = lean_array_get_size(x_4109);
x_4114 = lean_unsigned_to_nat(0u);
x_4115 = lean_unsigned_to_nat(1u);
x_4116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4116, 0, x_4114);
lean_ctor_set(x_4116, 1, x_4113);
lean_ctor_set(x_4116, 2, x_4115);
x_4117 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_4118 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8(x_4109, x_4112, x_4116, x_4116, x_4117, x_4114, lean_box(0), lean_box(0), x_3, x_4, x_5, x_4107);
lean_dec(x_4116);
x_4119 = lean_ctor_get(x_4118, 0);
lean_inc(x_4119);
x_4120 = lean_ctor_get(x_4118, 1);
lean_inc(x_4120);
lean_dec(x_4118);
x_4121 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_4108, x_4109, x_4112, x_4119, x_3, x_4, x_5, x_4120);
lean_dec(x_4112);
lean_dec(x_4109);
return x_4121;
}
else
{
lean_object* x_4122; lean_object* x_4123; lean_object* x_4124; lean_object* x_4125; 
lean_dec(x_4103);
lean_dec(x_4015);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4122 = lean_ctor_get(x_4105, 0);
lean_inc(x_4122);
x_4123 = lean_ctor_get(x_4105, 1);
lean_inc(x_4123);
if (lean_is_exclusive(x_4105)) {
 lean_ctor_release(x_4105, 0);
 lean_ctor_release(x_4105, 1);
 x_4124 = x_4105;
} else {
 lean_dec_ref(x_4105);
 x_4124 = lean_box(0);
}
if (lean_is_scalar(x_4124)) {
 x_4125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4125 = x_4124;
}
lean_ctor_set(x_4125, 0, x_4122);
lean_ctor_set(x_4125, 1, x_4123);
return x_4125;
}
}
else
{
lean_object* x_4126; 
lean_dec(x_4103);
lean_dec(x_4015);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4019);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4126 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4019, x_3, x_4, x_5, x_4026);
if (lean_obj_tag(x_4126) == 0)
{
lean_object* x_4127; 
x_4127 = lean_ctor_get(x_4126, 0);
lean_inc(x_4127);
if (lean_obj_tag(x_4127) == 0)
{
lean_object* x_4128; lean_object* x_4129; lean_object* x_4130; 
x_4128 = lean_ctor_get(x_4126, 1);
lean_inc(x_4128);
lean_dec(x_4126);
x_4129 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4129, 0, x_102);
lean_ctor_set(x_4129, 1, x_4019);
x_4130 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4129, x_3, x_4, x_5, x_4128);
return x_4130;
}
else
{
lean_object* x_4131; lean_object* x_4132; lean_object* x_4133; lean_object* x_4134; 
lean_dec(x_4019);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4131 = lean_ctor_get(x_4126, 1);
lean_inc(x_4131);
if (lean_is_exclusive(x_4126)) {
 lean_ctor_release(x_4126, 0);
 lean_ctor_release(x_4126, 1);
 x_4132 = x_4126;
} else {
 lean_dec_ref(x_4126);
 x_4132 = lean_box(0);
}
x_4133 = lean_ctor_get(x_4127, 0);
lean_inc(x_4133);
lean_dec(x_4127);
if (lean_is_scalar(x_4132)) {
 x_4134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4134 = x_4132;
}
lean_ctor_set(x_4134, 0, x_4133);
lean_ctor_set(x_4134, 1, x_4131);
return x_4134;
}
}
else
{
lean_object* x_4135; lean_object* x_4136; lean_object* x_4137; lean_object* x_4138; 
lean_dec(x_4019);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4135 = lean_ctor_get(x_4126, 0);
lean_inc(x_4135);
x_4136 = lean_ctor_get(x_4126, 1);
lean_inc(x_4136);
if (lean_is_exclusive(x_4126)) {
 lean_ctor_release(x_4126, 0);
 lean_ctor_release(x_4126, 1);
 x_4137 = x_4126;
} else {
 lean_dec_ref(x_4126);
 x_4137 = lean_box(0);
}
if (lean_is_scalar(x_4137)) {
 x_4138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4138 = x_4137;
}
lean_ctor_set(x_4138, 0, x_4135);
lean_ctor_set(x_4138, 1, x_4136);
return x_4138;
}
}
}
case 7:
{
lean_object* x_4139; uint8_t x_4140; lean_object* x_4141; lean_object* x_4142; lean_object* x_4143; lean_object* x_4144; lean_object* x_4145; lean_object* x_4146; lean_object* x_4147; lean_object* x_4148; lean_object* x_4149; 
lean_dec(x_4028);
lean_dec(x_4027);
lean_dec(x_4019);
lean_dec(x_4015);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_4033)) {
 lean_ctor_release(x_4033, 0);
 x_4139 = x_4033;
} else {
 lean_dec_ref(x_4033);
 x_4139 = lean_box(0);
}
x_4140 = 1;
x_4141 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4142 = l_Lean_Name_toString(x_102, x_4140, x_4141);
if (lean_is_scalar(x_4139)) {
 x_4143 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4143 = x_4139;
 lean_ctor_set_tag(x_4143, 3);
}
lean_ctor_set(x_4143, 0, x_4142);
x_4144 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_4145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4145, 0, x_4144);
lean_ctor_set(x_4145, 1, x_4143);
x_4146 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_4147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4147, 0, x_4145);
lean_ctor_set(x_4147, 1, x_4146);
x_4148 = l_Lean_MessageData_ofFormat(x_4147);
x_4149 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4148, x_3, x_4, x_5, x_4026);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4149;
}
default: 
{
lean_object* x_4150; 
lean_dec(x_4033);
lean_dec(x_4028);
lean_dec(x_4027);
lean_dec(x_4015);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4019);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4150 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4019, x_3, x_4, x_5, x_4026);
if (lean_obj_tag(x_4150) == 0)
{
lean_object* x_4151; 
x_4151 = lean_ctor_get(x_4150, 0);
lean_inc(x_4151);
if (lean_obj_tag(x_4151) == 0)
{
lean_object* x_4152; lean_object* x_4153; lean_object* x_4154; 
x_4152 = lean_ctor_get(x_4150, 1);
lean_inc(x_4152);
lean_dec(x_4150);
x_4153 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4153, 0, x_102);
lean_ctor_set(x_4153, 1, x_4019);
x_4154 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4153, x_3, x_4, x_5, x_4152);
return x_4154;
}
else
{
lean_object* x_4155; lean_object* x_4156; lean_object* x_4157; lean_object* x_4158; 
lean_dec(x_4019);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4155 = lean_ctor_get(x_4150, 1);
lean_inc(x_4155);
if (lean_is_exclusive(x_4150)) {
 lean_ctor_release(x_4150, 0);
 lean_ctor_release(x_4150, 1);
 x_4156 = x_4150;
} else {
 lean_dec_ref(x_4150);
 x_4156 = lean_box(0);
}
x_4157 = lean_ctor_get(x_4151, 0);
lean_inc(x_4157);
lean_dec(x_4151);
if (lean_is_scalar(x_4156)) {
 x_4158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4158 = x_4156;
}
lean_ctor_set(x_4158, 0, x_4157);
lean_ctor_set(x_4158, 1, x_4155);
return x_4158;
}
}
else
{
lean_object* x_4159; lean_object* x_4160; lean_object* x_4161; lean_object* x_4162; 
lean_dec(x_4019);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4159 = lean_ctor_get(x_4150, 0);
lean_inc(x_4159);
x_4160 = lean_ctor_get(x_4150, 1);
lean_inc(x_4160);
if (lean_is_exclusive(x_4150)) {
 lean_ctor_release(x_4150, 0);
 lean_ctor_release(x_4150, 1);
 x_4161 = x_4150;
} else {
 lean_dec_ref(x_4150);
 x_4161 = lean_box(0);
}
if (lean_is_scalar(x_4161)) {
 x_4162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4162 = x_4161;
}
lean_ctor_set(x_4162, 0, x_4159);
lean_ctor_set(x_4162, 1, x_4160);
return x_4162;
}
}
}
}
}
else
{
lean_object* x_4163; lean_object* x_4164; lean_object* x_4165; lean_object* x_4166; 
lean_dec(x_4019);
lean_dec(x_4015);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4163 = lean_ctor_get(x_4021, 1);
lean_inc(x_4163);
if (lean_is_exclusive(x_4021)) {
 lean_ctor_release(x_4021, 0);
 lean_ctor_release(x_4021, 1);
 x_4164 = x_4021;
} else {
 lean_dec_ref(x_4021);
 x_4164 = lean_box(0);
}
x_4165 = lean_ctor_get(x_4022, 0);
lean_inc(x_4165);
lean_dec(x_4022);
if (lean_is_scalar(x_4164)) {
 x_4166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4166 = x_4164;
}
lean_ctor_set(x_4166, 0, x_4165);
lean_ctor_set(x_4166, 1, x_4163);
return x_4166;
}
}
else
{
lean_object* x_4167; lean_object* x_4168; lean_object* x_4169; lean_object* x_4170; 
lean_dec(x_4019);
lean_dec(x_4015);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4167 = lean_ctor_get(x_4021, 0);
lean_inc(x_4167);
x_4168 = lean_ctor_get(x_4021, 1);
lean_inc(x_4168);
if (lean_is_exclusive(x_4021)) {
 lean_ctor_release(x_4021, 0);
 lean_ctor_release(x_4021, 1);
 x_4169 = x_4021;
} else {
 lean_dec_ref(x_4021);
 x_4169 = lean_box(0);
}
if (lean_is_scalar(x_4169)) {
 x_4170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4170 = x_4169;
}
lean_ctor_set(x_4170, 0, x_4167);
lean_ctor_set(x_4170, 1, x_4168);
return x_4170;
}
}
else
{
lean_object* x_4171; lean_object* x_4172; lean_object* x_4173; lean_object* x_4174; 
lean_dec(x_4015);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4171 = lean_ctor_get(x_4018, 0);
lean_inc(x_4171);
x_4172 = lean_ctor_get(x_4018, 1);
lean_inc(x_4172);
if (lean_is_exclusive(x_4018)) {
 lean_ctor_release(x_4018, 0);
 lean_ctor_release(x_4018, 1);
 x_4173 = x_4018;
} else {
 lean_dec_ref(x_4018);
 x_4173 = lean_box(0);
}
if (lean_is_scalar(x_4173)) {
 x_4174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4174 = x_4173;
}
lean_ctor_set(x_4174, 0, x_4171);
lean_ctor_set(x_4174, 1, x_4172);
return x_4174;
}
}
}
}
}
default: 
{
uint8_t x_4175; 
x_4175 = !lean_is_exclusive(x_7);
if (x_4175 == 0)
{
lean_object* x_4176; lean_object* x_4177; lean_object* x_4178; size_t x_4179; size_t x_4180; lean_object* x_4181; 
x_4176 = lean_ctor_get(x_7, 2);
x_4177 = lean_ctor_get(x_7, 1);
lean_dec(x_4177);
x_4178 = lean_ctor_get(x_7, 0);
lean_dec(x_4178);
x_4179 = lean_array_size(x_4176);
x_4180 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4176);
x_4181 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_4179, x_4180, x_4176, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_4181) == 0)
{
lean_object* x_4182; lean_object* x_4183; lean_object* x_4184; 
x_4182 = lean_ctor_get(x_4181, 0);
lean_inc(x_4182);
x_4183 = lean_ctor_get(x_4181, 1);
lean_inc(x_4183);
lean_dec(x_4181);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4182);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4184 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4182, x_3, x_4, x_5, x_4183);
if (lean_obj_tag(x_4184) == 0)
{
lean_object* x_4185; 
x_4185 = lean_ctor_get(x_4184, 0);
lean_inc(x_4185);
if (lean_obj_tag(x_4185) == 0)
{
lean_object* x_4186; lean_object* x_4187; uint8_t x_4188; 
x_4186 = lean_ctor_get(x_4184, 1);
lean_inc(x_4186);
lean_dec(x_4184);
x_4187 = lean_st_ref_get(x_5, x_4186);
x_4188 = !lean_is_exclusive(x_4187);
if (x_4188 == 0)
{
lean_object* x_4189; lean_object* x_4190; lean_object* x_4191; uint8_t x_4192; lean_object* x_4193; 
x_4189 = lean_ctor_get(x_4187, 0);
x_4190 = lean_ctor_get(x_4187, 1);
x_4191 = lean_ctor_get(x_4189, 0);
lean_inc(x_4191);
lean_dec(x_4189);
x_4192 = 0;
lean_inc(x_102);
lean_inc(x_4191);
x_4193 = l_Lean_Environment_find_x3f(x_4191, x_102, x_4192);
if (lean_obj_tag(x_4193) == 0)
{
lean_object* x_4194; lean_object* x_4195; 
lean_dec(x_4191);
lean_free_object(x_4187);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4194 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_4195 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4194, x_3, x_4, x_5, x_4190);
return x_4195;
}
else
{
lean_object* x_4196; 
x_4196 = lean_ctor_get(x_4193, 0);
lean_inc(x_4196);
lean_dec(x_4193);
switch (lean_obj_tag(x_4196)) {
case 0:
{
uint8_t x_4197; 
lean_dec(x_4191);
lean_free_object(x_7);
lean_dec(x_4176);
x_4197 = !lean_is_exclusive(x_4196);
if (x_4197 == 0)
{
lean_object* x_4198; lean_object* x_4199; uint8_t x_4200; 
x_4198 = lean_ctor_get(x_4196, 0);
lean_dec(x_4198);
x_4199 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_4200 = lean_name_eq(x_102, x_4199);
if (x_4200 == 0)
{
lean_object* x_4201; uint8_t x_4202; 
x_4201 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_4202 = lean_name_eq(x_102, x_4201);
if (x_4202 == 0)
{
lean_object* x_4203; lean_object* x_4204; 
lean_free_object(x_4187);
lean_inc(x_102);
x_4203 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_4190);
x_4204 = lean_ctor_get(x_4203, 0);
lean_inc(x_4204);
if (lean_obj_tag(x_4204) == 0)
{
uint8_t x_4205; 
lean_dec(x_4182);
lean_dec(x_2);
lean_dec(x_1);
x_4205 = !lean_is_exclusive(x_4203);
if (x_4205 == 0)
{
lean_object* x_4206; lean_object* x_4207; uint8_t x_4208; lean_object* x_4209; lean_object* x_4210; lean_object* x_4211; lean_object* x_4212; lean_object* x_4213; lean_object* x_4214; lean_object* x_4215; 
x_4206 = lean_ctor_get(x_4203, 1);
x_4207 = lean_ctor_get(x_4203, 0);
lean_dec(x_4207);
x_4208 = 1;
x_4209 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4210 = l_Lean_Name_toString(x_102, x_4208, x_4209);
lean_ctor_set_tag(x_4196, 3);
lean_ctor_set(x_4196, 0, x_4210);
x_4211 = l_Lean_IR_ToIR_lowerLet___closed__13;
lean_ctor_set_tag(x_4203, 5);
lean_ctor_set(x_4203, 1, x_4196);
lean_ctor_set(x_4203, 0, x_4211);
x_4212 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_4213 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4213, 0, x_4203);
lean_ctor_set(x_4213, 1, x_4212);
x_4214 = l_Lean_MessageData_ofFormat(x_4213);
x_4215 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4214, x_3, x_4, x_5, x_4206);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4215;
}
else
{
lean_object* x_4216; uint8_t x_4217; lean_object* x_4218; lean_object* x_4219; lean_object* x_4220; lean_object* x_4221; lean_object* x_4222; lean_object* x_4223; lean_object* x_4224; lean_object* x_4225; 
x_4216 = lean_ctor_get(x_4203, 1);
lean_inc(x_4216);
lean_dec(x_4203);
x_4217 = 1;
x_4218 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4219 = l_Lean_Name_toString(x_102, x_4217, x_4218);
lean_ctor_set_tag(x_4196, 3);
lean_ctor_set(x_4196, 0, x_4219);
x_4220 = l_Lean_IR_ToIR_lowerLet___closed__13;
x_4221 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4221, 0, x_4220);
lean_ctor_set(x_4221, 1, x_4196);
x_4222 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_4223 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4223, 0, x_4221);
lean_ctor_set(x_4223, 1, x_4222);
x_4224 = l_Lean_MessageData_ofFormat(x_4223);
x_4225 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4224, x_3, x_4, x_5, x_4216);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4225;
}
}
else
{
uint8_t x_4226; 
lean_free_object(x_4196);
x_4226 = !lean_is_exclusive(x_4203);
if (x_4226 == 0)
{
lean_object* x_4227; lean_object* x_4228; lean_object* x_4229; lean_object* x_4230; lean_object* x_4231; lean_object* x_4232; uint8_t x_4233; 
x_4227 = lean_ctor_get(x_4203, 1);
x_4228 = lean_ctor_get(x_4203, 0);
lean_dec(x_4228);
x_4229 = lean_ctor_get(x_4204, 0);
lean_inc(x_4229);
lean_dec(x_4204);
x_4230 = lean_array_get_size(x_4182);
x_4231 = l_Lean_IR_Decl_params(x_4229);
lean_dec(x_4229);
x_4232 = lean_array_get_size(x_4231);
lean_dec(x_4231);
x_4233 = lean_nat_dec_lt(x_4230, x_4232);
if (x_4233 == 0)
{
uint8_t x_4234; 
x_4234 = lean_nat_dec_eq(x_4230, x_4232);
if (x_4234 == 0)
{
lean_object* x_4235; lean_object* x_4236; lean_object* x_4237; lean_object* x_4238; 
x_4235 = lean_unsigned_to_nat(0u);
x_4236 = l_Array_extract___rarg(x_4182, x_4235, x_4232);
x_4237 = l_Array_extract___rarg(x_4182, x_4232, x_4230);
lean_dec(x_4230);
lean_dec(x_4182);
lean_ctor_set_tag(x_4203, 6);
lean_ctor_set(x_4203, 1, x_4236);
lean_ctor_set(x_4203, 0, x_102);
x_4238 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_4203, x_4237, x_3, x_4, x_5, x_4227);
return x_4238;
}
else
{
lean_object* x_4239; 
lean_dec(x_4232);
lean_dec(x_4230);
lean_ctor_set_tag(x_4203, 6);
lean_ctor_set(x_4203, 1, x_4182);
lean_ctor_set(x_4203, 0, x_102);
x_4239 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4203, x_3, x_4, x_5, x_4227);
return x_4239;
}
}
else
{
lean_object* x_4240; 
lean_dec(x_4232);
lean_dec(x_4230);
lean_ctor_set_tag(x_4203, 7);
lean_ctor_set(x_4203, 1, x_4182);
lean_ctor_set(x_4203, 0, x_102);
x_4240 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4203, x_3, x_4, x_5, x_4227);
return x_4240;
}
}
else
{
lean_object* x_4241; lean_object* x_4242; lean_object* x_4243; lean_object* x_4244; lean_object* x_4245; uint8_t x_4246; 
x_4241 = lean_ctor_get(x_4203, 1);
lean_inc(x_4241);
lean_dec(x_4203);
x_4242 = lean_ctor_get(x_4204, 0);
lean_inc(x_4242);
lean_dec(x_4204);
x_4243 = lean_array_get_size(x_4182);
x_4244 = l_Lean_IR_Decl_params(x_4242);
lean_dec(x_4242);
x_4245 = lean_array_get_size(x_4244);
lean_dec(x_4244);
x_4246 = lean_nat_dec_lt(x_4243, x_4245);
if (x_4246 == 0)
{
uint8_t x_4247; 
x_4247 = lean_nat_dec_eq(x_4243, x_4245);
if (x_4247 == 0)
{
lean_object* x_4248; lean_object* x_4249; lean_object* x_4250; lean_object* x_4251; lean_object* x_4252; 
x_4248 = lean_unsigned_to_nat(0u);
x_4249 = l_Array_extract___rarg(x_4182, x_4248, x_4245);
x_4250 = l_Array_extract___rarg(x_4182, x_4245, x_4243);
lean_dec(x_4243);
lean_dec(x_4182);
x_4251 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4251, 0, x_102);
lean_ctor_set(x_4251, 1, x_4249);
x_4252 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_4251, x_4250, x_3, x_4, x_5, x_4241);
return x_4252;
}
else
{
lean_object* x_4253; lean_object* x_4254; 
lean_dec(x_4245);
lean_dec(x_4243);
x_4253 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4253, 0, x_102);
lean_ctor_set(x_4253, 1, x_4182);
x_4254 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4253, x_3, x_4, x_5, x_4241);
return x_4254;
}
}
else
{
lean_object* x_4255; lean_object* x_4256; 
lean_dec(x_4245);
lean_dec(x_4243);
x_4255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4255, 0, x_102);
lean_ctor_set(x_4255, 1, x_4182);
x_4256 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4255, x_3, x_4, x_5, x_4241);
return x_4256;
}
}
}
}
else
{
lean_object* x_4257; 
lean_free_object(x_4196);
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4257 = lean_box(13);
lean_ctor_set(x_4187, 0, x_4257);
return x_4187;
}
}
else
{
lean_object* x_4258; lean_object* x_4259; lean_object* x_4260; 
lean_free_object(x_4196);
lean_free_object(x_4187);
lean_dec(x_102);
x_4258 = l_Lean_IR_instInhabitedArg;
x_4259 = lean_unsigned_to_nat(2u);
x_4260 = lean_array_get(x_4258, x_4182, x_4259);
lean_dec(x_4182);
if (lean_obj_tag(x_4260) == 0)
{
lean_object* x_4261; lean_object* x_4262; 
x_4261 = lean_ctor_get(x_4260, 0);
lean_inc(x_4261);
lean_dec(x_4260);
x_4262 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4261, x_3, x_4, x_5, x_4190);
return x_4262;
}
else
{
lean_object* x_4263; lean_object* x_4264; 
x_4263 = lean_box(0);
x_4264 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4263, x_3, x_4, x_5, x_4190);
return x_4264;
}
}
}
else
{
lean_object* x_4265; uint8_t x_4266; 
lean_dec(x_4196);
x_4265 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_4266 = lean_name_eq(x_102, x_4265);
if (x_4266 == 0)
{
lean_object* x_4267; uint8_t x_4268; 
x_4267 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_4268 = lean_name_eq(x_102, x_4267);
if (x_4268 == 0)
{
lean_object* x_4269; lean_object* x_4270; 
lean_free_object(x_4187);
lean_inc(x_102);
x_4269 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_4190);
x_4270 = lean_ctor_get(x_4269, 0);
lean_inc(x_4270);
if (lean_obj_tag(x_4270) == 0)
{
lean_object* x_4271; lean_object* x_4272; uint8_t x_4273; lean_object* x_4274; lean_object* x_4275; lean_object* x_4276; lean_object* x_4277; lean_object* x_4278; lean_object* x_4279; lean_object* x_4280; lean_object* x_4281; lean_object* x_4282; 
lean_dec(x_4182);
lean_dec(x_2);
lean_dec(x_1);
x_4271 = lean_ctor_get(x_4269, 1);
lean_inc(x_4271);
if (lean_is_exclusive(x_4269)) {
 lean_ctor_release(x_4269, 0);
 lean_ctor_release(x_4269, 1);
 x_4272 = x_4269;
} else {
 lean_dec_ref(x_4269);
 x_4272 = lean_box(0);
}
x_4273 = 1;
x_4274 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4275 = l_Lean_Name_toString(x_102, x_4273, x_4274);
x_4276 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4276, 0, x_4275);
x_4277 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_4272)) {
 x_4278 = lean_alloc_ctor(5, 2, 0);
} else {
 x_4278 = x_4272;
 lean_ctor_set_tag(x_4278, 5);
}
lean_ctor_set(x_4278, 0, x_4277);
lean_ctor_set(x_4278, 1, x_4276);
x_4279 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_4280 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4280, 0, x_4278);
lean_ctor_set(x_4280, 1, x_4279);
x_4281 = l_Lean_MessageData_ofFormat(x_4280);
x_4282 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4281, x_3, x_4, x_5, x_4271);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4282;
}
else
{
lean_object* x_4283; lean_object* x_4284; lean_object* x_4285; lean_object* x_4286; lean_object* x_4287; lean_object* x_4288; uint8_t x_4289; 
x_4283 = lean_ctor_get(x_4269, 1);
lean_inc(x_4283);
if (lean_is_exclusive(x_4269)) {
 lean_ctor_release(x_4269, 0);
 lean_ctor_release(x_4269, 1);
 x_4284 = x_4269;
} else {
 lean_dec_ref(x_4269);
 x_4284 = lean_box(0);
}
x_4285 = lean_ctor_get(x_4270, 0);
lean_inc(x_4285);
lean_dec(x_4270);
x_4286 = lean_array_get_size(x_4182);
x_4287 = l_Lean_IR_Decl_params(x_4285);
lean_dec(x_4285);
x_4288 = lean_array_get_size(x_4287);
lean_dec(x_4287);
x_4289 = lean_nat_dec_lt(x_4286, x_4288);
if (x_4289 == 0)
{
uint8_t x_4290; 
x_4290 = lean_nat_dec_eq(x_4286, x_4288);
if (x_4290 == 0)
{
lean_object* x_4291; lean_object* x_4292; lean_object* x_4293; lean_object* x_4294; lean_object* x_4295; 
x_4291 = lean_unsigned_to_nat(0u);
x_4292 = l_Array_extract___rarg(x_4182, x_4291, x_4288);
x_4293 = l_Array_extract___rarg(x_4182, x_4288, x_4286);
lean_dec(x_4286);
lean_dec(x_4182);
if (lean_is_scalar(x_4284)) {
 x_4294 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4294 = x_4284;
 lean_ctor_set_tag(x_4294, 6);
}
lean_ctor_set(x_4294, 0, x_102);
lean_ctor_set(x_4294, 1, x_4292);
x_4295 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_4294, x_4293, x_3, x_4, x_5, x_4283);
return x_4295;
}
else
{
lean_object* x_4296; lean_object* x_4297; 
lean_dec(x_4288);
lean_dec(x_4286);
if (lean_is_scalar(x_4284)) {
 x_4296 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4296 = x_4284;
 lean_ctor_set_tag(x_4296, 6);
}
lean_ctor_set(x_4296, 0, x_102);
lean_ctor_set(x_4296, 1, x_4182);
x_4297 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4296, x_3, x_4, x_5, x_4283);
return x_4297;
}
}
else
{
lean_object* x_4298; lean_object* x_4299; 
lean_dec(x_4288);
lean_dec(x_4286);
if (lean_is_scalar(x_4284)) {
 x_4298 = lean_alloc_ctor(7, 2, 0);
} else {
 x_4298 = x_4284;
 lean_ctor_set_tag(x_4298, 7);
}
lean_ctor_set(x_4298, 0, x_102);
lean_ctor_set(x_4298, 1, x_4182);
x_4299 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4298, x_3, x_4, x_5, x_4283);
return x_4299;
}
}
}
else
{
lean_object* x_4300; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4300 = lean_box(13);
lean_ctor_set(x_4187, 0, x_4300);
return x_4187;
}
}
else
{
lean_object* x_4301; lean_object* x_4302; lean_object* x_4303; 
lean_free_object(x_4187);
lean_dec(x_102);
x_4301 = l_Lean_IR_instInhabitedArg;
x_4302 = lean_unsigned_to_nat(2u);
x_4303 = lean_array_get(x_4301, x_4182, x_4302);
lean_dec(x_4182);
if (lean_obj_tag(x_4303) == 0)
{
lean_object* x_4304; lean_object* x_4305; 
x_4304 = lean_ctor_get(x_4303, 0);
lean_inc(x_4304);
lean_dec(x_4303);
x_4305 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4304, x_3, x_4, x_5, x_4190);
return x_4305;
}
else
{
lean_object* x_4306; lean_object* x_4307; 
x_4306 = lean_box(0);
x_4307 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4306, x_3, x_4, x_5, x_4190);
return x_4307;
}
}
}
}
case 2:
{
lean_object* x_4308; lean_object* x_4309; 
lean_dec(x_4196);
lean_dec(x_4191);
lean_free_object(x_4187);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4308 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_4309 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4308, x_3, x_4, x_5, x_4190);
return x_4309;
}
case 4:
{
uint8_t x_4310; 
lean_dec(x_4191);
lean_free_object(x_4187);
lean_free_object(x_7);
lean_dec(x_4176);
x_4310 = !lean_is_exclusive(x_4196);
if (x_4310 == 0)
{
lean_object* x_4311; lean_object* x_4312; uint8_t x_4313; 
x_4311 = lean_ctor_get(x_4196, 0);
lean_dec(x_4311);
x_4312 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_4313 = lean_name_eq(x_102, x_4312);
if (x_4313 == 0)
{
uint8_t x_4314; lean_object* x_4315; lean_object* x_4316; lean_object* x_4317; lean_object* x_4318; lean_object* x_4319; lean_object* x_4320; lean_object* x_4321; lean_object* x_4322; 
lean_dec(x_4182);
lean_dec(x_2);
lean_dec(x_1);
x_4314 = 1;
x_4315 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4316 = l_Lean_Name_toString(x_102, x_4314, x_4315);
lean_ctor_set_tag(x_4196, 3);
lean_ctor_set(x_4196, 0, x_4316);
x_4317 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_4318 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4318, 0, x_4317);
lean_ctor_set(x_4318, 1, x_4196);
x_4319 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_4320 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4320, 0, x_4318);
lean_ctor_set(x_4320, 1, x_4319);
x_4321 = l_Lean_MessageData_ofFormat(x_4320);
x_4322 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4321, x_3, x_4, x_5, x_4190);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4322;
}
else
{
lean_object* x_4323; lean_object* x_4324; lean_object* x_4325; 
lean_free_object(x_4196);
lean_dec(x_102);
x_4323 = l_Lean_IR_instInhabitedArg;
x_4324 = lean_unsigned_to_nat(2u);
x_4325 = lean_array_get(x_4323, x_4182, x_4324);
lean_dec(x_4182);
if (lean_obj_tag(x_4325) == 0)
{
lean_object* x_4326; lean_object* x_4327; 
x_4326 = lean_ctor_get(x_4325, 0);
lean_inc(x_4326);
lean_dec(x_4325);
x_4327 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4326, x_3, x_4, x_5, x_4190);
return x_4327;
}
else
{
lean_object* x_4328; lean_object* x_4329; 
x_4328 = lean_box(0);
x_4329 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4328, x_3, x_4, x_5, x_4190);
return x_4329;
}
}
}
else
{
lean_object* x_4330; uint8_t x_4331; 
lean_dec(x_4196);
x_4330 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_4331 = lean_name_eq(x_102, x_4330);
if (x_4331 == 0)
{
uint8_t x_4332; lean_object* x_4333; lean_object* x_4334; lean_object* x_4335; lean_object* x_4336; lean_object* x_4337; lean_object* x_4338; lean_object* x_4339; lean_object* x_4340; lean_object* x_4341; 
lean_dec(x_4182);
lean_dec(x_2);
lean_dec(x_1);
x_4332 = 1;
x_4333 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4334 = l_Lean_Name_toString(x_102, x_4332, x_4333);
x_4335 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4335, 0, x_4334);
x_4336 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_4337 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4337, 0, x_4336);
lean_ctor_set(x_4337, 1, x_4335);
x_4338 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_4339 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4339, 0, x_4337);
lean_ctor_set(x_4339, 1, x_4338);
x_4340 = l_Lean_MessageData_ofFormat(x_4339);
x_4341 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4340, x_3, x_4, x_5, x_4190);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4341;
}
else
{
lean_object* x_4342; lean_object* x_4343; lean_object* x_4344; 
lean_dec(x_102);
x_4342 = l_Lean_IR_instInhabitedArg;
x_4343 = lean_unsigned_to_nat(2u);
x_4344 = lean_array_get(x_4342, x_4182, x_4343);
lean_dec(x_4182);
if (lean_obj_tag(x_4344) == 0)
{
lean_object* x_4345; lean_object* x_4346; 
x_4345 = lean_ctor_get(x_4344, 0);
lean_inc(x_4345);
lean_dec(x_4344);
x_4346 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4345, x_3, x_4, x_5, x_4190);
return x_4346;
}
else
{
lean_object* x_4347; lean_object* x_4348; 
x_4347 = lean_box(0);
x_4348 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4347, x_3, x_4, x_5, x_4190);
return x_4348;
}
}
}
}
case 5:
{
lean_object* x_4349; lean_object* x_4350; 
lean_dec(x_4196);
lean_dec(x_4191);
lean_free_object(x_4187);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4349 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_4350 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4349, x_3, x_4, x_5, x_4190);
return x_4350;
}
case 6:
{
lean_object* x_4351; uint8_t x_4352; 
lean_free_object(x_4187);
x_4351 = lean_ctor_get(x_4196, 0);
lean_inc(x_4351);
lean_dec(x_4196);
lean_inc(x_102);
x_4352 = l_Lean_isExtern(x_4191, x_102);
if (x_4352 == 0)
{
lean_object* x_4353; 
lean_dec(x_4182);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4353 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_4190);
if (lean_obj_tag(x_4353) == 0)
{
lean_object* x_4354; lean_object* x_4355; lean_object* x_4356; lean_object* x_4357; lean_object* x_4358; lean_object* x_4359; lean_object* x_4360; lean_object* x_4361; lean_object* x_4362; lean_object* x_4363; lean_object* x_4364; lean_object* x_4365; lean_object* x_4366; lean_object* x_4367; lean_object* x_4368; 
x_4354 = lean_ctor_get(x_4353, 0);
lean_inc(x_4354);
x_4355 = lean_ctor_get(x_4353, 1);
lean_inc(x_4355);
lean_dec(x_4353);
x_4356 = lean_ctor_get(x_4354, 0);
lean_inc(x_4356);
x_4357 = lean_ctor_get(x_4354, 1);
lean_inc(x_4357);
lean_dec(x_4354);
x_4358 = lean_ctor_get(x_4351, 3);
lean_inc(x_4358);
lean_dec(x_4351);
x_4359 = lean_array_get_size(x_4176);
x_4360 = l_Array_extract___rarg(x_4176, x_4358, x_4359);
lean_dec(x_4359);
lean_dec(x_4176);
x_4361 = lean_array_get_size(x_4357);
x_4362 = lean_unsigned_to_nat(0u);
x_4363 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_4363);
lean_ctor_set(x_7, 1, x_4361);
lean_ctor_set(x_7, 0, x_4362);
x_4364 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_4365 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9(x_4357, x_4360, x_7, x_7, x_4364, x_4362, lean_box(0), lean_box(0), x_3, x_4, x_5, x_4355);
lean_dec(x_7);
x_4366 = lean_ctor_get(x_4365, 0);
lean_inc(x_4366);
x_4367 = lean_ctor_get(x_4365, 1);
lean_inc(x_4367);
lean_dec(x_4365);
x_4368 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_4356, x_4357, x_4360, x_4366, x_3, x_4, x_5, x_4367);
lean_dec(x_4360);
lean_dec(x_4357);
return x_4368;
}
else
{
uint8_t x_4369; 
lean_dec(x_4351);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4369 = !lean_is_exclusive(x_4353);
if (x_4369 == 0)
{
return x_4353;
}
else
{
lean_object* x_4370; lean_object* x_4371; lean_object* x_4372; 
x_4370 = lean_ctor_get(x_4353, 0);
x_4371 = lean_ctor_get(x_4353, 1);
lean_inc(x_4371);
lean_inc(x_4370);
lean_dec(x_4353);
x_4372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4372, 0, x_4370);
lean_ctor_set(x_4372, 1, x_4371);
return x_4372;
}
}
}
else
{
lean_object* x_4373; 
lean_dec(x_4351);
lean_free_object(x_7);
lean_dec(x_4176);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4182);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4373 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4182, x_3, x_4, x_5, x_4190);
if (lean_obj_tag(x_4373) == 0)
{
lean_object* x_4374; 
x_4374 = lean_ctor_get(x_4373, 0);
lean_inc(x_4374);
if (lean_obj_tag(x_4374) == 0)
{
lean_object* x_4375; lean_object* x_4376; lean_object* x_4377; 
x_4375 = lean_ctor_get(x_4373, 1);
lean_inc(x_4375);
lean_dec(x_4373);
x_4376 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4376, 0, x_102);
lean_ctor_set(x_4376, 1, x_4182);
x_4377 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4376, x_3, x_4, x_5, x_4375);
return x_4377;
}
else
{
uint8_t x_4378; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4378 = !lean_is_exclusive(x_4373);
if (x_4378 == 0)
{
lean_object* x_4379; lean_object* x_4380; 
x_4379 = lean_ctor_get(x_4373, 0);
lean_dec(x_4379);
x_4380 = lean_ctor_get(x_4374, 0);
lean_inc(x_4380);
lean_dec(x_4374);
lean_ctor_set(x_4373, 0, x_4380);
return x_4373;
}
else
{
lean_object* x_4381; lean_object* x_4382; lean_object* x_4383; 
x_4381 = lean_ctor_get(x_4373, 1);
lean_inc(x_4381);
lean_dec(x_4373);
x_4382 = lean_ctor_get(x_4374, 0);
lean_inc(x_4382);
lean_dec(x_4374);
x_4383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4383, 0, x_4382);
lean_ctor_set(x_4383, 1, x_4381);
return x_4383;
}
}
}
else
{
uint8_t x_4384; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4384 = !lean_is_exclusive(x_4373);
if (x_4384 == 0)
{
return x_4373;
}
else
{
lean_object* x_4385; lean_object* x_4386; lean_object* x_4387; 
x_4385 = lean_ctor_get(x_4373, 0);
x_4386 = lean_ctor_get(x_4373, 1);
lean_inc(x_4386);
lean_inc(x_4385);
lean_dec(x_4373);
x_4387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4387, 0, x_4385);
lean_ctor_set(x_4387, 1, x_4386);
return x_4387;
}
}
}
}
case 7:
{
uint8_t x_4388; 
lean_dec(x_4191);
lean_free_object(x_4187);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_2);
lean_dec(x_1);
x_4388 = !lean_is_exclusive(x_4196);
if (x_4388 == 0)
{
lean_object* x_4389; uint8_t x_4390; lean_object* x_4391; lean_object* x_4392; lean_object* x_4393; lean_object* x_4394; lean_object* x_4395; lean_object* x_4396; lean_object* x_4397; lean_object* x_4398; 
x_4389 = lean_ctor_get(x_4196, 0);
lean_dec(x_4389);
x_4390 = 1;
x_4391 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4392 = l_Lean_Name_toString(x_102, x_4390, x_4391);
lean_ctor_set_tag(x_4196, 3);
lean_ctor_set(x_4196, 0, x_4392);
x_4393 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_4394 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4394, 0, x_4393);
lean_ctor_set(x_4394, 1, x_4196);
x_4395 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_4396 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4396, 0, x_4394);
lean_ctor_set(x_4396, 1, x_4395);
x_4397 = l_Lean_MessageData_ofFormat(x_4396);
x_4398 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4397, x_3, x_4, x_5, x_4190);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4398;
}
else
{
uint8_t x_4399; lean_object* x_4400; lean_object* x_4401; lean_object* x_4402; lean_object* x_4403; lean_object* x_4404; lean_object* x_4405; lean_object* x_4406; lean_object* x_4407; lean_object* x_4408; 
lean_dec(x_4196);
x_4399 = 1;
x_4400 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4401 = l_Lean_Name_toString(x_102, x_4399, x_4400);
x_4402 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4402, 0, x_4401);
x_4403 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_4404 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4404, 0, x_4403);
lean_ctor_set(x_4404, 1, x_4402);
x_4405 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_4406 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4406, 0, x_4404);
lean_ctor_set(x_4406, 1, x_4405);
x_4407 = l_Lean_MessageData_ofFormat(x_4406);
x_4408 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4407, x_3, x_4, x_5, x_4190);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4408;
}
}
default: 
{
lean_object* x_4409; 
lean_dec(x_4196);
lean_dec(x_4191);
lean_free_object(x_4187);
lean_free_object(x_7);
lean_dec(x_4176);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4182);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4409 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4182, x_3, x_4, x_5, x_4190);
if (lean_obj_tag(x_4409) == 0)
{
lean_object* x_4410; 
x_4410 = lean_ctor_get(x_4409, 0);
lean_inc(x_4410);
if (lean_obj_tag(x_4410) == 0)
{
lean_object* x_4411; lean_object* x_4412; lean_object* x_4413; 
x_4411 = lean_ctor_get(x_4409, 1);
lean_inc(x_4411);
lean_dec(x_4409);
x_4412 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4412, 0, x_102);
lean_ctor_set(x_4412, 1, x_4182);
x_4413 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4412, x_3, x_4, x_5, x_4411);
return x_4413;
}
else
{
uint8_t x_4414; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4414 = !lean_is_exclusive(x_4409);
if (x_4414 == 0)
{
lean_object* x_4415; lean_object* x_4416; 
x_4415 = lean_ctor_get(x_4409, 0);
lean_dec(x_4415);
x_4416 = lean_ctor_get(x_4410, 0);
lean_inc(x_4416);
lean_dec(x_4410);
lean_ctor_set(x_4409, 0, x_4416);
return x_4409;
}
else
{
lean_object* x_4417; lean_object* x_4418; lean_object* x_4419; 
x_4417 = lean_ctor_get(x_4409, 1);
lean_inc(x_4417);
lean_dec(x_4409);
x_4418 = lean_ctor_get(x_4410, 0);
lean_inc(x_4418);
lean_dec(x_4410);
x_4419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4419, 0, x_4418);
lean_ctor_set(x_4419, 1, x_4417);
return x_4419;
}
}
}
else
{
uint8_t x_4420; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4420 = !lean_is_exclusive(x_4409);
if (x_4420 == 0)
{
return x_4409;
}
else
{
lean_object* x_4421; lean_object* x_4422; lean_object* x_4423; 
x_4421 = lean_ctor_get(x_4409, 0);
x_4422 = lean_ctor_get(x_4409, 1);
lean_inc(x_4422);
lean_inc(x_4421);
lean_dec(x_4409);
x_4423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4423, 0, x_4421);
lean_ctor_set(x_4423, 1, x_4422);
return x_4423;
}
}
}
}
}
}
else
{
lean_object* x_4424; lean_object* x_4425; lean_object* x_4426; uint8_t x_4427; lean_object* x_4428; 
x_4424 = lean_ctor_get(x_4187, 0);
x_4425 = lean_ctor_get(x_4187, 1);
lean_inc(x_4425);
lean_inc(x_4424);
lean_dec(x_4187);
x_4426 = lean_ctor_get(x_4424, 0);
lean_inc(x_4426);
lean_dec(x_4424);
x_4427 = 0;
lean_inc(x_102);
lean_inc(x_4426);
x_4428 = l_Lean_Environment_find_x3f(x_4426, x_102, x_4427);
if (lean_obj_tag(x_4428) == 0)
{
lean_object* x_4429; lean_object* x_4430; 
lean_dec(x_4426);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4429 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_4430 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4429, x_3, x_4, x_5, x_4425);
return x_4430;
}
else
{
lean_object* x_4431; 
x_4431 = lean_ctor_get(x_4428, 0);
lean_inc(x_4431);
lean_dec(x_4428);
switch (lean_obj_tag(x_4431)) {
case 0:
{
lean_object* x_4432; lean_object* x_4433; uint8_t x_4434; 
lean_dec(x_4426);
lean_free_object(x_7);
lean_dec(x_4176);
if (lean_is_exclusive(x_4431)) {
 lean_ctor_release(x_4431, 0);
 x_4432 = x_4431;
} else {
 lean_dec_ref(x_4431);
 x_4432 = lean_box(0);
}
x_4433 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_4434 = lean_name_eq(x_102, x_4433);
if (x_4434 == 0)
{
lean_object* x_4435; uint8_t x_4436; 
x_4435 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_4436 = lean_name_eq(x_102, x_4435);
if (x_4436 == 0)
{
lean_object* x_4437; lean_object* x_4438; 
lean_inc(x_102);
x_4437 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_4425);
x_4438 = lean_ctor_get(x_4437, 0);
lean_inc(x_4438);
if (lean_obj_tag(x_4438) == 0)
{
lean_object* x_4439; lean_object* x_4440; uint8_t x_4441; lean_object* x_4442; lean_object* x_4443; lean_object* x_4444; lean_object* x_4445; lean_object* x_4446; lean_object* x_4447; lean_object* x_4448; lean_object* x_4449; lean_object* x_4450; 
lean_dec(x_4182);
lean_dec(x_2);
lean_dec(x_1);
x_4439 = lean_ctor_get(x_4437, 1);
lean_inc(x_4439);
if (lean_is_exclusive(x_4437)) {
 lean_ctor_release(x_4437, 0);
 lean_ctor_release(x_4437, 1);
 x_4440 = x_4437;
} else {
 lean_dec_ref(x_4437);
 x_4440 = lean_box(0);
}
x_4441 = 1;
x_4442 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4443 = l_Lean_Name_toString(x_102, x_4441, x_4442);
if (lean_is_scalar(x_4432)) {
 x_4444 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4444 = x_4432;
 lean_ctor_set_tag(x_4444, 3);
}
lean_ctor_set(x_4444, 0, x_4443);
x_4445 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_4440)) {
 x_4446 = lean_alloc_ctor(5, 2, 0);
} else {
 x_4446 = x_4440;
 lean_ctor_set_tag(x_4446, 5);
}
lean_ctor_set(x_4446, 0, x_4445);
lean_ctor_set(x_4446, 1, x_4444);
x_4447 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_4448 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4448, 0, x_4446);
lean_ctor_set(x_4448, 1, x_4447);
x_4449 = l_Lean_MessageData_ofFormat(x_4448);
x_4450 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4449, x_3, x_4, x_5, x_4439);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4450;
}
else
{
lean_object* x_4451; lean_object* x_4452; lean_object* x_4453; lean_object* x_4454; lean_object* x_4455; lean_object* x_4456; uint8_t x_4457; 
lean_dec(x_4432);
x_4451 = lean_ctor_get(x_4437, 1);
lean_inc(x_4451);
if (lean_is_exclusive(x_4437)) {
 lean_ctor_release(x_4437, 0);
 lean_ctor_release(x_4437, 1);
 x_4452 = x_4437;
} else {
 lean_dec_ref(x_4437);
 x_4452 = lean_box(0);
}
x_4453 = lean_ctor_get(x_4438, 0);
lean_inc(x_4453);
lean_dec(x_4438);
x_4454 = lean_array_get_size(x_4182);
x_4455 = l_Lean_IR_Decl_params(x_4453);
lean_dec(x_4453);
x_4456 = lean_array_get_size(x_4455);
lean_dec(x_4455);
x_4457 = lean_nat_dec_lt(x_4454, x_4456);
if (x_4457 == 0)
{
uint8_t x_4458; 
x_4458 = lean_nat_dec_eq(x_4454, x_4456);
if (x_4458 == 0)
{
lean_object* x_4459; lean_object* x_4460; lean_object* x_4461; lean_object* x_4462; lean_object* x_4463; 
x_4459 = lean_unsigned_to_nat(0u);
x_4460 = l_Array_extract___rarg(x_4182, x_4459, x_4456);
x_4461 = l_Array_extract___rarg(x_4182, x_4456, x_4454);
lean_dec(x_4454);
lean_dec(x_4182);
if (lean_is_scalar(x_4452)) {
 x_4462 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4462 = x_4452;
 lean_ctor_set_tag(x_4462, 6);
}
lean_ctor_set(x_4462, 0, x_102);
lean_ctor_set(x_4462, 1, x_4460);
x_4463 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_4462, x_4461, x_3, x_4, x_5, x_4451);
return x_4463;
}
else
{
lean_object* x_4464; lean_object* x_4465; 
lean_dec(x_4456);
lean_dec(x_4454);
if (lean_is_scalar(x_4452)) {
 x_4464 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4464 = x_4452;
 lean_ctor_set_tag(x_4464, 6);
}
lean_ctor_set(x_4464, 0, x_102);
lean_ctor_set(x_4464, 1, x_4182);
x_4465 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4464, x_3, x_4, x_5, x_4451);
return x_4465;
}
}
else
{
lean_object* x_4466; lean_object* x_4467; 
lean_dec(x_4456);
lean_dec(x_4454);
if (lean_is_scalar(x_4452)) {
 x_4466 = lean_alloc_ctor(7, 2, 0);
} else {
 x_4466 = x_4452;
 lean_ctor_set_tag(x_4466, 7);
}
lean_ctor_set(x_4466, 0, x_102);
lean_ctor_set(x_4466, 1, x_4182);
x_4467 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4466, x_3, x_4, x_5, x_4451);
return x_4467;
}
}
}
else
{
lean_object* x_4468; lean_object* x_4469; 
lean_dec(x_4432);
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4468 = lean_box(13);
x_4469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4469, 0, x_4468);
lean_ctor_set(x_4469, 1, x_4425);
return x_4469;
}
}
else
{
lean_object* x_4470; lean_object* x_4471; lean_object* x_4472; 
lean_dec(x_4432);
lean_dec(x_102);
x_4470 = l_Lean_IR_instInhabitedArg;
x_4471 = lean_unsigned_to_nat(2u);
x_4472 = lean_array_get(x_4470, x_4182, x_4471);
lean_dec(x_4182);
if (lean_obj_tag(x_4472) == 0)
{
lean_object* x_4473; lean_object* x_4474; 
x_4473 = lean_ctor_get(x_4472, 0);
lean_inc(x_4473);
lean_dec(x_4472);
x_4474 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4473, x_3, x_4, x_5, x_4425);
return x_4474;
}
else
{
lean_object* x_4475; lean_object* x_4476; 
x_4475 = lean_box(0);
x_4476 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4475, x_3, x_4, x_5, x_4425);
return x_4476;
}
}
}
case 2:
{
lean_object* x_4477; lean_object* x_4478; 
lean_dec(x_4431);
lean_dec(x_4426);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4477 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_4478 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4477, x_3, x_4, x_5, x_4425);
return x_4478;
}
case 4:
{
lean_object* x_4479; lean_object* x_4480; uint8_t x_4481; 
lean_dec(x_4426);
lean_free_object(x_7);
lean_dec(x_4176);
if (lean_is_exclusive(x_4431)) {
 lean_ctor_release(x_4431, 0);
 x_4479 = x_4431;
} else {
 lean_dec_ref(x_4431);
 x_4479 = lean_box(0);
}
x_4480 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_4481 = lean_name_eq(x_102, x_4480);
if (x_4481 == 0)
{
uint8_t x_4482; lean_object* x_4483; lean_object* x_4484; lean_object* x_4485; lean_object* x_4486; lean_object* x_4487; lean_object* x_4488; lean_object* x_4489; lean_object* x_4490; lean_object* x_4491; 
lean_dec(x_4182);
lean_dec(x_2);
lean_dec(x_1);
x_4482 = 1;
x_4483 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4484 = l_Lean_Name_toString(x_102, x_4482, x_4483);
if (lean_is_scalar(x_4479)) {
 x_4485 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4485 = x_4479;
 lean_ctor_set_tag(x_4485, 3);
}
lean_ctor_set(x_4485, 0, x_4484);
x_4486 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_4487 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4487, 0, x_4486);
lean_ctor_set(x_4487, 1, x_4485);
x_4488 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_4489 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4489, 0, x_4487);
lean_ctor_set(x_4489, 1, x_4488);
x_4490 = l_Lean_MessageData_ofFormat(x_4489);
x_4491 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4490, x_3, x_4, x_5, x_4425);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4491;
}
else
{
lean_object* x_4492; lean_object* x_4493; lean_object* x_4494; 
lean_dec(x_4479);
lean_dec(x_102);
x_4492 = l_Lean_IR_instInhabitedArg;
x_4493 = lean_unsigned_to_nat(2u);
x_4494 = lean_array_get(x_4492, x_4182, x_4493);
lean_dec(x_4182);
if (lean_obj_tag(x_4494) == 0)
{
lean_object* x_4495; lean_object* x_4496; 
x_4495 = lean_ctor_get(x_4494, 0);
lean_inc(x_4495);
lean_dec(x_4494);
x_4496 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4495, x_3, x_4, x_5, x_4425);
return x_4496;
}
else
{
lean_object* x_4497; lean_object* x_4498; 
x_4497 = lean_box(0);
x_4498 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4497, x_3, x_4, x_5, x_4425);
return x_4498;
}
}
}
case 5:
{
lean_object* x_4499; lean_object* x_4500; 
lean_dec(x_4431);
lean_dec(x_4426);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4499 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_4500 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4499, x_3, x_4, x_5, x_4425);
return x_4500;
}
case 6:
{
lean_object* x_4501; uint8_t x_4502; 
x_4501 = lean_ctor_get(x_4431, 0);
lean_inc(x_4501);
lean_dec(x_4431);
lean_inc(x_102);
x_4502 = l_Lean_isExtern(x_4426, x_102);
if (x_4502 == 0)
{
lean_object* x_4503; 
lean_dec(x_4182);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4503 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_4425);
if (lean_obj_tag(x_4503) == 0)
{
lean_object* x_4504; lean_object* x_4505; lean_object* x_4506; lean_object* x_4507; lean_object* x_4508; lean_object* x_4509; lean_object* x_4510; lean_object* x_4511; lean_object* x_4512; lean_object* x_4513; lean_object* x_4514; lean_object* x_4515; lean_object* x_4516; lean_object* x_4517; lean_object* x_4518; 
x_4504 = lean_ctor_get(x_4503, 0);
lean_inc(x_4504);
x_4505 = lean_ctor_get(x_4503, 1);
lean_inc(x_4505);
lean_dec(x_4503);
x_4506 = lean_ctor_get(x_4504, 0);
lean_inc(x_4506);
x_4507 = lean_ctor_get(x_4504, 1);
lean_inc(x_4507);
lean_dec(x_4504);
x_4508 = lean_ctor_get(x_4501, 3);
lean_inc(x_4508);
lean_dec(x_4501);
x_4509 = lean_array_get_size(x_4176);
x_4510 = l_Array_extract___rarg(x_4176, x_4508, x_4509);
lean_dec(x_4509);
lean_dec(x_4176);
x_4511 = lean_array_get_size(x_4507);
x_4512 = lean_unsigned_to_nat(0u);
x_4513 = lean_unsigned_to_nat(1u);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 2, x_4513);
lean_ctor_set(x_7, 1, x_4511);
lean_ctor_set(x_7, 0, x_4512);
x_4514 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_4515 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9(x_4507, x_4510, x_7, x_7, x_4514, x_4512, lean_box(0), lean_box(0), x_3, x_4, x_5, x_4505);
lean_dec(x_7);
x_4516 = lean_ctor_get(x_4515, 0);
lean_inc(x_4516);
x_4517 = lean_ctor_get(x_4515, 1);
lean_inc(x_4517);
lean_dec(x_4515);
x_4518 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_4506, x_4507, x_4510, x_4516, x_3, x_4, x_5, x_4517);
lean_dec(x_4510);
lean_dec(x_4507);
return x_4518;
}
else
{
lean_object* x_4519; lean_object* x_4520; lean_object* x_4521; lean_object* x_4522; 
lean_dec(x_4501);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4519 = lean_ctor_get(x_4503, 0);
lean_inc(x_4519);
x_4520 = lean_ctor_get(x_4503, 1);
lean_inc(x_4520);
if (lean_is_exclusive(x_4503)) {
 lean_ctor_release(x_4503, 0);
 lean_ctor_release(x_4503, 1);
 x_4521 = x_4503;
} else {
 lean_dec_ref(x_4503);
 x_4521 = lean_box(0);
}
if (lean_is_scalar(x_4521)) {
 x_4522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4522 = x_4521;
}
lean_ctor_set(x_4522, 0, x_4519);
lean_ctor_set(x_4522, 1, x_4520);
return x_4522;
}
}
else
{
lean_object* x_4523; 
lean_dec(x_4501);
lean_free_object(x_7);
lean_dec(x_4176);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4182);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4523 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4182, x_3, x_4, x_5, x_4425);
if (lean_obj_tag(x_4523) == 0)
{
lean_object* x_4524; 
x_4524 = lean_ctor_get(x_4523, 0);
lean_inc(x_4524);
if (lean_obj_tag(x_4524) == 0)
{
lean_object* x_4525; lean_object* x_4526; lean_object* x_4527; 
x_4525 = lean_ctor_get(x_4523, 1);
lean_inc(x_4525);
lean_dec(x_4523);
x_4526 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4526, 0, x_102);
lean_ctor_set(x_4526, 1, x_4182);
x_4527 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4526, x_3, x_4, x_5, x_4525);
return x_4527;
}
else
{
lean_object* x_4528; lean_object* x_4529; lean_object* x_4530; lean_object* x_4531; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4528 = lean_ctor_get(x_4523, 1);
lean_inc(x_4528);
if (lean_is_exclusive(x_4523)) {
 lean_ctor_release(x_4523, 0);
 lean_ctor_release(x_4523, 1);
 x_4529 = x_4523;
} else {
 lean_dec_ref(x_4523);
 x_4529 = lean_box(0);
}
x_4530 = lean_ctor_get(x_4524, 0);
lean_inc(x_4530);
lean_dec(x_4524);
if (lean_is_scalar(x_4529)) {
 x_4531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4531 = x_4529;
}
lean_ctor_set(x_4531, 0, x_4530);
lean_ctor_set(x_4531, 1, x_4528);
return x_4531;
}
}
else
{
lean_object* x_4532; lean_object* x_4533; lean_object* x_4534; lean_object* x_4535; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4532 = lean_ctor_get(x_4523, 0);
lean_inc(x_4532);
x_4533 = lean_ctor_get(x_4523, 1);
lean_inc(x_4533);
if (lean_is_exclusive(x_4523)) {
 lean_ctor_release(x_4523, 0);
 lean_ctor_release(x_4523, 1);
 x_4534 = x_4523;
} else {
 lean_dec_ref(x_4523);
 x_4534 = lean_box(0);
}
if (lean_is_scalar(x_4534)) {
 x_4535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4535 = x_4534;
}
lean_ctor_set(x_4535, 0, x_4532);
lean_ctor_set(x_4535, 1, x_4533);
return x_4535;
}
}
}
case 7:
{
lean_object* x_4536; uint8_t x_4537; lean_object* x_4538; lean_object* x_4539; lean_object* x_4540; lean_object* x_4541; lean_object* x_4542; lean_object* x_4543; lean_object* x_4544; lean_object* x_4545; lean_object* x_4546; 
lean_dec(x_4426);
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_4431)) {
 lean_ctor_release(x_4431, 0);
 x_4536 = x_4431;
} else {
 lean_dec_ref(x_4431);
 x_4536 = lean_box(0);
}
x_4537 = 1;
x_4538 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4539 = l_Lean_Name_toString(x_102, x_4537, x_4538);
if (lean_is_scalar(x_4536)) {
 x_4540 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4540 = x_4536;
 lean_ctor_set_tag(x_4540, 3);
}
lean_ctor_set(x_4540, 0, x_4539);
x_4541 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_4542 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4542, 0, x_4541);
lean_ctor_set(x_4542, 1, x_4540);
x_4543 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_4544 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4544, 0, x_4542);
lean_ctor_set(x_4544, 1, x_4543);
x_4545 = l_Lean_MessageData_ofFormat(x_4544);
x_4546 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4545, x_3, x_4, x_5, x_4425);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4546;
}
default: 
{
lean_object* x_4547; 
lean_dec(x_4431);
lean_dec(x_4426);
lean_free_object(x_7);
lean_dec(x_4176);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4182);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4547 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4182, x_3, x_4, x_5, x_4425);
if (lean_obj_tag(x_4547) == 0)
{
lean_object* x_4548; 
x_4548 = lean_ctor_get(x_4547, 0);
lean_inc(x_4548);
if (lean_obj_tag(x_4548) == 0)
{
lean_object* x_4549; lean_object* x_4550; lean_object* x_4551; 
x_4549 = lean_ctor_get(x_4547, 1);
lean_inc(x_4549);
lean_dec(x_4547);
x_4550 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4550, 0, x_102);
lean_ctor_set(x_4550, 1, x_4182);
x_4551 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4550, x_3, x_4, x_5, x_4549);
return x_4551;
}
else
{
lean_object* x_4552; lean_object* x_4553; lean_object* x_4554; lean_object* x_4555; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4552 = lean_ctor_get(x_4547, 1);
lean_inc(x_4552);
if (lean_is_exclusive(x_4547)) {
 lean_ctor_release(x_4547, 0);
 lean_ctor_release(x_4547, 1);
 x_4553 = x_4547;
} else {
 lean_dec_ref(x_4547);
 x_4553 = lean_box(0);
}
x_4554 = lean_ctor_get(x_4548, 0);
lean_inc(x_4554);
lean_dec(x_4548);
if (lean_is_scalar(x_4553)) {
 x_4555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4555 = x_4553;
}
lean_ctor_set(x_4555, 0, x_4554);
lean_ctor_set(x_4555, 1, x_4552);
return x_4555;
}
}
else
{
lean_object* x_4556; lean_object* x_4557; lean_object* x_4558; lean_object* x_4559; 
lean_dec(x_4182);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4556 = lean_ctor_get(x_4547, 0);
lean_inc(x_4556);
x_4557 = lean_ctor_get(x_4547, 1);
lean_inc(x_4557);
if (lean_is_exclusive(x_4547)) {
 lean_ctor_release(x_4547, 0);
 lean_ctor_release(x_4547, 1);
 x_4558 = x_4547;
} else {
 lean_dec_ref(x_4547);
 x_4558 = lean_box(0);
}
if (lean_is_scalar(x_4558)) {
 x_4559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4559 = x_4558;
}
lean_ctor_set(x_4559, 0, x_4556);
lean_ctor_set(x_4559, 1, x_4557);
return x_4559;
}
}
}
}
}
}
else
{
uint8_t x_4560; 
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4560 = !lean_is_exclusive(x_4184);
if (x_4560 == 0)
{
lean_object* x_4561; lean_object* x_4562; 
x_4561 = lean_ctor_get(x_4184, 0);
lean_dec(x_4561);
x_4562 = lean_ctor_get(x_4185, 0);
lean_inc(x_4562);
lean_dec(x_4185);
lean_ctor_set(x_4184, 0, x_4562);
return x_4184;
}
else
{
lean_object* x_4563; lean_object* x_4564; lean_object* x_4565; 
x_4563 = lean_ctor_get(x_4184, 1);
lean_inc(x_4563);
lean_dec(x_4184);
x_4564 = lean_ctor_get(x_4185, 0);
lean_inc(x_4564);
lean_dec(x_4185);
x_4565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4565, 0, x_4564);
lean_ctor_set(x_4565, 1, x_4563);
return x_4565;
}
}
}
else
{
uint8_t x_4566; 
lean_dec(x_4182);
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4566 = !lean_is_exclusive(x_4184);
if (x_4566 == 0)
{
return x_4184;
}
else
{
lean_object* x_4567; lean_object* x_4568; lean_object* x_4569; 
x_4567 = lean_ctor_get(x_4184, 0);
x_4568 = lean_ctor_get(x_4184, 1);
lean_inc(x_4568);
lean_inc(x_4567);
lean_dec(x_4184);
x_4569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4569, 0, x_4567);
lean_ctor_set(x_4569, 1, x_4568);
return x_4569;
}
}
}
else
{
uint8_t x_4570; 
lean_free_object(x_7);
lean_dec(x_4176);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4570 = !lean_is_exclusive(x_4181);
if (x_4570 == 0)
{
return x_4181;
}
else
{
lean_object* x_4571; lean_object* x_4572; lean_object* x_4573; 
x_4571 = lean_ctor_get(x_4181, 0);
x_4572 = lean_ctor_get(x_4181, 1);
lean_inc(x_4572);
lean_inc(x_4571);
lean_dec(x_4181);
x_4573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4573, 0, x_4571);
lean_ctor_set(x_4573, 1, x_4572);
return x_4573;
}
}
}
else
{
lean_object* x_4574; size_t x_4575; size_t x_4576; lean_object* x_4577; 
x_4574 = lean_ctor_get(x_7, 2);
lean_inc(x_4574);
lean_dec(x_7);
x_4575 = lean_array_size(x_4574);
x_4576 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4574);
x_4577 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_4575, x_4576, x_4574, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_4577) == 0)
{
lean_object* x_4578; lean_object* x_4579; lean_object* x_4580; 
x_4578 = lean_ctor_get(x_4577, 0);
lean_inc(x_4578);
x_4579 = lean_ctor_get(x_4577, 1);
lean_inc(x_4579);
lean_dec(x_4577);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4578);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4580 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4578, x_3, x_4, x_5, x_4579);
if (lean_obj_tag(x_4580) == 0)
{
lean_object* x_4581; 
x_4581 = lean_ctor_get(x_4580, 0);
lean_inc(x_4581);
if (lean_obj_tag(x_4581) == 0)
{
lean_object* x_4582; lean_object* x_4583; lean_object* x_4584; lean_object* x_4585; lean_object* x_4586; lean_object* x_4587; uint8_t x_4588; lean_object* x_4589; 
x_4582 = lean_ctor_get(x_4580, 1);
lean_inc(x_4582);
lean_dec(x_4580);
x_4583 = lean_st_ref_get(x_5, x_4582);
x_4584 = lean_ctor_get(x_4583, 0);
lean_inc(x_4584);
x_4585 = lean_ctor_get(x_4583, 1);
lean_inc(x_4585);
if (lean_is_exclusive(x_4583)) {
 lean_ctor_release(x_4583, 0);
 lean_ctor_release(x_4583, 1);
 x_4586 = x_4583;
} else {
 lean_dec_ref(x_4583);
 x_4586 = lean_box(0);
}
x_4587 = lean_ctor_get(x_4584, 0);
lean_inc(x_4587);
lean_dec(x_4584);
x_4588 = 0;
lean_inc(x_102);
lean_inc(x_4587);
x_4589 = l_Lean_Environment_find_x3f(x_4587, x_102, x_4588);
if (lean_obj_tag(x_4589) == 0)
{
lean_object* x_4590; lean_object* x_4591; 
lean_dec(x_4587);
lean_dec(x_4586);
lean_dec(x_4578);
lean_dec(x_4574);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4590 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_4591 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4590, x_3, x_4, x_5, x_4585);
return x_4591;
}
else
{
lean_object* x_4592; 
x_4592 = lean_ctor_get(x_4589, 0);
lean_inc(x_4592);
lean_dec(x_4589);
switch (lean_obj_tag(x_4592)) {
case 0:
{
lean_object* x_4593; lean_object* x_4594; uint8_t x_4595; 
lean_dec(x_4587);
lean_dec(x_4574);
if (lean_is_exclusive(x_4592)) {
 lean_ctor_release(x_4592, 0);
 x_4593 = x_4592;
} else {
 lean_dec_ref(x_4592);
 x_4593 = lean_box(0);
}
x_4594 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_4595 = lean_name_eq(x_102, x_4594);
if (x_4595 == 0)
{
lean_object* x_4596; uint8_t x_4597; 
x_4596 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_4597 = lean_name_eq(x_102, x_4596);
if (x_4597 == 0)
{
lean_object* x_4598; lean_object* x_4599; 
lean_dec(x_4586);
lean_inc(x_102);
x_4598 = l_Lean_IR_ToIR_findDecl(x_102, x_3, x_4, x_5, x_4585);
x_4599 = lean_ctor_get(x_4598, 0);
lean_inc(x_4599);
if (lean_obj_tag(x_4599) == 0)
{
lean_object* x_4600; lean_object* x_4601; uint8_t x_4602; lean_object* x_4603; lean_object* x_4604; lean_object* x_4605; lean_object* x_4606; lean_object* x_4607; lean_object* x_4608; lean_object* x_4609; lean_object* x_4610; lean_object* x_4611; 
lean_dec(x_4578);
lean_dec(x_2);
lean_dec(x_1);
x_4600 = lean_ctor_get(x_4598, 1);
lean_inc(x_4600);
if (lean_is_exclusive(x_4598)) {
 lean_ctor_release(x_4598, 0);
 lean_ctor_release(x_4598, 1);
 x_4601 = x_4598;
} else {
 lean_dec_ref(x_4598);
 x_4601 = lean_box(0);
}
x_4602 = 1;
x_4603 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4604 = l_Lean_Name_toString(x_102, x_4602, x_4603);
if (lean_is_scalar(x_4593)) {
 x_4605 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4605 = x_4593;
 lean_ctor_set_tag(x_4605, 3);
}
lean_ctor_set(x_4605, 0, x_4604);
x_4606 = l_Lean_IR_ToIR_lowerLet___closed__13;
if (lean_is_scalar(x_4601)) {
 x_4607 = lean_alloc_ctor(5, 2, 0);
} else {
 x_4607 = x_4601;
 lean_ctor_set_tag(x_4607, 5);
}
lean_ctor_set(x_4607, 0, x_4606);
lean_ctor_set(x_4607, 1, x_4605);
x_4608 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_4609 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4609, 0, x_4607);
lean_ctor_set(x_4609, 1, x_4608);
x_4610 = l_Lean_MessageData_ofFormat(x_4609);
x_4611 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4610, x_3, x_4, x_5, x_4600);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4611;
}
else
{
lean_object* x_4612; lean_object* x_4613; lean_object* x_4614; lean_object* x_4615; lean_object* x_4616; lean_object* x_4617; uint8_t x_4618; 
lean_dec(x_4593);
x_4612 = lean_ctor_get(x_4598, 1);
lean_inc(x_4612);
if (lean_is_exclusive(x_4598)) {
 lean_ctor_release(x_4598, 0);
 lean_ctor_release(x_4598, 1);
 x_4613 = x_4598;
} else {
 lean_dec_ref(x_4598);
 x_4613 = lean_box(0);
}
x_4614 = lean_ctor_get(x_4599, 0);
lean_inc(x_4614);
lean_dec(x_4599);
x_4615 = lean_array_get_size(x_4578);
x_4616 = l_Lean_IR_Decl_params(x_4614);
lean_dec(x_4614);
x_4617 = lean_array_get_size(x_4616);
lean_dec(x_4616);
x_4618 = lean_nat_dec_lt(x_4615, x_4617);
if (x_4618 == 0)
{
uint8_t x_4619; 
x_4619 = lean_nat_dec_eq(x_4615, x_4617);
if (x_4619 == 0)
{
lean_object* x_4620; lean_object* x_4621; lean_object* x_4622; lean_object* x_4623; lean_object* x_4624; 
x_4620 = lean_unsigned_to_nat(0u);
x_4621 = l_Array_extract___rarg(x_4578, x_4620, x_4617);
x_4622 = l_Array_extract___rarg(x_4578, x_4617, x_4615);
lean_dec(x_4615);
lean_dec(x_4578);
if (lean_is_scalar(x_4613)) {
 x_4623 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4623 = x_4613;
 lean_ctor_set_tag(x_4623, 6);
}
lean_ctor_set(x_4623, 0, x_102);
lean_ctor_set(x_4623, 1, x_4621);
x_4624 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_4623, x_4622, x_3, x_4, x_5, x_4612);
return x_4624;
}
else
{
lean_object* x_4625; lean_object* x_4626; 
lean_dec(x_4617);
lean_dec(x_4615);
if (lean_is_scalar(x_4613)) {
 x_4625 = lean_alloc_ctor(6, 2, 0);
} else {
 x_4625 = x_4613;
 lean_ctor_set_tag(x_4625, 6);
}
lean_ctor_set(x_4625, 0, x_102);
lean_ctor_set(x_4625, 1, x_4578);
x_4626 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4625, x_3, x_4, x_5, x_4612);
return x_4626;
}
}
else
{
lean_object* x_4627; lean_object* x_4628; 
lean_dec(x_4617);
lean_dec(x_4615);
if (lean_is_scalar(x_4613)) {
 x_4627 = lean_alloc_ctor(7, 2, 0);
} else {
 x_4627 = x_4613;
 lean_ctor_set_tag(x_4627, 7);
}
lean_ctor_set(x_4627, 0, x_102);
lean_ctor_set(x_4627, 1, x_4578);
x_4628 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4627, x_3, x_4, x_5, x_4612);
return x_4628;
}
}
}
else
{
lean_object* x_4629; lean_object* x_4630; 
lean_dec(x_4593);
lean_dec(x_4578);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4629 = lean_box(13);
if (lean_is_scalar(x_4586)) {
 x_4630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4630 = x_4586;
}
lean_ctor_set(x_4630, 0, x_4629);
lean_ctor_set(x_4630, 1, x_4585);
return x_4630;
}
}
else
{
lean_object* x_4631; lean_object* x_4632; lean_object* x_4633; 
lean_dec(x_4593);
lean_dec(x_4586);
lean_dec(x_102);
x_4631 = l_Lean_IR_instInhabitedArg;
x_4632 = lean_unsigned_to_nat(2u);
x_4633 = lean_array_get(x_4631, x_4578, x_4632);
lean_dec(x_4578);
if (lean_obj_tag(x_4633) == 0)
{
lean_object* x_4634; lean_object* x_4635; 
x_4634 = lean_ctor_get(x_4633, 0);
lean_inc(x_4634);
lean_dec(x_4633);
x_4635 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4634, x_3, x_4, x_5, x_4585);
return x_4635;
}
else
{
lean_object* x_4636; lean_object* x_4637; 
x_4636 = lean_box(0);
x_4637 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4636, x_3, x_4, x_5, x_4585);
return x_4637;
}
}
}
case 2:
{
lean_object* x_4638; lean_object* x_4639; 
lean_dec(x_4592);
lean_dec(x_4587);
lean_dec(x_4586);
lean_dec(x_4578);
lean_dec(x_4574);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4638 = l_Lean_IR_ToIR_lowerLet___closed__18;
x_4639 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4638, x_3, x_4, x_5, x_4585);
return x_4639;
}
case 4:
{
lean_object* x_4640; lean_object* x_4641; uint8_t x_4642; 
lean_dec(x_4587);
lean_dec(x_4586);
lean_dec(x_4574);
if (lean_is_exclusive(x_4592)) {
 lean_ctor_release(x_4592, 0);
 x_4640 = x_4592;
} else {
 lean_dec_ref(x_4592);
 x_4640 = lean_box(0);
}
x_4641 = l_Lean_IR_ToIR_lowerLet___closed__20;
x_4642 = lean_name_eq(x_102, x_4641);
if (x_4642 == 0)
{
uint8_t x_4643; lean_object* x_4644; lean_object* x_4645; lean_object* x_4646; lean_object* x_4647; lean_object* x_4648; lean_object* x_4649; lean_object* x_4650; lean_object* x_4651; lean_object* x_4652; 
lean_dec(x_4578);
lean_dec(x_2);
lean_dec(x_1);
x_4643 = 1;
x_4644 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4645 = l_Lean_Name_toString(x_102, x_4643, x_4644);
if (lean_is_scalar(x_4640)) {
 x_4646 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4646 = x_4640;
 lean_ctor_set_tag(x_4646, 3);
}
lean_ctor_set(x_4646, 0, x_4645);
x_4647 = l_Lean_IR_ToIR_lowerLet___closed__22;
x_4648 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4648, 0, x_4647);
lean_ctor_set(x_4648, 1, x_4646);
x_4649 = l_Lean_IR_ToIR_lowerLet___closed__24;
x_4650 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4650, 0, x_4648);
lean_ctor_set(x_4650, 1, x_4649);
x_4651 = l_Lean_MessageData_ofFormat(x_4650);
x_4652 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4651, x_3, x_4, x_5, x_4585);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4652;
}
else
{
lean_object* x_4653; lean_object* x_4654; lean_object* x_4655; 
lean_dec(x_4640);
lean_dec(x_102);
x_4653 = l_Lean_IR_instInhabitedArg;
x_4654 = lean_unsigned_to_nat(2u);
x_4655 = lean_array_get(x_4653, x_4578, x_4654);
lean_dec(x_4578);
if (lean_obj_tag(x_4655) == 0)
{
lean_object* x_4656; lean_object* x_4657; 
x_4656 = lean_ctor_get(x_4655, 0);
lean_inc(x_4656);
lean_dec(x_4655);
x_4657 = l_Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_4656, x_3, x_4, x_5, x_4585);
return x_4657;
}
else
{
lean_object* x_4658; lean_object* x_4659; 
x_4658 = lean_box(0);
x_4659 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4658, x_3, x_4, x_5, x_4585);
return x_4659;
}
}
}
case 5:
{
lean_object* x_4660; lean_object* x_4661; 
lean_dec(x_4592);
lean_dec(x_4587);
lean_dec(x_4586);
lean_dec(x_4578);
lean_dec(x_4574);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_4660 = l_Lean_IR_ToIR_lowerLet___closed__26;
x_4661 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4660, x_3, x_4, x_5, x_4585);
return x_4661;
}
case 6:
{
lean_object* x_4662; uint8_t x_4663; 
lean_dec(x_4586);
x_4662 = lean_ctor_get(x_4592, 0);
lean_inc(x_4662);
lean_dec(x_4592);
lean_inc(x_102);
x_4663 = l_Lean_isExtern(x_4587, x_102);
if (x_4663 == 0)
{
lean_object* x_4664; 
lean_dec(x_4578);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4664 = l_Lean_IR_ToIR_getCtorInfo(x_102, x_3, x_4, x_5, x_4585);
if (lean_obj_tag(x_4664) == 0)
{
lean_object* x_4665; lean_object* x_4666; lean_object* x_4667; lean_object* x_4668; lean_object* x_4669; lean_object* x_4670; lean_object* x_4671; lean_object* x_4672; lean_object* x_4673; lean_object* x_4674; lean_object* x_4675; lean_object* x_4676; lean_object* x_4677; lean_object* x_4678; lean_object* x_4679; lean_object* x_4680; 
x_4665 = lean_ctor_get(x_4664, 0);
lean_inc(x_4665);
x_4666 = lean_ctor_get(x_4664, 1);
lean_inc(x_4666);
lean_dec(x_4664);
x_4667 = lean_ctor_get(x_4665, 0);
lean_inc(x_4667);
x_4668 = lean_ctor_get(x_4665, 1);
lean_inc(x_4668);
lean_dec(x_4665);
x_4669 = lean_ctor_get(x_4662, 3);
lean_inc(x_4669);
lean_dec(x_4662);
x_4670 = lean_array_get_size(x_4574);
x_4671 = l_Array_extract___rarg(x_4574, x_4669, x_4670);
lean_dec(x_4670);
lean_dec(x_4574);
x_4672 = lean_array_get_size(x_4668);
x_4673 = lean_unsigned_to_nat(0u);
x_4674 = lean_unsigned_to_nat(1u);
x_4675 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4675, 0, x_4673);
lean_ctor_set(x_4675, 1, x_4672);
lean_ctor_set(x_4675, 2, x_4674);
x_4676 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_4677 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9(x_4668, x_4671, x_4675, x_4675, x_4676, x_4673, lean_box(0), lean_box(0), x_3, x_4, x_5, x_4666);
lean_dec(x_4675);
x_4678 = lean_ctor_get(x_4677, 0);
lean_inc(x_4678);
x_4679 = lean_ctor_get(x_4677, 1);
lean_inc(x_4679);
lean_dec(x_4677);
x_4680 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_4667, x_4668, x_4671, x_4678, x_3, x_4, x_5, x_4679);
lean_dec(x_4671);
lean_dec(x_4668);
return x_4680;
}
else
{
lean_object* x_4681; lean_object* x_4682; lean_object* x_4683; lean_object* x_4684; 
lean_dec(x_4662);
lean_dec(x_4574);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4681 = lean_ctor_get(x_4664, 0);
lean_inc(x_4681);
x_4682 = lean_ctor_get(x_4664, 1);
lean_inc(x_4682);
if (lean_is_exclusive(x_4664)) {
 lean_ctor_release(x_4664, 0);
 lean_ctor_release(x_4664, 1);
 x_4683 = x_4664;
} else {
 lean_dec_ref(x_4664);
 x_4683 = lean_box(0);
}
if (lean_is_scalar(x_4683)) {
 x_4684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4684 = x_4683;
}
lean_ctor_set(x_4684, 0, x_4681);
lean_ctor_set(x_4684, 1, x_4682);
return x_4684;
}
}
else
{
lean_object* x_4685; 
lean_dec(x_4662);
lean_dec(x_4574);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4578);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4685 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4578, x_3, x_4, x_5, x_4585);
if (lean_obj_tag(x_4685) == 0)
{
lean_object* x_4686; 
x_4686 = lean_ctor_get(x_4685, 0);
lean_inc(x_4686);
if (lean_obj_tag(x_4686) == 0)
{
lean_object* x_4687; lean_object* x_4688; lean_object* x_4689; 
x_4687 = lean_ctor_get(x_4685, 1);
lean_inc(x_4687);
lean_dec(x_4685);
x_4688 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4688, 0, x_102);
lean_ctor_set(x_4688, 1, x_4578);
x_4689 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4688, x_3, x_4, x_5, x_4687);
return x_4689;
}
else
{
lean_object* x_4690; lean_object* x_4691; lean_object* x_4692; lean_object* x_4693; 
lean_dec(x_4578);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4690 = lean_ctor_get(x_4685, 1);
lean_inc(x_4690);
if (lean_is_exclusive(x_4685)) {
 lean_ctor_release(x_4685, 0);
 lean_ctor_release(x_4685, 1);
 x_4691 = x_4685;
} else {
 lean_dec_ref(x_4685);
 x_4691 = lean_box(0);
}
x_4692 = lean_ctor_get(x_4686, 0);
lean_inc(x_4692);
lean_dec(x_4686);
if (lean_is_scalar(x_4691)) {
 x_4693 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4693 = x_4691;
}
lean_ctor_set(x_4693, 0, x_4692);
lean_ctor_set(x_4693, 1, x_4690);
return x_4693;
}
}
else
{
lean_object* x_4694; lean_object* x_4695; lean_object* x_4696; lean_object* x_4697; 
lean_dec(x_4578);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4694 = lean_ctor_get(x_4685, 0);
lean_inc(x_4694);
x_4695 = lean_ctor_get(x_4685, 1);
lean_inc(x_4695);
if (lean_is_exclusive(x_4685)) {
 lean_ctor_release(x_4685, 0);
 lean_ctor_release(x_4685, 1);
 x_4696 = x_4685;
} else {
 lean_dec_ref(x_4685);
 x_4696 = lean_box(0);
}
if (lean_is_scalar(x_4696)) {
 x_4697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4697 = x_4696;
}
lean_ctor_set(x_4697, 0, x_4694);
lean_ctor_set(x_4697, 1, x_4695);
return x_4697;
}
}
}
case 7:
{
lean_object* x_4698; uint8_t x_4699; lean_object* x_4700; lean_object* x_4701; lean_object* x_4702; lean_object* x_4703; lean_object* x_4704; lean_object* x_4705; lean_object* x_4706; lean_object* x_4707; lean_object* x_4708; 
lean_dec(x_4587);
lean_dec(x_4586);
lean_dec(x_4578);
lean_dec(x_4574);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_4592)) {
 lean_ctor_release(x_4592, 0);
 x_4698 = x_4592;
} else {
 lean_dec_ref(x_4592);
 x_4698 = lean_box(0);
}
x_4699 = 1;
x_4700 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_4701 = l_Lean_Name_toString(x_102, x_4699, x_4700);
if (lean_is_scalar(x_4698)) {
 x_4702 = lean_alloc_ctor(3, 1, 0);
} else {
 x_4702 = x_4698;
 lean_ctor_set_tag(x_4702, 3);
}
lean_ctor_set(x_4702, 0, x_4701);
x_4703 = l_Lean_IR_ToIR_lowerLet___closed__29;
x_4704 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4704, 0, x_4703);
lean_ctor_set(x_4704, 1, x_4702);
x_4705 = l_Lean_IR_ToIR_lowerLet___closed__31;
x_4706 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4706, 0, x_4704);
lean_ctor_set(x_4706, 1, x_4705);
x_4707 = l_Lean_MessageData_ofFormat(x_4706);
x_4708 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_4707, x_3, x_4, x_5, x_4585);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_4708;
}
default: 
{
lean_object* x_4709; 
lean_dec(x_4592);
lean_dec(x_4587);
lean_dec(x_4586);
lean_dec(x_4574);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4578);
lean_inc(x_102);
lean_inc(x_2);
lean_inc(x_1);
x_4709 = l_Lean_IR_ToIR_lowerLet_tryIrDecl_x3f(x_1, x_2, x_102, x_4578, x_3, x_4, x_5, x_4585);
if (lean_obj_tag(x_4709) == 0)
{
lean_object* x_4710; 
x_4710 = lean_ctor_get(x_4709, 0);
lean_inc(x_4710);
if (lean_obj_tag(x_4710) == 0)
{
lean_object* x_4711; lean_object* x_4712; lean_object* x_4713; 
x_4711 = lean_ctor_get(x_4709, 1);
lean_inc(x_4711);
lean_dec(x_4709);
x_4712 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4712, 0, x_102);
lean_ctor_set(x_4712, 1, x_4578);
x_4713 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4712, x_3, x_4, x_5, x_4711);
return x_4713;
}
else
{
lean_object* x_4714; lean_object* x_4715; lean_object* x_4716; lean_object* x_4717; 
lean_dec(x_4578);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4714 = lean_ctor_get(x_4709, 1);
lean_inc(x_4714);
if (lean_is_exclusive(x_4709)) {
 lean_ctor_release(x_4709, 0);
 lean_ctor_release(x_4709, 1);
 x_4715 = x_4709;
} else {
 lean_dec_ref(x_4709);
 x_4715 = lean_box(0);
}
x_4716 = lean_ctor_get(x_4710, 0);
lean_inc(x_4716);
lean_dec(x_4710);
if (lean_is_scalar(x_4715)) {
 x_4717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4717 = x_4715;
}
lean_ctor_set(x_4717, 0, x_4716);
lean_ctor_set(x_4717, 1, x_4714);
return x_4717;
}
}
else
{
lean_object* x_4718; lean_object* x_4719; lean_object* x_4720; lean_object* x_4721; 
lean_dec(x_4578);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4718 = lean_ctor_get(x_4709, 0);
lean_inc(x_4718);
x_4719 = lean_ctor_get(x_4709, 1);
lean_inc(x_4719);
if (lean_is_exclusive(x_4709)) {
 lean_ctor_release(x_4709, 0);
 lean_ctor_release(x_4709, 1);
 x_4720 = x_4709;
} else {
 lean_dec_ref(x_4709);
 x_4720 = lean_box(0);
}
if (lean_is_scalar(x_4720)) {
 x_4721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4721 = x_4720;
}
lean_ctor_set(x_4721, 0, x_4718);
lean_ctor_set(x_4721, 1, x_4719);
return x_4721;
}
}
}
}
}
else
{
lean_object* x_4722; lean_object* x_4723; lean_object* x_4724; lean_object* x_4725; 
lean_dec(x_4578);
lean_dec(x_4574);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4722 = lean_ctor_get(x_4580, 1);
lean_inc(x_4722);
if (lean_is_exclusive(x_4580)) {
 lean_ctor_release(x_4580, 0);
 lean_ctor_release(x_4580, 1);
 x_4723 = x_4580;
} else {
 lean_dec_ref(x_4580);
 x_4723 = lean_box(0);
}
x_4724 = lean_ctor_get(x_4581, 0);
lean_inc(x_4724);
lean_dec(x_4581);
if (lean_is_scalar(x_4723)) {
 x_4725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4725 = x_4723;
}
lean_ctor_set(x_4725, 0, x_4724);
lean_ctor_set(x_4725, 1, x_4722);
return x_4725;
}
}
else
{
lean_object* x_4726; lean_object* x_4727; lean_object* x_4728; lean_object* x_4729; 
lean_dec(x_4578);
lean_dec(x_4574);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4726 = lean_ctor_get(x_4580, 0);
lean_inc(x_4726);
x_4727 = lean_ctor_get(x_4580, 1);
lean_inc(x_4727);
if (lean_is_exclusive(x_4580)) {
 lean_ctor_release(x_4580, 0);
 lean_ctor_release(x_4580, 1);
 x_4728 = x_4580;
} else {
 lean_dec_ref(x_4580);
 x_4728 = lean_box(0);
}
if (lean_is_scalar(x_4728)) {
 x_4729 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4729 = x_4728;
}
lean_ctor_set(x_4729, 0, x_4726);
lean_ctor_set(x_4729, 1, x_4727);
return x_4729;
}
}
else
{
lean_object* x_4730; lean_object* x_4731; lean_object* x_4732; lean_object* x_4733; 
lean_dec(x_4574);
lean_dec(x_102);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4730 = lean_ctor_get(x_4577, 0);
lean_inc(x_4730);
x_4731 = lean_ctor_get(x_4577, 1);
lean_inc(x_4731);
if (lean_is_exclusive(x_4577)) {
 lean_ctor_release(x_4577, 0);
 lean_ctor_release(x_4577, 1);
 x_4732 = x_4577;
} else {
 lean_dec_ref(x_4577);
 x_4732 = lean_box(0);
}
if (lean_is_scalar(x_4732)) {
 x_4733 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4733 = x_4732;
}
lean_ctor_set(x_4733, 0, x_4730);
lean_ctor_set(x_4733, 1, x_4731);
return x_4733;
}
}
}
}
}
default: 
{
lean_object* x_4734; lean_object* x_4735; lean_object* x_4736; lean_object* x_4737; lean_object* x_4738; lean_object* x_4739; uint8_t x_4740; 
x_4734 = lean_ctor_get(x_7, 0);
lean_inc(x_4734);
x_4735 = lean_ctor_get(x_7, 1);
lean_inc(x_4735);
lean_dec(x_7);
x_4736 = lean_st_ref_get(x_3, x_6);
x_4737 = lean_ctor_get(x_4736, 0);
lean_inc(x_4737);
x_4738 = lean_ctor_get(x_4737, 0);
lean_inc(x_4738);
lean_dec(x_4737);
x_4739 = lean_ctor_get(x_4736, 1);
lean_inc(x_4739);
lean_dec(x_4736);
x_4740 = !lean_is_exclusive(x_4738);
if (x_4740 == 0)
{
lean_object* x_4741; lean_object* x_4742; lean_object* x_4743; uint64_t x_4744; uint64_t x_4745; uint64_t x_4746; uint64_t x_4747; uint64_t x_4748; uint64_t x_4749; uint64_t x_4750; size_t x_4751; size_t x_4752; size_t x_4753; size_t x_4754; size_t x_4755; lean_object* x_4756; lean_object* x_4757; 
x_4741 = lean_ctor_get(x_4738, 1);
x_4742 = lean_ctor_get(x_4738, 0);
lean_dec(x_4742);
x_4743 = lean_array_get_size(x_4741);
x_4744 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_4734);
x_4745 = 32;
x_4746 = lean_uint64_shift_right(x_4744, x_4745);
x_4747 = lean_uint64_xor(x_4744, x_4746);
x_4748 = 16;
x_4749 = lean_uint64_shift_right(x_4747, x_4748);
x_4750 = lean_uint64_xor(x_4747, x_4749);
x_4751 = lean_uint64_to_usize(x_4750);
x_4752 = lean_usize_of_nat(x_4743);
lean_dec(x_4743);
x_4753 = 1;
x_4754 = lean_usize_sub(x_4752, x_4753);
x_4755 = lean_usize_land(x_4751, x_4754);
x_4756 = lean_array_uget(x_4741, x_4755);
lean_dec(x_4741);
x_4757 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_4734, x_4756);
lean_dec(x_4756);
lean_dec(x_4734);
if (lean_obj_tag(x_4757) == 0)
{
lean_object* x_4758; lean_object* x_4759; 
lean_free_object(x_4738);
lean_dec(x_4735);
lean_dec(x_2);
lean_dec(x_1);
x_4758 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_4759 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4758, x_3, x_4, x_5, x_4739);
return x_4759;
}
else
{
lean_object* x_4760; 
x_4760 = lean_ctor_get(x_4757, 0);
lean_inc(x_4760);
lean_dec(x_4757);
switch (lean_obj_tag(x_4760)) {
case 0:
{
lean_object* x_4761; size_t x_4762; size_t x_4763; lean_object* x_4764; 
x_4761 = lean_ctor_get(x_4760, 0);
lean_inc(x_4761);
lean_dec(x_4760);
x_4762 = lean_array_size(x_4735);
x_4763 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4764 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_4762, x_4763, x_4735, x_3, x_4, x_5, x_4739);
if (lean_obj_tag(x_4764) == 0)
{
lean_object* x_4765; lean_object* x_4766; lean_object* x_4767; 
x_4765 = lean_ctor_get(x_4764, 0);
lean_inc(x_4765);
x_4766 = lean_ctor_get(x_4764, 1);
lean_inc(x_4766);
lean_dec(x_4764);
lean_ctor_set_tag(x_4738, 8);
lean_ctor_set(x_4738, 1, x_4765);
lean_ctor_set(x_4738, 0, x_4761);
x_4767 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4738, x_3, x_4, x_5, x_4766);
return x_4767;
}
else
{
uint8_t x_4768; 
lean_dec(x_4761);
lean_free_object(x_4738);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4768 = !lean_is_exclusive(x_4764);
if (x_4768 == 0)
{
return x_4764;
}
else
{
lean_object* x_4769; lean_object* x_4770; lean_object* x_4771; 
x_4769 = lean_ctor_get(x_4764, 0);
x_4770 = lean_ctor_get(x_4764, 1);
lean_inc(x_4770);
lean_inc(x_4769);
lean_dec(x_4764);
x_4771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4771, 0, x_4769);
lean_ctor_set(x_4771, 1, x_4770);
return x_4771;
}
}
}
case 1:
{
lean_object* x_4772; lean_object* x_4773; 
lean_dec(x_4760);
lean_free_object(x_4738);
lean_dec(x_4735);
lean_dec(x_2);
lean_dec(x_1);
x_4772 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_4773 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4772, x_3, x_4, x_5, x_4739);
return x_4773;
}
default: 
{
lean_object* x_4774; lean_object* x_4775; 
lean_free_object(x_4738);
lean_dec(x_4735);
x_4774 = lean_box(0);
x_4775 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4774, x_3, x_4, x_5, x_4739);
return x_4775;
}
}
}
}
else
{
lean_object* x_4776; lean_object* x_4777; uint64_t x_4778; uint64_t x_4779; uint64_t x_4780; uint64_t x_4781; uint64_t x_4782; uint64_t x_4783; uint64_t x_4784; size_t x_4785; size_t x_4786; size_t x_4787; size_t x_4788; size_t x_4789; lean_object* x_4790; lean_object* x_4791; 
x_4776 = lean_ctor_get(x_4738, 1);
lean_inc(x_4776);
lean_dec(x_4738);
x_4777 = lean_array_get_size(x_4776);
x_4778 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_4734);
x_4779 = 32;
x_4780 = lean_uint64_shift_right(x_4778, x_4779);
x_4781 = lean_uint64_xor(x_4778, x_4780);
x_4782 = 16;
x_4783 = lean_uint64_shift_right(x_4781, x_4782);
x_4784 = lean_uint64_xor(x_4781, x_4783);
x_4785 = lean_uint64_to_usize(x_4784);
x_4786 = lean_usize_of_nat(x_4777);
lean_dec(x_4777);
x_4787 = 1;
x_4788 = lean_usize_sub(x_4786, x_4787);
x_4789 = lean_usize_land(x_4785, x_4788);
x_4790 = lean_array_uget(x_4776, x_4789);
lean_dec(x_4776);
x_4791 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_4734, x_4790);
lean_dec(x_4790);
lean_dec(x_4734);
if (lean_obj_tag(x_4791) == 0)
{
lean_object* x_4792; lean_object* x_4793; 
lean_dec(x_4735);
lean_dec(x_2);
lean_dec(x_1);
x_4792 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_4793 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4792, x_3, x_4, x_5, x_4739);
return x_4793;
}
else
{
lean_object* x_4794; 
x_4794 = lean_ctor_get(x_4791, 0);
lean_inc(x_4794);
lean_dec(x_4791);
switch (lean_obj_tag(x_4794)) {
case 0:
{
lean_object* x_4795; size_t x_4796; size_t x_4797; lean_object* x_4798; 
x_4795 = lean_ctor_get(x_4794, 0);
lean_inc(x_4795);
lean_dec(x_4794);
x_4796 = lean_array_size(x_4735);
x_4797 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4798 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_4796, x_4797, x_4735, x_3, x_4, x_5, x_4739);
if (lean_obj_tag(x_4798) == 0)
{
lean_object* x_4799; lean_object* x_4800; lean_object* x_4801; lean_object* x_4802; 
x_4799 = lean_ctor_get(x_4798, 0);
lean_inc(x_4799);
x_4800 = lean_ctor_get(x_4798, 1);
lean_inc(x_4800);
lean_dec(x_4798);
x_4801 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_4801, 0, x_4795);
lean_ctor_set(x_4801, 1, x_4799);
x_4802 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_4801, x_3, x_4, x_5, x_4800);
return x_4802;
}
else
{
lean_object* x_4803; lean_object* x_4804; lean_object* x_4805; lean_object* x_4806; 
lean_dec(x_4795);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4803 = lean_ctor_get(x_4798, 0);
lean_inc(x_4803);
x_4804 = lean_ctor_get(x_4798, 1);
lean_inc(x_4804);
if (lean_is_exclusive(x_4798)) {
 lean_ctor_release(x_4798, 0);
 lean_ctor_release(x_4798, 1);
 x_4805 = x_4798;
} else {
 lean_dec_ref(x_4798);
 x_4805 = lean_box(0);
}
if (lean_is_scalar(x_4805)) {
 x_4806 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4806 = x_4805;
}
lean_ctor_set(x_4806, 0, x_4803);
lean_ctor_set(x_4806, 1, x_4804);
return x_4806;
}
}
case 1:
{
lean_object* x_4807; lean_object* x_4808; 
lean_dec(x_4794);
lean_dec(x_4735);
lean_dec(x_2);
lean_dec(x_1);
x_4807 = l_Lean_IR_ToIR_lowerLet___closed__38;
x_4808 = l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1(x_4807, x_3, x_4, x_5, x_4739);
return x_4808;
}
default: 
{
lean_object* x_4809; lean_object* x_4810; 
lean_dec(x_4735);
x_4809 = lean_box(0);
x_4810 = l_Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_4809, x_3, x_4, x_5, x_4739);
return x_4810;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkPartialApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerCode(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_2);
x_14 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_13);
x_16 = lean_box(7);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_5);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
lean_inc(x_2);
x_20 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_18);
x_22 = lean_box(7);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_5);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_IR_ToIR_bindVar(x_9, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_IR_ToIR_newVar(x_5, x_6, x_7, x_12);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(7);
x_17 = l_Lean_IR_ToIR_lowerLet_mkPartialApp___lambda__1(x_2, x_14, x_4, x_11, x_3, x_16, x_5, x_6, x_7, x_15);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(7);
x_21 = l_Lean_IR_ToIR_lowerLet_mkPartialApp___lambda__1(x_2, x_18, x_4, x_11, x_3, x_20, x_5, x_6, x_7, x_19);
return x_21;
}
case 7:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_box(7);
x_25 = l_Lean_IR_ToIR_lowerLet_mkPartialApp___lambda__1(x_2, x_22, x_4, x_11, x_3, x_24, x_5, x_6, x_7, x_23);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_IR_ToIR_lowerType(x_28, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_IR_ToIR_lowerLet_mkPartialApp___lambda__1(x_2, x_26, x_4, x_11, x_3, x_30, x_5, x_6, x_7, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_IR_ToIR_bindErased(x_8, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_ToIR_lowerCode(x_2, x_4, x_5, x_6, x_10);
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
x_9 = l_Lean_IR_ToIR_bindVarToVarId(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_ToIR_lowerCode(x_2, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_11, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_7, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
x_14 = l_Lean_IR_ToIR_lowerCode(x_1, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fget(x_4, x_7);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_8, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_21);
x_23 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1741_(x_16);
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
lean_dec(x_21);
x_36 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ToIR_lowerArg___spec__1(x_16, x_35);
lean_dec(x_35);
lean_dec(x_16);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_7, x_37);
lean_dec(x_7);
x_7 = x_38;
x_11 = x_20;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_IR_instInhabitedCtorFieldInfo;
x_43 = lean_array_get(x_42, x_3, x_7);
switch (lean_obj_tag(x_43)) {
case 2:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_6, x_44);
x_46 = lean_nat_add(x_7, x_44);
lean_dec(x_7);
lean_inc(x_5);
x_47 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_45, x_46, x_8, x_9, x_10, x_20);
lean_dec(x_45);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_nat_add(x_50, x_6);
x_52 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_41);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_nat_add(x_55, x_6);
x_57 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_41);
lean_ctor_set(x_57, 3, x_53);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_41);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 3:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_43, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_43, 2);
lean_inc(x_64);
lean_dec(x_43);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_7, x_65);
lean_dec(x_7);
lean_inc(x_5);
x_67 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_66, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_2, 2);
x_71 = lean_ctor_get(x_2, 3);
x_72 = lean_nat_add(x_70, x_71);
x_73 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_63);
lean_ctor_set(x_73, 3, x_41);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_69);
lean_ctor_set(x_67, 0, x_73);
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_76 = lean_ctor_get(x_2, 2);
x_77 = lean_ctor_get(x_2, 3);
x_78 = lean_nat_add(x_76, x_77);
x_79 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_79, 0, x_5);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_63);
lean_ctor_set(x_79, 3, x_41);
lean_ctor_set(x_79, 4, x_64);
lean_ctor_set(x_79, 5, x_74);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_41);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_67);
if (x_81 == 0)
{
return x_67;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_67, 0);
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_67);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
default: 
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_43);
lean_dec(x_41);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_7, x_85);
lean_dec(x_7);
x_7 = x_86;
x_11 = x_20;
goto _start;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_40);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_7, x_88);
lean_dec(x_7);
x_7 = x_89;
x_11 = x_20;
goto _start;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_15);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_7, x_91);
lean_dec(x_7);
x_7 = x_92;
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
x_9 = l_Lean_Compiler_LCNF_getMonoDecl_x3f(x_3, x_6, x_7, x_8);
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_array_get_size(x_4);
x_21 = lean_ctor_get(x_19, 3);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_nat_dec_lt(x_20, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_20, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_extract___rarg(x_4, x_25, x_22);
x_27 = l_Array_extract___rarg(x_4, x_22, x_20);
lean_dec(x_20);
lean_dec(x_4);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_28, x_27, x_5, x_6, x_7, x_17);
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
lean_dec(x_20);
x_39 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_4);
x_40 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_39, x_5, x_6, x_7, x_17);
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
lean_dec(x_20);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_4);
x_51 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_50, x_5, x_6, x_7, x_17);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
lean_dec(x_10);
x_62 = lean_array_get_size(x_4);
x_63 = lean_ctor_get(x_61, 3);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_array_get_size(x_63);
lean_dec(x_63);
x_65 = lean_nat_dec_lt(x_62, x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = lean_nat_dec_eq(x_62, x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_extract___rarg(x_4, x_67, x_64);
x_69 = l_Array_extract___rarg(x_4, x_64, x_62);
lean_dec(x_62);
lean_dec(x_4);
x_70 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_IR_ToIR_lowerLet_mkPartialApp(x_1, x_2, x_70, x_69, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_64);
lean_dec(x_62);
x_81 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_81, 0, x_3);
lean_ctor_set(x_81, 1, x_4);
x_82 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_81, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_64);
lean_dec(x_62);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_4);
x_93 = l_Lean_IR_ToIR_lowerLet_mkExpr(x_1, x_2, x_92, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_94);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ToIR_lowerCode(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_mkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_ToIR_bindVar(x_8, x_4, x_5, x_6, x_7);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(7);
x_13 = l_Lean_IR_ToIR_lowerLet_mkExpr___lambda__1(x_2, x_10, x_3, x_12, x_4, x_5, x_6, x_11);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(7);
x_17 = l_Lean_IR_ToIR_lowerLet_mkExpr___lambda__1(x_2, x_14, x_3, x_16, x_4, x_5, x_6, x_15);
return x_17;
}
case 7:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_box(7);
x_21 = l_Lean_IR_ToIR_lowerLet_mkExpr___lambda__1(x_2, x_18, x_3, x_20, x_4, x_5, x_6, x_19);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_IR_ToIR_lowerType(x_24, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_IR_ToIR_lowerLet_mkExpr___lambda__1(x_2, x_22, x_3, x_26, x_4, x_5, x_6, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__1(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__2(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__3(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_IR_ToIR_lowerLet___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_IR_ToIR_lowerLet___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ToIR_lowerLet___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerLet___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerResultType.resultTypeForArity", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid arity", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1;
x_2 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
x_3 = lean_unsigned_to_nat(389u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ToIR_lowerType___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
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
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_Lean_IR_ToIR_lowerType___closed__12;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_11 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_14 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_16 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_15);
return x_16;
}
}
case 7:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_2, x_18);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_19;
goto _start;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_22 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_21);
return x_22;
}
}
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
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
x_12 = l_Array_mapMUnsafe_map___at_Lean_IR_ToIR_lowerCode___spec__1(x_10, x_11, x_8, x_2, x_3, x_4, x_5);
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
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_9);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
x_54 = l_List_isEmpty___rarg(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_13);
lean_ctor_set(x_55, 2, x_50);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_9, 0, x_55);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_9);
lean_dec(x_52);
lean_free_object(x_16);
x_56 = lean_ir_mk_dummy_extern_decl(x_6, x_13, x_50);
x_57 = l_Lean_IR_ToIR_addDecl(x_56, x_2, x_3, x_4, x_51);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_64 = lean_ctor_get(x_16, 0);
x_65 = lean_ctor_get(x_16, 1);
x_66 = lean_ctor_get(x_9, 0);
lean_inc(x_66);
lean_dec(x_9);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
x_68 = l_List_isEmpty___rarg(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_6);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_66);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_16, 0, x_70);
return x_16;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_66);
lean_free_object(x_16);
x_71 = lean_ir_mk_dummy_extern_decl(x_6, x_13, x_64);
x_72 = l_Lean_IR_ToIR_addDecl(x_71, x_2, x_3, x_4, x_65);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_77 = lean_ctor_get(x_16, 0);
x_78 = lean_ctor_get(x_16, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_16);
x_79 = lean_ctor_get(x_9, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_80 = x_9;
} else {
 lean_dec_ref(x_9);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = l_List_isEmpty___rarg(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_83, 0, x_6);
lean_ctor_set(x_83, 1, x_13);
lean_ctor_set(x_83, 2, x_77);
lean_ctor_set(x_83, 3, x_79);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_80);
lean_dec(x_79);
x_86 = lean_ir_mk_dummy_extern_decl(x_6, x_13, x_77);
x_87 = l_Lean_IR_ToIR_addDecl(x_86, x_2, x_3, x_4, x_78);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_IR_toIR___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl), 5, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_IR_ToIR_M_run___rarg(x_13, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_5, x_17);
x_5 = x_18;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_array_push(x_6, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_9 = x_20;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l_Lean_IR_ToIR_lowerLet___closed__27;
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_IR_toIR___spec__1(x_1, x_5, x_1, x_6, x_7, x_8, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_IR_toIR___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_IR_toIR___spec__1(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
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
l_Lean_IR_ToIR_M_run___rarg___closed__1 = _init_l_Lean_IR_ToIR_M_run___rarg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___rarg___closed__1);
l_Lean_IR_ToIR_M_run___rarg___closed__2 = _init_l_Lean_IR_ToIR_M_run___rarg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___rarg___closed__2);
l_Lean_IR_ToIR_M_run___rarg___closed__3 = _init_l_Lean_IR_ToIR_M_run___rarg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___rarg___closed__3);
l_Lean_IR_ToIR_M_run___rarg___closed__4 = _init_l_Lean_IR_ToIR_M_run___rarg___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___rarg___closed__4);
l_Lean_IR_ToIR_addDecl___closed__1 = _init_l_Lean_IR_ToIR_addDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___closed__1);
l_Lean_IR_ToIR_addDecl___closed__2 = _init_l_Lean_IR_ToIR_addDecl___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___closed__2);
l_Lean_IR_ToIR_addDecl___closed__3 = _init_l_Lean_IR_ToIR_addDecl___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___closed__3);
l_Lean_IR_ToIR_addDecl___closed__4 = _init_l_Lean_IR_ToIR_addDecl___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___closed__4);
l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1 = _init_l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__1);
l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__2 = _init_l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__1___closed__2);
l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__1);
l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__2);
l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__3);
l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__4);
l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__5 = _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__5);
l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__6 = _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__6);
l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__7 = _init_l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__7();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_IR_ToIR_lowerEnumToScalarType___spec__2___closed__7);
l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__1 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__1);
l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__2 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__2);
l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__3 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType___lambda__1___closed__3);
l_Lean_IR_ToIR_lowerEnumToScalarType___closed__1 = _init_l_Lean_IR_ToIR_lowerEnumToScalarType___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerEnumToScalarType___closed__1);
l_panic___at_Lean_IR_ToIR_lowerType___spec__1___closed__1 = _init_l_panic___at_Lean_IR_ToIR_lowerType___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_lowerType___spec__1___closed__1);
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
l_Lean_IR_ToIR_lowerType___closed__12 = _init_l_Lean_IR_ToIR_lowerType___closed__12();
lean_mark_persistent(l_Lean_IR_ToIR_lowerType___closed__12);
l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__1 = _init_l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__1);
l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__2 = _init_l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__2);
l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__3 = _init_l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_getCtorInfo___spec__1___closed__3);
l_Lean_IR_ToIR_getCtorInfo___closed__1 = _init_l_Lean_IR_ToIR_getCtorInfo___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_getCtorInfo___closed__1);
l_Lean_IR_ToIR_getCtorInfo___closed__2 = _init_l_Lean_IR_ToIR_getCtorInfo___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_getCtorInfo___closed__2);
l_Lean_IR_ToIR_getCtorInfo___closed__3 = _init_l_Lean_IR_ToIR_getCtorInfo___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_getCtorInfo___closed__3);
l_panic___at_Lean_IR_ToIR_lowerArg___spec__2___closed__1 = _init_l_panic___at_Lean_IR_ToIR_lowerArg___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_lowerArg___spec__2___closed__1);
l_Lean_IR_ToIR_lowerArg___closed__1 = _init_l_Lean_IR_ToIR_lowerArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__1);
l_Lean_IR_ToIR_lowerArg___closed__2 = _init_l_Lean_IR_ToIR_lowerArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__2);
l_Lean_IR_ToIR_lowerArg___closed__3 = _init_l_Lean_IR_ToIR_lowerArg___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerArg___closed__3);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__1);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__2);
l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj___closed__3);
l_Lean_IR_ToIR_instInhabitedTranslatedProj = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj);
l_Lean_IR_ToIR_lowerProj___closed__1 = _init_l_Lean_IR_ToIR_lowerProj___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerProj___closed__1);
l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1___closed__1 = _init_l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_IR_ToIR_lowerAlt_loop___spec__1___closed__1);
l_Lean_IR_ToIR_lowerAlt_loop___closed__1 = _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerAlt_loop___closed__1);
l_Lean_IR_ToIR_lowerAlt_loop___closed__2 = _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerAlt_loop___closed__2);
l_Lean_IR_ToIR_lowerAlt_loop___closed__3 = _init_l_Lean_IR_ToIR_lowerAlt_loop___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerAlt_loop___closed__3);
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
l_Lean_IR_ToIR_lowerCode___closed__6 = _init_l_Lean_IR_ToIR_lowerCode___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__6);
l_Lean_IR_ToIR_lowerCode___closed__7 = _init_l_Lean_IR_ToIR_lowerCode___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__7);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
